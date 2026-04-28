theory Timely_Infrastructure

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.BNA_Operators
  Progress_Tracking.Propagate
  Nondeterministic_Dataflow.Eval
  "HOL-Library.While_Combinator"
  "../propagation_extras/Executable"
  "../propagation_extras/Termination"
  Zero_Cyc_Check
  Locations
  Operators_Utils
  DataplaneUtils
  Containers.Collection_Order
  AntichainOrder
  MyProduct_Instances
begin 

context includes cset.lifting begin
lift_definition cthe_elem :: "'m cset \<Rightarrow> 'm" is Set.the_elem .
lift_definition csome_elem :: "'m cset \<Rightarrow> 'm" is some_elem .
lift_definition ccard :: "'m cset \<Rightarrow> nat" is card .
lift_definition cinfinite :: "'m cset \<Rightarrow> bool" is Finite_Set.infinite.
end


lemma ccard_eq_0_iff[simp]:
  "(ccard A = 0) = (A = {||} \<or> cinfinite A)"
  unfolding ccard_def cinfinite_def
  by fastforce


lemma cset_of_llist_llist_of_append[simp]:
  "cset_of_llist (llist_of (xs @ ys)) = cUn (cset_of_llist (llist_of xs)) (cset_of_llist (llist_of ys))"
  unfolding cset_of_llist_def
  apply (clarsimp simp flip: cin.rep_eq)
  apply (subst sup_cset.abs_eq)
    apply (simp_all add: countable_finite eq_onp_same_args)
  done

lemma in_cset_of_llist_llist_of[simp]:
  "x |\<in>| cset_of_llist (llist_of xs) \<longleftrightarrow> x \<in> set xs"
  using cin_code by force

lemma csubset_eq_cset_of_llist:
  "csubset_eq (cset_of_llist lxs) S \<longleftrightarrow> (\<forall> x \<in> lset lxs. x |\<in>| S)"
  using cin_code by fastforce


declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

(* FIXME: move me *)
fun rmdups where
  "rmdups S [] = []"
| "rmdups S (x # xs) = (if x \<in> S then rmdups S xs else x # (rmdups (insert x S) xs))"

lemma set_rmdups[simp]:
  "set (rmdups S xs) = set xs - S"
  by (induct xs arbitrary: S) auto

lemma rmdups_rmdups[simp]:
  "rmdups S1 (rmdups S2 xs) = rmdups (S1 \<union> S2) xs"
  by (induct xs arbitrary: S1 S2) (auto simp add: insert_absorb)

lemma rmdups_append[simp]:
  "rmdups S (xs @ ys) = rmdups S xs @ rmdups (S \<union> set xs) ys"
  by (induct xs arbitrary: S ys) (auto simp add: insert_absorb)

lemma rmdups_cong:
  "A \<inter> set xs = B \<inter> set xs \<Longrightarrow>
   rmdups A xs = rmdups B xs"
  apply (induct xs arbitrary: A B)
   apply simp
  apply (smt (verit, best) Diff_Diff_Int Diff_iff Int_insert_left_if1 insert_absorb inter_eq_subsetI list.inject list.set(2) list.set_intros(1) rmdups.simps(2) set_subset_Cons)
  done

lemma rmdups_NilI:
  "(set xs \<subseteq> A \<and> xs \<noteq> []) \<or> xs = [] \<Longrightarrow>
   rmdups A xs = []"
  apply (induct xs arbitrary: A)
   apply simp_all
  done

lemma rmdups_insert_NilI:
  "(set xs = {a} \<and> xs \<noteq> []) \<or> xs = [] \<Longrightarrow>
   rmdups (insert a A) xs = []"
  apply (induct xs arbitrary: A)
   apply auto
  done

definition "DEBUG = False"

definition "trace = (if DEBUG then Debug.tracing else (\<lambda> x y. y))"


lemma trace_simp[simp]:
  "trace x r = r"
  by (auto simp add: trace_def)

(* Inspired by timely/src/progress/change_batch.rs:12 *)
type_synonym 'a change_batch = "'a list"

(* Inspired by timely/src/progress/subgraph.rs:237 *)
record ('id, 'p, 't) subgraph =
  pt_tr :: "(('id, 'p) location, 't) configuration"
  nxt :: "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option"
  summ :: "('id, 'p) location \<Rightarrow> ('id, 'p) location \<Rightarrow> 't antichain"
  upfro :: "'id \<Rightarrow> bool"

datatype ('id, 'p, 's, 'd, 't) dataflow_tree = 
  "apply": Logic "('p option, 'p option, 's + 'd) op" "'p \<Rightarrow> 'p \<Rightarrow> 't list"
  | Comp "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option" "('id, 'p, 's, 'd, 't) dataflow_tree" "('id, 'p, 's, 'd, 't) dataflow_tree"

fun dataflow_tree_to_operator_aux where
  "dataflow_tree_to_operator_aux n chns (Logic op su) = (

    n + 1,
    map_op (case_option (Inl n) (\<lambda> p. Inr (n, p))) (case_option (Inl n) (\<lambda> p. Inr (n, p))) op)"
| "dataflow_tree_to_operator_aux n chns (Comp wire dt1 dt2) = (
    let (n', op1) = dataflow_tree_to_operator_aux n chns dt1 in
    let (n'', op2) = dataflow_tree_to_operator_aux n' chns dt2 in
    (n'', map_op (case_sum id id) (case_sum id id)
     (comp_op 
      (case_sum (\<lambda> _. None) ((case_option None (Some o Inr)) o (\<lambda> (nid, p). case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n' + offset, q))))
      ((\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (d, t)) (chns x)))
       op1 op2))
   )"
definition "dataflow_tree_to_operator chns df = snd (dataflow_tree_to_operator_aux 0 chns df)"

(* Recursive function that builds the graph for the progration algorithm *)
fun dataflow_tree_to_graph_aux where
  "dataflow_tree_to_graph_aux n (Logic op su) = 
    (n+ 1, \<lambda> l1 l2. if n = node l1 \<and> n = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) then su (idp (port l1)) (idp (port l2)) else [])"
| "dataflow_tree_to_graph_aux n (Comp wire dt1 dt2) = (
    let (n', summary1) = dataflow_tree_to_graph_aux n dt1 in
    let (n'', summary2) = dataflow_tree_to_graph_aux n' dt2 in
        (n'', \<lambda> l1 l2. 
         if node l1 \<ge> n \<and> node l1 < n' \<and> node l2 \<ge> n \<and> node l2 < n' then summary1 l1 l2
         else
           (if node l1 \<ge> n' \<and> node l2 \<ge> n' then summary2 l1 l2
            else
            (if node l1 \<ge> n \<and> node l1 < n' \<and> node l2 \<ge> n' \<and> is_Src (port l1) \<and> is_Trg (port l2)
                   then (case wire (node l1 - n, idp (port l1)) of 
                           None \<Rightarrow> []
                         | Some (offset, q) \<Rightarrow> (if node l2 = n' + offset \<and> q = idp (port l2) then [0] else [])) 
                   else []))
         )
   )"

fun nodes_count where
  "nodes_count (Logic op su) = 1"
| "nodes_count (Comp wire dt1 dt2) = nodes_count dt1 + nodes_count dt2"

fun op_conn where
  "op_conn su (nid, p) (nid', p') = (su (Loc nid (Src p)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A)"

(* Builds the graph for the progration algorithm *)
definition "dataflow_tree_to_graph (df :: ('id :: {minus,one,plus,zero,ord,enum,hashable}, _, _, _, _) dataflow_tree) = (
  let (_, raw_s) = dataflow_tree_to_graph_aux 0 df in
  let s = antichain_from_list oo raw_s in
  let ints = (\<lambda> n p1 p2. raw_s (Loc n (Trg p1)) (Loc n (Src p2))) in
  if \<not> has_zero_cyc s \<and>
     no_self_loop_checker s \<and>
     implementation_graph_checker (weights_to_graph_fun (remove_non_zero_weights s)) \<and>
     CARD ('id) = nodes_count df \<and>
     (\<forall> l1 l2. incomparable (set (raw_s l1 l2))) \<and>
     (\<forall> nid p1 p2. distinct (ints nid p1 p2)) \<and>
     bi_unique (op_conn s)
  then raw_s
  else Code.abort (STR ''Control plane could not be build'') (\<lambda> _. ((\<lambda> _ _. []))))"

lemma compile_dataflow_tree_aux_same_loc:
  "(n'', intsum) = dataflow_tree_to_graph_aux n df \<Longrightarrow>
   intsum loc loc = []"
  apply (induct df arbitrary: n n'' intsum)
  subgoal for x1 x2 n n'' intsum
    by (cases loc; simp add: antichain_from_list_is_empty split: port.splits if_splits)
  subgoal for x1 df1 df2 n n'' intsum
    apply (clarsimp simp add: port.case_eq_if split: list.splits if_splits option.splits prod.splits; hypsubst_thin?)
    apply (metis list.simps(2))
    done
  done

lemma enum_dataflow_topology_compile_dataflow[simp]:
  "enum_dataflow_topology (antichain_from_list oo (dataflow_tree_to_graph (df :: (_, _, _, _, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) dataflow_tree))) (+)"
  apply standard
       apply (simp_all add: add_mono_thms_linordered_semiring(1) Groups.add_ac(1))
  subgoal
    unfolding dataflow_tree_to_graph_def Let_def
    apply (cases "dataflow_tree_to_graph_aux 0 df"; simp)
    using compile_dataflow_tree_aux_same_loc 
    apply (metis (no_types, lifting) antichain_from_list_is_empty filter.simps(1))
    done
  subgoal
    unfolding dataflow_tree_to_graph_def Let_def
    apply (cases "dataflow_tree_to_graph_aux 0 df")
    apply (simp add: no_self_loop_checker_is_graph_checker split: if_splits)
    subgoal
      apply (rule decide_graph_construction[where t=0, simplified, rotated])
          apply assumption+
      apply simp_all
      done
    subgoal
      apply (rule empty_graph_no_zero_cyc)
         apply assumption+
        apply simp_all
       apply (simp_all add: antichain_from_list.abs_eq empty_antichain.abs_eq comp_def add_mono_thms_linordered_semiring(1))
      apply standard
       apply (simp_all add: antichain_from_list.abs_eq empty_antichain.abs_eq comp_def add_mono_thms_linordered_semiring(1))
      done
    done
  done

lemma is_empty_antichain_plus[simp]:
  "is_empty_antichain B \<Longrightarrow>
   antichain A + B = antichain A"
  by (metis Set.is_empty_iff antichain_add_commute antichain_sum_empty_2 empty_antichain.abs_eq is_empty_antichain.rep_eq set_antichain_inverse)
lemma is_empty_antichain_plus'[simp]:
  "is_empty_antichain A \<Longrightarrow>
   A + antichain B = antichain B"
  by (metis Set.is_empty_iff antichain_sum_empty_2 empty_antichain.abs_eq is_empty_antichain.rep_eq set_antichain_inverse)
lemma antichain_sum_eq[simp]:
  "finite A \<Longrightarrow> incomparable A \<Longrightarrow>
   antichain A + antichain A = antichain A"
  apply (subst plus_antichain.abs_eq)
  apply (clarsimp simp add:  eq_onp_def)+
  apply (metis (no_types, lifting) basic_trans_rules(20) in_minimal_antichain incomparable_def order_antisym_conv subsetI)
  done
lemma incomparable_singleton[simp]:
  "incomparable {a}"
  unfolding incomparable_def by auto

lemma dataflow_tree_to_graph_aux_Src_Trg_zero:
  "dataflow_tree_to_graph_aux n dt = (m, su) \<Longrightarrow>
   (su (Loc nid (Src p)) (Loc nid' (Trg p'))) \<noteq> [] \<Longrightarrow>
   x \<in> set (su (Loc nid (Src p)) (Loc nid' (Trg p'))) \<Longrightarrow>
   x = 0"
  apply (induct dt arbitrary: n m su)
   apply (clarsimp simp add:  antichain_from_list_singleton split: list.splits prod.splits if_splits option.splits)
  apply simp
  apply (fastforce simp add: if_distrib  antichain_from_list_singleton split: prod.splits if_splits option.splits)
  done

lemma antichain_from_list_empty[simp]:
  "antichain_from_list [] \<noteq> antichain {a}"
  by (metis antichain_from_list_singleton is_empty_antichain_empty_list is_empty_antichain_not_empty_list)

lemma antichain_from_list_all_eq:
  "(\<forall> x \<in> set xs. x = a) \<Longrightarrow>
   xs \<noteq> [] \<Longrightarrow>
   antichain_from_list xs = antichain {a}"
  apply (induct xs)
   apply auto
  unfolding antichain_from_list_def
  apply auto
  apply (smt (verit, best) Collect_cong insert_compr mem_Collect_eq set_diff_eq singleton_iff)
  done

lemma dataflow_tree_to_graph_Src_Trg_zero[simp]:
  "antichain_from_list oo dataflow_tree_to_graph dt = su \<Longrightarrow>
   \<not> is_empty_antichain (su (Loc nid (Src p)) (Loc nid' (Trg p'))) \<Longrightarrow>
   su (Loc nid (Src p)) (Loc nid' (Trg p')) = antichain {0}"
  unfolding dataflow_tree_to_graph_def Let_def
  apply (simp add: comp_def split: prod.splits if_splits)
  subgoal for _ rs
    apply (subgoal_tac "\<forall> x \<in> set (rs (Loc nid (Src p)) (Loc nid' (Trg p'))). x = 0")
    subgoal
      using antichain_from_list_all_eq by fastforce
    subgoal
      unfolding comp_def
      using dataflow_tree_to_graph_aux_Src_Trg_zero
      by (metis in_set_simps(3))
    done
  subgoal
    by auto
  done

lemma in_antichain_from_list[intro]:
  "\<forall>t'\<in>set xs. \<not> t' < t \<and> \<not> t < t' \<Longrightarrow>
   t \<in> set xs \<Longrightarrow>
   t \<in>\<^sub>A antichain_from_list xs"
  apply (induct xs)
  unfolding antichain_from_list_def
   apply clarsimp+
    apply (subst member_antichain.abs_eq)
    apply (auto simp add: eq_onp_def incomparable_def)
  done
lemma in_antichain_from_list_alt[intro]:
  "incomparable (set xs) \<Longrightarrow>
   t \<in> set xs \<Longrightarrow>
   t \<in>\<^sub>A antichain_from_list xs"
  apply (induct xs)
  unfolding antichain_from_list_def
   apply clarsimp+
    apply (subst member_antichain.abs_eq)
    apply (auto simp add: eq_onp_def incomparable_def)
  done

lemma aux:
  "t \<in>\<^sub>A antichain (minimal_antichain A) \<Longrightarrow>
   finite A \<Longrightarrow>
   (\<forall> t' \<in> A. \<not> t' < t)"
  unfolding member_antichain_def
  apply (auto simp add: minimal_antichain_def)
   apply (subst (asm)  antichain.antichain_inverse)
     apply (auto simp add: incomparable_def)
  done

lemma dataflow_tree_to_graph_aux_no_inp_and_out_connection:
  "dataflow_tree_to_graph_aux n dt = (m, su) \<Longrightarrow>
   su (Loc nid (Trg p)) (Loc nid (Trg p')) = [] \<and> su (Loc nid (Src p)) (Loc nid (Src p')) = []"
  apply (induct dt arbitrary: n m su)
   apply (auto simp add: if_distrib split: if_splits prod.splits list.splits option.splits)
  done

lemma dataflow_tree_to_graph_aux_no_inp_to_other_operator_connection:
  "dataflow_tree_to_graph_aux n dt = (m, su) \<Longrightarrow>
   nid \<noteq> nid' \<Longrightarrow>
   su (Loc nid (Trg p)) (Loc nid' lp) = []"
  apply (induct dt arbitrary: n m su)
   apply (auto simp add: if_distrib split: if_splits prod.splits list.splits option.splits)
  done


lemma dataflow_tree_to_graph_aux_no_out_to_inp_connection:
  "dataflow_tree_to_graph_aux n dt = (m, su) \<Longrightarrow>
   su (Loc nid (Src p)) (Loc nid' (Src p')) = []"
  apply (induct dt arbitrary: n m su)
   apply (auto simp add: if_distrib split: if_splits prod.splits list.splits option.splits)
  done



(* lemma dataflow_tree_to_graph_aux_incomparable_distinct:
  "dataflow_tree_to_graph_aux n dt = (m, su) \<Longrightarrow>
   incomparable (set (su l1 l2)) \<and> distinct (su l1 l2)"
  apply (induct dt arbitrary: n m su)
  subgoal for x1 x2 n m su
    by (auto simp add: incomparable_def split: if_splits; hypsubst_thin?)
  subgoal for x1 dt1 dt2 n m su
    apply (cases l1; cases l2; simp)
    subgoal for nid1 lp1 nid2 lp2
      apply (cases lp1; cases lp2; simp; hypsubst_thin)
         apply (fastforce simp add: incomparable_def  split: list.splits if_splits option.splits prod.splits; hypsubst_thin?)
      apply (fastforce simp add: incomparable_def  split: list.splits if_splits option.splits prod.splits; hypsubst_thin?)
      subgoal
        apply (clarsimp simp add: if_distrib  split: list.split if_splits option.splits prod.splits; hypsubst_thin?)
        apply (safe ;  (fastforce simp add: incomparable_def)?)
        done
      subgoal
        apply (clarsimp simp add:  split: list.split if_splits option.splits prod.splits; hypsubst_thin?)
        done
      done
    done
  done *)

lemma foldr_plus:
  "foldr (+) (map (\<lambda>(s, l, t). l) xs) ((a :: _ :: {monoid_add,ab_semigroup_add,order}) + b) = foldr (+) (map (\<lambda>(s, l, t). l) xs) b + a"
  by (induct xs arbitrary: a b)
   (auto simp add: Groups.add_ac)

lemma  summary_in_path_weight:
  assumes G: "Graph.graph (antichain_from_list oo su)"
  shows 
    "t \<in> set (su l1 l2) \<Longrightarrow>
   (\<forall> l1 l2. incomparable (set (su l1 l2))) \<Longrightarrow>
   \<exists>t' \<le> t. (t' :: _ :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) l1 l2"
  apply (subst Graph.graph.path_weight_def)
  subgoal
    using G[unfolded comp_def] by auto
  subgoal
    apply simp
    apply (subst member_antichain.abs_eq)
     apply (clarsimp simp add: eq_onp_def)
     apply (rule graph.finite_minimal_antichain_path_weightp)
    using G[unfolded comp_def] apply assumption
    unfolding minimal_antichain_def Graph.graph.path_weightp_def[OF G, unfolded comp_def]
    apply clarsimp
    apply (subgoal_tac "graph.path (\<lambda>xa xaa. antichain_from_list (su xa xaa)) l1 l2 [(l1, t, l2)]")
    subgoal
      by (smt (verit) \<open>t \<in> set (su l1 l2) \<Longrightarrow> \<forall>l1 l2. incomparable (set (su l1 l2)) \<Longrightarrow> Graph.graph (\<lambda>x xa. antichain_from_list (su x xa))\<close> add_le_cancel_left graph.path.simps
          graph.path_path_weight graph.path_weight_conv_path graph.sum_path_weights_append_singleton graph.sum_weights_append list_e_eq_lel(1) map_append
          not_Cons_self)
    subgoal
      apply (rule graph.path.intros(2)[where xs=Nil, simplified])
      using G[unfolded comp_def] apply assumption
       apply (rule graph.path.intros(1))
      using G[unfolded comp_def] apply assumption
       apply simp_all
      apply (rule in_antichain_from_list)
      unfolding incomparable_def apply fastforce
      apply assumption
      done
    done
  done

global_interpretation dataflow_topology_from_tree: enum_dataflow_topology "antichain_from_list oo (dataflow_tree_to_graph (df :: (_, _, _, _, 't :: {bot,ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}) dataflow_tree))" "(+)"
  for df
  defines take_step' = "enum_dataflow_topology.take_step (antichain_from_list oo (dataflow_tree_to_graph df)) (+)"
    and after_summary = "dataflow_topology.after_summary (+) :: 't zmultiset \<Rightarrow> 't antichain \<Rightarrow> 't zmultiset"
  by simp

notation dataflow_topology_from_tree.followed_by (infixl \<open>-+-\<close> 65)
notation dataflow_topology_from_tree.after_summary (infixl \<open>+++\<close> 65)

lemma in_empty_graph_False:
  "(s :: _ :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A graph.path_weight (\<lambda>x xa. {}\<^sub>A) l1 l2 \<Longrightarrow>
    l1 \<noteq> l2 \<Longrightarrow> False"
  apply(subgoal_tac "Graph.graph (\<lambda>x xa. {}\<^sub>A)")
   apply (subst (asm) Graph.graph.path_weight_def)
  apply assumption
  subgoal
  apply clarsimp
  subgoal premises prems
    using prems(1) apply -
    unfolding Graph.graph.path_weightp_def[OF prems(3), unfolded comp_def]
    apply (subst (asm) in_antichain_minimal_antichain)
    subgoal
      apply (rule rev_finite_subset[where B="{}"])
       apply auto
       apply (erule graph.path.cases[OF prems(3)])
      using prems(2) mem_antichain_nonempty apply auto
      done
    subgoal
      unfolding minimal_antichain_def
      apply clarsimp
      apply (erule graph.path.cases[OF prems(3)])
      using prems(2) mem_antichain_nonempty apply auto
      done
    done
  done
  subgoal
    apply standard
    using dataflow_topology_from_tree.plus_mono apply auto
    done
  done

lemma path_ConsE:
  assumes G: "Graph.graph weights"
  shows "graph.path weights l1 l3 ((l2, s, l2') # xs) \<Longrightarrow> (l1 = l2 \<Longrightarrow> graph.path weights l2' l3 xs \<Longrightarrow> s \<in>\<^sub>A weights l2 l2' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct l1 l3 "((l2, s, l2') # xs)" arbitrary: xs rule: graph.path.induct[OF G, consumes 1])
    (auto simp: append_eq_Cons_conv elim!: graph.path0E[OF G] intro: graph.path.intros[OF G])

lemma mem_antichain_nonempty_alt[simp]: "s \<notin>\<^sub>A {}\<^sub>A"
  using mem_antichain_nonempty by auto

lemma path_ConsI[intro]:
  assumes G: "Graph.graph weights"
 shows "graph.path weights l2 l3 xs \<Longrightarrow> lbl \<in>\<^sub>A weights l1 l2 \<Longrightarrow> graph.path weights l1 l3 ((l1, lbl, l2) # xs)"
  apply (induct l2 l3 xs arbitrary: rule: graph.path.induct[OF G, consumes 1])
  subgoal for l1 l2
    apply hypsubst_thin
    apply (rule graph.path.intros(2)[OF G, where xs=Nil, simplified])
     apply (rule graph.path.intros(1)[OF G])
    apply simp_all
    done
  subgoal for l1a l2 xs lbla l3
    by (auto simp flip: append.simps intro: graph.path.intros[OF G])
  done

lemma path_weight_Trg_decompose:
  assumes G: "Graph.graph su"
  shows "s \<in>\<^sub>A graph.path_weight su (Loc nid (Trg p)) l \<Longrightarrow>
   l \<noteq> Loc nid (Trg p) \<Longrightarrow>
   (\<forall> nid1 nid2 p2 p1 . su (Loc nid1 (Trg p1)) (Loc nid2 (Trg p2)) = {}\<^sub>A) \<Longrightarrow>
   (\<forall> nid1 nid2 p2 p1 . nid1 \<noteq> nid2 \<longrightarrow> su (Loc nid1 (Trg p1)) (Loc nid2 (Src p2)) = {}\<^sub>A) \<Longrightarrow>
    \<exists>t p'.
       t \<in>\<^sub>A (su (Loc nid (Trg p)) (Loc nid (Src p'))) \<and>
       (\<exists>s'. s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p')) l \<and> s = t -+- s')"
  apply (drule graph.path_weight_conv_path[OF G])
  apply clarsimp
  subgoal for xs
    apply (rotate_tac 3)
    apply (cases xs; hypsubst_thin?)
    subgoal 
      apply (erule graph.path.cases[OF G])
       apply auto
      done
    subgoal for a xs
      apply (cases a; simp; hypsubst_thin)
      subgoal for l1 t' l2
        apply (erule path_ConsE[OF G])
        apply simp_all
        apply hypsubst_thin
        apply (cases l2; simp)
        subgoal for nid2 lp2
          apply (cases lp2; simp; hypsubst_thin)
          subgoal for p2
            apply (cases "nid = nid2")
            subgoal
              apply simp
              apply hypsubst_thin
              apply (rule exI[of _ t'])
              apply (rule exI[of _ p2])
              apply simp
              apply (subst graph.path_weight_def[OF G])
              apply simp
              apply (subst member_antichain.abs_eq)
               apply (simp add: eq_onp_def)
               apply (rule  Graph.graph.finite_minimal_antichain_path_weightp[OF G])
              unfolding minimal_antichain_def
              apply clarsimp
              apply (intro conjI)
               apply (subst graph.path_weightp_def[OF G])
               apply auto[1]
              apply safe
              subgoal for t''
                apply (subst (asm) graph.path_weightp_def[OF G])
                apply clarsimp
                subgoal for ys
                  apply (drule spec[of _ "(Loc nid2 (Trg p), t', Loc nid2 (Src p2)) # ys"])
                  apply (drule mp)
                   apply (rule path_ConsI[OF G])
                    apply assumption+
                  apply auto
                  done
                done
              done
            subgoal
              by auto
            done
          done
        done
      done
    done
  done


lemma graph_path_weight_Trg_Src:
  assumes G: " Graph.graph (\<lambda>x xa. antichain_from_list (su x xa))"
  shows "s \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) (Loc nid (Trg p)) l \<Longrightarrow>
   l \<noteq> Loc nid (Trg p) \<Longrightarrow>
   (m, su) = dataflow_tree_to_graph_aux n dt \<Longrightarrow>
    \<exists>t p'.
       t \<in> set (su (Loc nid (Trg p)) (Loc nid (Src p'))) \<and>
       (\<exists>s'. s' \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) (Loc nid (Src p')) l \<and> s = t -+- s') "
  apply (drule path_weight_Trg_decompose[OF G])
     apply simp_all
  apply (metis antichain_from_list_empty_antichain dataflow_tree_to_graph_aux_no_inp_and_out_connection
      dataflow_tree_to_graph_aux_no_inp_to_other_operator_connection) 
  apply (metis antichain_from_list_empty_antichain
      dataflow_tree_to_graph_aux_no_inp_to_other_operator_connection) 
  apply clarsimp
  using in_antichain_from_listD apply blast
  done


lemma dataflow_tree_to_graph_Trg_decompose:
  "(s :: _ :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) (Loc nid (Trg p)) l \<Longrightarrow>
   l \<noteq> Loc (nid :: _ :: {enum,minus,one,plus,zero,hashable,linorder}) (Trg (p :: _ :: {enum,hashable,linorder})) \<Longrightarrow>
   su = dataflow_tree_to_graph dt \<Longrightarrow>
    \<exists>t p'.
       t \<in> set (su (Loc nid (Trg p)) (Loc nid (Src p'))) \<and>
       (\<exists>s'. s' \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) (Loc nid (Src p')) l \<and> s = t -+- s') "
  unfolding dataflow_tree_to_graph_def Let_def
  apply (cases "dataflow_tree_to_graph_aux 0 dt"; simp only: prod.case simp_thms split: if_splits)
  subgoal for n su'
  apply (rule graph_path_weight_Trg_Src)
       apply (rule dataflow_topology.axioms(1)[of _ "(+)"]; hypsubst_thin?)
    using dataflow_topology_from_tree.dataflow_topology_axioms[unfolded comp_def, of dt, simplified] 
       apply (simp add: dataflow_tree_to_graph_def)
      apply assumption+
    apply (erule sym)
    done
  subgoal 
    by (auto dest: in_empty_graph_False split: prod.splits)
  done



abbreviation AF where
  "AF \<equiv> dataflow_topology.after_summary (-+-)"

notation "AF" (infixl \<open>-++-\<close> 65)

abbreviation "ifrontier \<equiv> dataflow_topology.implied_frontier_alt"

lemma AF_empty[simp]:
  "A -++- {}\<^sub>A = {#}\<^sub>z"
  by (metis after_summary_def dataflow_topology_from_tree.after_summary_empty_summary)

lemma AP_simp[simp]:
  "M -++- S = (\<Sum>s \<in> set_antichain S. image_zmset (\<lambda>t. t -+- s) M)"
  by (metis after_summary_def dataflow_topology_from_tree.after_summary_def)



definition take_step_locale where
  "take_step_locale df = take_step' df cless"

fun take_step where
  "take_step summary (CM loc t delta) c =
  (let c_pointstamps_old = c_pts c loc; c_pointstamps_new = (c_pts c)(loc := update_zmultiset (c_pts c loc) t delta)
   in c\<lparr>c_pts := c_pointstamps_new, c_work := (c_work c)(loc := c_work c loc + frontier_change_code c_pointstamps_old (c_pointstamps_new loc))\<rparr>)"
| "take_step summary PR c =
   (let (t, loc) = mymin_code (t_loc_pairs c); c_implications_old = c_imp c loc; c_implications_new = (c_imp c)(loc := c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#});
    c_worklist_removed_loc = map_entry loc (filter_zmset (\<lambda>t'. t' \<noteq> t)) (c_work c)
    in c\<lparr>c_work := \<lambda>loc'. c_worklist_removed_loc loc' + after_summary (frontier_change_code c_implications_old (c_implications_new loc)) (summary loc loc'),
        c_imp := c_implications_new\<rparr>)"

definition "propagate_all_locale summary df c0 = (while_option (Not o (worklist_is_empty summary))
                                           (take_step_locale df PR) c0)"

abbreviation empty_conf where
  "empty_conf \<equiv> \<lparr>c_work = (\<lambda> _.  {#}\<^sub>z), c_pts = (\<lambda> _.  {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>"

definition "propagate_all summary c0 = (while_option (Not o (worklist_is_empty summary))
                                        (take_step summary PR) c0)"

lemma take_step_fast_code[simp]:
  "take_step_locale df x = take_step (antichain_from_list oo (dataflow_tree_to_graph df)) x"
  unfolding take_step_locale_def
  apply (cases x)
   apply (auto simp add: fun_eq_iff mymin_code_def)
  done

lemma propagate_all_locale_eq_propagate_all:
  "propagate_all_locale (antichain_from_list oo (dataflow_tree_to_graph df)) df c = propagate_all (antichain_from_list oo (dataflow_tree_to_graph df)) c"
  unfolding propagate_all_locale_def Let_def propagate_all_def by (auto split: prod.splits)

abbreviation "show_frontier x \<equiv> let f = Max_antichain x in if f = 42 then STR ''{}'' else STR ''{ '' + show_nat (Max_antichain x) + STR '' }''" 

abbreviation "print_frontier x \<equiv> trace ((STR ''Frontier: '') + show_frontier x)" 

abbreviation "show_frontiers impf \<equiv> show_list (show_prod show_loc show_frontier) (map (\<lambda> l. (l, frontier (impf l))) enum_location_inst.enum_location)"

(* Inspired by timely/src/progress/subgraph.rs:453 *)
(* First migrate all change batches to the worklist, then call propagate_all_locale *)
definition "change_multiplicities summary xs conf = fold (\<lambda> (l, t, m) c. take_step summary (CM l t m) c) xs conf"

(* Inspired by timely/src/dataflow/operators/generic/builder_rc.rs:29 and timely/src/progress/operate.rs:63 *)
(* This is the shared that the operator exposes to the subgraph *)
record ('p, 't) shared_state =
  cons :: "('p \<times> 't \<times> int) change_batch"
  inte :: "('p \<times> 't \<times> int) change_batch"
  prod :: "('p \<times> 't \<times> int) change_batch"

(* Inspired by timely/src/progress/subgraph.rs:759 *)
definition extract_progress where
  "extract_progress nid nt st =
    map (\<lambda> (p, t, m). (Loc nid (Trg p), t, -m)) (cons st) @ 
    map (\<lambda> (p, t, m). (Loc nid (Src p), t, m)) (inte st) @
    List.map_filter (\<lambda> (p, t, m). case_option None (\<lambda> (nid', p'). Some (Loc nid' (Trg p'), t, m)) (nt (nid, p))) (prod st)"

(* Inspired by timely/src/dataflow/operators/capability.rs:62 *)
datatype ('p, 't) capability = Cap (time: "'t :: plus") (out: 'p)

abbreviation "nop sg op \<equiv> (case op of Read (Inl nid) f \<Rightarrow> upfro sg nid | _ \<Rightarrow> True)"

term upfro

(* Connects the data plane with the control plane (wraps the operators inside the propagation algorithm)  *)
corec dataflow_op where
  "dataflow_op sg op = Choice (cimage (\<lambda> op. case op of 
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None \<Rightarrow> \<oslash>)
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. dataflow_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (dataflow_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>)) (let C = cfilter (nop sg) (choices op) in C))"

lemma dataflow_op_code[code]:
  "dataflow_op sg op = Choice (cimage (\<lambda> op. case op of 
     Read (Inl nid) f \<Rightarrow> trace (STR ''Reading from frontier at nid: '' + print_2 nid) (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None \<Rightarrow> \<oslash>)
   | Read (Inr (nid, p)) f \<Rightarrow>  (Read (nid, p) (\<lambda> x. dataflow_op sg (f (Inr x))))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> trace (STR ''Writing out data at location: '' + show_loc (Loc nid (Src p))) (Write (dataflow_op sg op') (nid, p) x)     
   | Silent op' \<Rightarrow> trace (STR ''Some silent step'') Silent (dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow>
      trace (STR ''Reading progress at nid: '' + print_2 nid + STR '' cgs sizes: ('' + show_nat (length (cons st)) + STR '', '' + show_nat (length (inte st))  + STR '', '' + show_nat (length (prod st)) + STR '')''
   ) (Silent (dataflow_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr :=change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op'))
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>)) 
 (let C = cfilter (nop sg) (choices op) in C))"
  apply (simp only: trace_simp id_def)
  apply (subst dataflow_op.code[symmetric])
  apply auto
  done

lemma class_linorder_lt_of_comp:
  "ID ccompare = Some a \<Longrightarrow> class.linorder (\<lambda>t u. lt_of_comp a t u \<or> t = u) (lt_of_comp a)"
  apply (frule ID_ccompare)
  apply (erule arg_cong2[where ?f=class.linorder, THEN iffD1, rotated 2])
   apply (auto simp add: le_of_comp_def lt_of_comp_def fun_eq_iff split: order.splits)
   apply (meson ID_ccompare' comparator.nEq_neq_conv)
  apply (simp add: ID_code ccompare comparator.comp_same)
  done

lemma mymin_code_in_worklist:
  assumes "\<not> worklist_is_empty su c"
  and "mymin_code (t_loc_pairs c) = (t :: 't :: {order, ccompare}, (loc :: 'loc :: {enum,linorder}))"
  and "ID CCOMPARE('t) \<noteq> None"
  shows "t \<in>#\<^sub>z c_work c loc"
proof -
  (* First establish that we have a linorder on t_loc_linord cless *)
  have cless_linorder: "class.linorder (\<lambda>(t :: 't) u. cless t u \<or> t = u) cless"
  proof -
    from assms(3) obtain comp where comp: "ID CCOMPARE('t) = Some comp" by auto
    have "class.linorder (\<lambda>(t :: 't) u. lt_of_comp comp t u \<or> t = u) (lt_of_comp comp)"
      by (rule class_linorder_lt_of_comp[OF comp])
    also have "lt_of_comp comp = cless"
      using comp by simp
    finally show ?thesis 
      by assumption
  qed
  interpret tloc: linorder "t_loc_linord cless" "\<lambda>(t :: 't \<times> 'loc) u. t_loc_linord cless t u \<and> t \<noteq> u"
    by (rule linorder_t_loc_linord[OF cless_linorder])
  (* The set t_loc_pairs c is non-empty because worklist is not empty *)
  have nonempty: "t_loc_pairs c \<noteq> {}"
    using assms(1)
    unfolding worklist_is_empty_def t_loc_pairs_def enum_class.enum_UNIV
    by auto
  (* The set is finite *)
  have finite: "finite (t_loc_pairs c)"
    by (auto simp: t_loc_pairs_def intro:)
  
  (* Min is in the set *)
  have "(t, loc) \<in> t_loc_pairs c"
    using assms(2)
    unfolding mymin_code_def mymin_def
    using tloc.Min_in[OF finite nonempty]
    by simp
  
  then show ?thesis
    unfolding t_loc_pairs_def set_zmset_def
    by auto
qed

lemma mymin_code_is_minimum:
  assumes "\<not> worklist_is_empty su c"
  and "mymin_code (t_loc_pairs c) = (t :: 't :: {compare_order, ccompare}, (loc :: 'loc :: {enum,linorder}))"
  and "t' \<in>#\<^sub>z c_work c loc'"
  and "ID CCOMPARE('t) = Some compare"
  shows "\<not> t' < t"
proof -
  (* First establish that we have a linorder on t_loc_linord cless *)
  have cless_linorder: "class.linorder (\<lambda>(t :: 't) u. cless t u \<or> t = u) cless"
  proof -
    from assms(4) obtain comp where comp: "ID CCOMPARE('t) = Some comp" by auto
    have "class.linorder (\<lambda>t u. lt_of_comp comp t u \<or> t = u) (lt_of_comp comp)"
      by (rule class_linorder_lt_of_comp[OF comp])
    also have "lt_of_comp comp = (cless :: 't \<Rightarrow> 't \<Rightarrow> bool)"
      using comp by simp
    finally show ?thesis by assumption
  qed
  interpret tloc: linorder "t_loc_linord (cless :: 't \<Rightarrow> 't \<Rightarrow> bool)" "\<lambda>t u. t_loc_linord cless t u \<and> t \<noteq> u"
    by (rule linorder_t_loc_linord[OF cless_linorder])

  (* The set t_loc_pairs c is non-empty because worklist is not empty *)
  have nonempty: "t_loc_pairs c \<noteq> {}"
    using assms(1)
    unfolding worklist_is_empty_def t_loc_pairs_def enum_class.enum_UNIV
    by auto

  (* The set is finite *)
  have finite: "finite (t_loc_pairs c)"
    by (auto simp: t_loc_pairs_def)

  (* (t', loc') is in the set *)
  have t'_in: "(t', loc') \<in> t_loc_pairs c"
    using assms(3) unfolding t_loc_pairs_def set_zmset_def
    by (auto simp: enum_UNIV)

  (* Min is <= all elements *)
  have "t_loc_linord cless (t, loc) (t', loc')"
    using assms(2) t'_in
    unfolding mymin_code_def mymin_def
    using tloc.Min_le[OF finite t'_in]
    by simp

  (* t_loc_linord orders by timestamp first, so cless t t' or t = t' *)
  then have "cless t t' \<or> t = t'"
    unfolding t_loc_linord_def
    by (auto split: prod.splits)

  (* cless = (<) for compare_order types, so cless t t' means t < t' *)
  moreover have "(cless :: 't \<Rightarrow> 't \<Rightarrow> bool) = (<)"
    using assms(4) ord_defs(2) by (simp add: compare_order_class.ord_defs)
  ultimately show ?thesis
    by auto
qed

lemma take_step_enum_dataflow_topology_take_step:
  "enum_dataflow_topology su dataflow_topology_from_tree.followed_by \<Longrightarrow>
   take_step su = enum_dataflow_topology.take_step su dataflow_topology_from_tree.followed_by cless"
  apply (rule ext)+
  subgoal for S c
    apply (cases S; hypsubst_thin)
     apply (simp add: Executable.enum_dataflow_topology.take_step.simps)
    apply (subst Executable.enum_dataflow_topology.take_step.simps(2))
     apply assumption
    apply (simp add: after_summary_def mymin_code_def)
    done
  done

lemma take_step_PR_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary (-+-) \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   ID CCOMPARE('t) = Some compare \<Longrightarrow>
   \<exists>(t :: 't::  {compare,ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR) c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
     apply assumption
  subgoal
  apply (rule class_linorder_lt_of_comp)
    apply (simp add: linorder_class.linorder_axioms)
    done
   apply (clarsimp simp add: compare_order_class.ord_defs )
  apply (elim exE)
  subgoal for t loc loc' t'
    apply (subst take_step_enum_dataflow_topology_take_step)
     apply (simp add: enum_dataflow_topology_def)
    apply (rule Propagate.dataflow_topology.p_preserves_inv_imps_work_sum[where loc=loc and t=t'])
      apply assumption+
    done
  done

lemma take_step_PR_p_preserves_inv_implications_nonneg:
  "dataflow_topology su (-+-) \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   ID CCOMPARE('t) = Some compare \<Longrightarrow>
   \<exists>(t :: 't::  {compare,ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg (take_step su PR c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
     apply assumption
  subgoal
  apply (rule class_linorder_lt_of_comp)
    apply (simp add: linorder_class.linorder_axioms)
    done
     apply (clarsimp simp add: compare_order_class.ord_defs )
  defer
  apply (elim exE)
    apply (subst take_step_enum_dataflow_topology_take_step)
     apply (simp add: enum_dataflow_topology_def)
  apply simp
   apply (rule Propagate.dataflow_topology.p_preserves_inv_implications_nonneg[of _ _ c])
         apply assumption+
  done

lemma take_step_PR_p_preserves_inv_implications_nonneg:
  "dataflow_topology su (-+-) \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   ID CCOMPARE('t) = Some compare \<Longrightarrow>
   \<exists>(t :: 't::  {compare,ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg (take_step su PR c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
     apply assumption
  subgoal
  apply (rule class_linorder_lt_of_comp)
    apply (simp add: linorder_class.linorder_axioms)
    done
     apply (clarsimp simp add: compare_order_class.ord_defs )
  apply (elim exE)
    apply (subst take_step_enum_dataflow_topology_take_step)
     apply (simp add: enum_dataflow_topology_def)
  apply simp
  oops

lemma take_step_PR_p_preserves_inv:
  "dataflow_topology summary (-+-) \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   \<exists>(t :: 't::  {compare,ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   ID CCOMPARE('t) = Some compare \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary PR) c) \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg ((take_step summary PR) c) \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR) c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
  apply assumption
  subgoal
  apply (rule class_linorder_lt_of_comp)
    apply (simp add: linorder_class.linorder_axioms)
    done
   apply (clarsimp simp add: compare_order_class.ord_defs )
  apply (elim exE)
  subgoal for t loc loc' t'
    apply (subst (1 2) take_step_enum_dataflow_topology_take_step)
     apply (simp add: enum_dataflow_topology_def)
    apply (intro conjI)
      apply (rule Propagate.dataflow_topology.p_preserves_inv_implications_nonneg)
         apply assumption+
     apply (rule Propagate.dataflow_topology.iiws_imp_iipwn)
      apply assumption+
     apply (subst take_step_enum_dataflow_topology_take_step[symmetric])
      apply (simp add: enum_dataflow_topology_def)
     apply (rule take_step_PR_p_preserves_inv_imps_work_sum)
       apply assumption+
     apply auto[1]
    apply (rule take_step_PR_p_preserves_inv_imps_work_sum)
      apply assumption+
    apply auto
    done
  done

lemma propagate_all_terminates:
  assumes "dataflow_topology su (-+-)"
    and "Propagate.dataflow_topology.inv_imps_work_sum su (-+-) c"
    and "Propagate.dataflow_topology.inv_implications_nonneg (c :: ('loc :: {enum,linorder}, 't :: {compare_order,ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) configuration)"
    and "ID CCOMPARE('t) = Some compare"
    and "\<forall> loc. su loc loc = {}\<^sub>A"
    and "dataflow_topology_from_tree.inv_imp_plus_work_nonneg c"
  shows "propagate_all su c \<noteq> None"
  unfolding propagate_all_def
  apply simp
  apply (rule wf_rel_while_option_Some[where
        R = "inv_image {(x, y). x < y} (Termination.dataflow_topology.neg_order su dataflow_topology_from_tree.followed_by)" and
        P = "\<lambda>c. Propagate.dataflow_topology.inv_imps_work_sum su dataflow_topology_from_tree.followed_by c \<and>
             Propagate.dataflow_topology.inv_implications_nonneg c \<and> dataflow_topology_from_tree.inv_imp_plus_work_nonneg c"])
     apply (rule wf_inv_image, rule wellorder_class.wf)
  subgoal for s
    apply (clarsimp simp: inv_image_def split: prod.splits)
    apply (rule dataflow_topology.propagation_termination[OF assms(1)])
      defer 
      apply force
     apply force
    subgoal for t loc
      apply (simp add: dataflow_topology.next_propagate'_def[OF assms(1)])
      apply (rule exI[of _ loc])
      apply (rule exI[of _ t])
      apply (intro conjI impI)
      subgoal
        apply (rule mymin_code_in_worklist)
          apply assumption+
        using assms apply auto
        done
      subgoal
        apply (intro allI impI)
        apply (elim exE)
        subgoal for t' loc
        apply (rule mymin_code_is_minimum)
           apply assumption+
          using assms apply auto
          done
        done
      subgoal
        apply (cases s)
        apply clarsimp
        apply (rule ext)
        apply (auto split: )
         apply (subgoal_tac "su loc loc = {}\<^sub>A")
        apply simp
        using assms apply simp
        apply (simp add: dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.zmset_of_lemma)
        done
      done
    done
  subgoal
    apply safe
    subgoal
      apply (rule take_step_PR_p_preserves_inv_imps_work_sum[OF assms(1)])
        apply assumption+
      using assms(4) apply simp
      apply (metis trimono_spec_defs(3) worklist_is_empty_def zequal_equal zmultiset_nonemptyE)
      done
    subgoal
      apply (rule take_step_PR_p_preserves_inv_implications_nonneg[OF assms(1)])
         apply assumption+
      using assms apply auto
      apply (metis worklist_is_empty_def zequal_equal zmultiset_nonemptyE)
      done
    subgoal
      apply (drule take_step_PR_p_preserves_inv[OF assms(1)])
          apply assumption+
      apply (metis trimono_spec_defs(3) worklist_is_empty_def zequal_equal zmultiset_nonemptyE)
      using assms apply auto
      done
    done
  using assms apply auto
  done

(* FIXME: Update this for the new optimizations *)
lemma step_dataflow_op_elim:
  assumes "step io (dataflow_op sg op) op'"
  obtains
    nid p op'' x where "io = Inp (nid, p) x" "op' = dataflow_op sg op''" "step (Inp (Inr (nid, p)) (Inr x)) op op''"
  | nid p op'' x where "io = Out (nid, p) x" "op' = dataflow_op sg op''" "step (Out (Inr (nid, p)) (Inr x)) op op''"
  | op'' where "io = Tau" "op' = dataflow_op sg op''" "step Tau op op''"
  | nid op'' st where "io = Tau" "op' = dataflow_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := (change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg)) \<rparr>) op''" "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | nid op'' imp_fron sg' where "io = Tau" "sg' = (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr>)" "upfro sg nid"
    "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))" "op' = dataflow_op sg' op''" "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) dataflow_op.code)
  apply (simp split: if_splits)
  apply (elim stepChoiceE)
  subgoal for op'
    apply (auto del: disjCI split: op.splits sum.splits option.splits)
        apply fastforce+
    done
  done

lemma step_Tau_dataflow_op_Inp_Inl_intro[intro]:
  "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op' \<Longrightarrow>
   propagate_all(summ sg) (pt_tr sg) = Some conf' \<Longrightarrow>
   upfro sg nid \<Longrightarrow>
   sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> \<Longrightarrow>
   imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg' op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_op_Out_Inl_intro[intro]:
  "step (Out (Inl nid) (Inl (Inl st))) op op' \<Longrightarrow>
   sg' = sg\<lparr> upfro := (\<lambda> _. True), pt_tr := (change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg)) \<rparr> \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg' op')"
  apply (subst dataflow_op.code)
  apply (force elim: step_choicesE split: sum.splits option.splits)
  done


lemma step_Tau_dataflow_op_Tau_intro[intro]:
  "step Tau op op' \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Out_dataflow_op_Out_Inr_intro[intro!]:
  "step (Out (Inr (nid, p)) (Inr x)) op op' \<Longrightarrow>
   step (Out (nid, p) x) (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Inp_dataflow_op_Inp_Inr_intro[intro!]:
  "step (Inp (Inr (nid, p)) (Inr x)) op op' \<Longrightarrow>
   step (Inp (nid, p) x) (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma dataflow_op_end_op:
  "dataflow_op sg \<oslash> = \<oslash>"
  apply (subst dataflow_op.code)
  apply simp
  done

lemma steps_Tau_dataflow_op_Tau_intro[intro]:
  "steps (replicate n Tau) op op' \<Longrightarrow>
   (step Tau ^^ n) (dataflow_op sg op) (dataflow_op sg op')"
  apply (induct n arbitrary: op op' sg)
   apply clarsimp+
  apply (metis (no_types, lifting) relcompp_apply relpowp_commute step_Tau_dataflow_op_Tau_intro)
  done

lemma steps_Tau_dataflow_op_steps_Out_intro[intro]:
  "steps (map (\<lambda> x. Out (Inr (nid, p)) (Inr x)) xs) op op' \<Longrightarrow>
   (steps (map (\<lambda> x. Out (nid, p) x) xs)) (dataflow_op sg op) (dataflow_op sg op')"
  apply (induct xs arbitrary: op op' sg rule: rev_induct)
   apply clarsimp+
  apply fastforce
  done

lemma step_Taus_dataflow_op_Taus_intro[intro]:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   (step Tau)\<^sup>*\<^sup>*  (dataflow_op sg op) (dataflow_op sg op')"
  apply (induct op' rule: rtranclp_induct)
   apply force
  apply (meson rtranclp.intros(2) step_Tau_dataflow_op_Tau_intro)
  done


lemma step_tau_pow_dataflow_op[intro]:
  "(step Tau ^^ n) op op' \<Longrightarrow>
   (step Tau ^^ n) (dataflow_op sg op) (dataflow_op sg op')"
  by (induct n arbitrary:  op') auto

lemma step_tau_pow_map_op[intro]:
  "(step Tau ^^ n) op op' \<Longrightarrow> (step Tau ^^ n) (map_op f g op) (map_op f g op')"
  apply (induct n arbitrary: op op')
   apply simp_all
  subgoal for n op op'
    apply (elim relcomppE)
    apply (intro relcomppI)
     apply blast
    apply auto
    done
  done

lemma dataflow_op_simps[simp]:
  "\<not> is_Read (dataflow_op sg op)"
  "\<not> is_Write (dataflow_op sg op)"
  "\<not> is_Silent (dataflow_op sg op)"
  "is_Choice (dataflow_op sg op)"
  by (subst dataflow_op.code; simp)+

(* Inspired by timely/src/dataflow/channels/pushers/counter.rs:25 and timely/src/dataflow/channels/mod.rs:49 *)
(* writes maybe could support multiple different ports, then this one also would *)
abbreviation "push op p batch \<equiv> 
  writes op (trace (STR ''Pushing data!'') Some p) (map (\<lambda> (x, c). Inr (x, time c)) batch)"

abbreviation "delayed_cap c t \<equiv>
  (Cap (time c + abs t) (out c),
  \<lambda> op. Write op None 
     (Inl (Inl \<lparr> cons = [],
            inte = [(out c, time c, -1), (out c, time c + abs t, 1)],
            prod = [] \<rparr>)))"

(* The minted capability must depend on the internal wiring *)
abbreviation "pull i f \<equiv> (Read ((trace (STR ''Reading data'') Some) i)
  (\<lambda> x. case x of
    (Inr (d, t)) \<Rightarrow> Write (f (d, Cap t 0)) None (Inl (Inl \<lparr>  cons = [(i, t, 1)], inte = [(i, t, 1)], prod = [] \<rparr>))
   | _ \<Rightarrow> \<oslash>))"

lemma change_multiplicities_append:
  "change_multiplicities su (xs @ ys) = (\<lambda> c. change_multiplicities su ys (change_multiplicities su xs c))"
  unfolding change_multiplicities_def 
  apply (rule ext)
  apply simp
  done

lemma change_multiplicities_append_alt:
  "change_multiplicities su (xs @ ys) c = change_multiplicities su ys (change_multiplicities su xs c)"
  using change_multiplicities_append by metis

lemma change_multiplicities_append_comp:
  "change_multiplicities su (xs @ ys) = change_multiplicities su ys o change_multiplicities su xs"
  unfolding change_multiplicities_def
  apply simp
  done

lemma take_step_comm:
  "(take_step su (CM l2 t2 m2) \<circ>\<circ>\<circ> take_step) su (CM l1 t1 m1) = (take_step su (CM l1 t1 m1) \<circ>\<circ>\<circ> take_step) su (CM l2 t2 m2)"
  apply (rule ext)
  apply (auto simp add: fun_upd_twist update_zmultiset_comm)
  done

lemma take_step_plus[simp]:
  "take_step su (CM l t m) (take_step su (CM l t n) c) = take_step su (CM l t (m + n)) c"
  by (cases c; auto simp add: add.commute)

lemma change_multiplicitie_rev[simp]:
  "change_multiplicities su (rev xs) c = change_multiplicities su xs c"
  unfolding change_multiplicities_def
  apply (subst fold_rev)
   apply (clarsimp simp add: take_step_comm)+
  done

lemma change_multiplicities_comm:
  "change_multiplicities su (xs @ ys) c = change_multiplicities su (ys @ xs) c"
  unfolding change_multiplicities_def
  by (metis (mono_tags, lifting) change_multiplicitie_rev change_multiplicities_append change_multiplicities_def rev_append)

lemma change_multiplicities_simps[simp]:
  "change_multiplicities su [] c = c"
  "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su xs (take_step summary (CM l t m) c)"
  unfolding change_multiplicities_def by simp+

lemma change_multiplicities_simp_alt:
  "change_multiplicities su ((l, t, m) # xs) c = take_step su (CM l t m) (change_multiplicities su xs c)"
proof -
  have "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su (rev ((l, t, m) # xs)) c" using change_multiplicitie_rev by metis
  also have "\<dots> = take_step su (CM l t m) (change_multiplicities su (rev xs) c)" by (simp add: change_multiplicities_def foldr_conv_fold)
  ultimately show ?thesis by (metis change_multiplicitie_rev)
qed

lemma change_multiplicities_same_pointstamps_aux:
  "(\<forall> x \<in> set xs. \<forall> y \<in> set xs. fst x = fst y \<and> (fst o snd) x = (fst o snd) y) \<Longrightarrow>
   change_multiplicities su xs c = fold (\<lambda> m c. take_step su (CM ((fst o hd) xs) ((fst o snd o hd) xs) m) c) (map (snd o snd) xs) c"
  unfolding change_multiplicities_def
  apply (induct xs arbitrary: c)
   apply simp
  subgoal premises prems for a xs c
    using prems(2-) apply -
    apply (cases a; clarsimp)
    subgoal using prems(1)
      by (smt (verit) List.fold_cong List.fold_simps(1) fun_comp_eq_conv hd_in_set list.simps(8))
    done
  done

lemma change_multiplicities_same_pointstamps:
  "(\<forall> x \<in> set xs. \<forall> y \<in> set xs. fst x = l \<and> (fst o snd) x = t) \<Longrightarrow>
   m = sum_list (map (snd o snd) xs) \<Longrightarrow>
   change_multiplicities su xs c = take_step su (CM l t m) c"
  apply (induct xs arbitrary: c m)
   apply simp
  subgoal premises prems for x xs c m
    using prems(2-) apply -
    apply hypsubst_thin
    apply (cases x)
    subgoal for l t m
      apply (simp only: change_multiplicities_simp_alt)
      apply (subst prems(1))
        apply force
       apply (rule refl)
      apply clarsimp
      apply (intro conjI impI)
      subgoal by (metis (no_types) group_cancel.sub1 uminus_add_add_uminus update_zmultiset_comm update_zmultiset_plus)
      subgoal
        by blast 
      done
    done
  done

record ('p, 'd, 't) operator_state =
  intsum :: "'p \<Rightarrow> 'p \<Rightarrow> 't list"
  consu :: "('p \<times> 't \<times> int) list"
  inter :: "('p \<times> 't \<times> int) list"              
  produ :: "('p \<times> 't \<times> int) list"
  input :: "'p \<Rightarrow> ('d \<times> 't) list"
  outpu :: "'p \<Rightarrow> ('d \<times> 't) list"
  front :: "'p \<Rightarrow> 't antichain"
  ocaps :: "'p \<Rightarrow> 't list"
  initia :: bool
  nfron :: bool

definition "default_internal_summary = (\<lambda> p1 p2. if p1 = p2 then [0] else [])"

abbreviation init_op_state where
  "init_op_state su \<equiv> \<lparr> 
   intsum = su,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = undefined,
   ocaps = (\<lambda> _. []),
   initia = False,
   nfron = False
   \<rparr>"

abbreviation "init_c_pts summary cgs \<equiv> change_multiplicities summary cgs \<lparr>c_work = (\<lambda> _.  {#}\<^sub>z), c_pts = (\<lambda> _.  {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>"

abbreviation init_conf where
  "init_conf summary cgs \<equiv> the (propagate_all summary (init_c_pts summary cgs))"

record ('p, 'd, 'd1, 't) operator_state_ty = "('p, 'd, 't) operator_state" +
  en1 :: "'d1 \<Rightarrow> 'd" de1 :: "'d \<Rightarrow> 'd1" is_en1 :: "'d \<Rightarrow> bool"
record ('p, 'd, 'd1, 'd2, 't) operator_state_ty2 = "('p, 'd, 'd1, 't) operator_state_ty" +
  en2 :: "'d2 \<Rightarrow> 'd" de2 :: "'d \<Rightarrow> 'd2" is_en2 :: "'d \<Rightarrow> bool"
record ('p, 'd, 'd1, 'd2, 'd3, 't) operator_state_ty3 = "('p, 'd, 'd1, 'd2, 't) operator_state_ty2" +
  en3 :: "'d3 \<Rightarrow> 'd" de3 :: "'d \<Rightarrow> 'd3" is_en3 :: "'d \<Rightarrow> bool"

find_consts "_ set \<Rightarrow> _ option"

definition "graph_to_nxt summary = 
  (\<lambda> (nid, p). find (\<lambda> (nid', p'). \<not> is_empty_antichain (summary (Loc nid (Src p)) (Loc nid' (Trg p')))) Enum.enum)"

lemma zero_in_graph_path_weight[simp,intro]:
  "nt = graph_to_nxt su \<Longrightarrow>
   Graph.graph su \<Longrightarrow>
   (\<forall> nid nid' p p'. \<not> is_empty_antichain (su (Loc nid (Src p)) (Loc nid' (Trg p'))) \<longrightarrow> su (Loc nid (Src p)) (Loc nid' (Trg p')) = antichain {0}) \<Longrightarrow>
   nt (nid', p') = Some (nid, p) \<Longrightarrow>
   0 \<in>\<^sub>A graph.path_weight su (Loc nid' (Src p')) (Loc nid (Trg p))"
  unfolding graph_to_nxt_def Let_def
  apply (subst graph.in_path_weight)
   apply (clarsimp simp add: split: if_splits prod.splits)
  apply hypsubst_thin
  apply (drule spec2[of _ nid' nid])
  apply (drule spec2[of _ p' p])
  apply (subgoal_tac "su (Loc nid' (Src p')) (Loc nid (Trg p)) = antichain {0}")
  subgoal
    apply (auto simp add: minimal_antichain_def Graph.graph.path_weightp_def)
    subgoal
      apply (intro conjI exI)
       apply (rule graph.path.intros(2))
         apply assumption
        apply (rule graph.path.intros(1))
         apply assumption
        apply (rule refl)
       apply (simp add: member_antichain.rep_eq)
      apply auto
      done
    subgoal for xs
      using graph.sum_not_less_zero by blast
    done
  subgoal
    apply (clarsimp simp add: member_antichain.rep_eq find_Some_iff split: if_splits prod.splits)
    apply (metis surj_pair)
    done
  done

definition "init_subgraph summary cgs =
   \<lparr> pt_tr = init_conf summary cgs,
   nxt = graph_to_nxt summary,
   summ = summary, upfro = (\<lambda> _. True) \<rparr>"

definition "compile_dataflow chns dt = (let summary = antichain_from_list oo (dataflow_tree_to_graph dt) in
                                    let op = dataflow_tree_to_operator chns dt in
                                    let sg = init_subgraph summary (map (\<lambda> (nid, p). (Loc nid (Src p), bot, 1)) (List.product Enum.enum Enum.enum)) in
                                    dataflow_op sg op)"

definition "delay_cap os cap incr = (os\<lparr> inter := inter os @ [(out cap, time cap, -1), (out cap, time cap + incr, 1)] \<rparr>)"

definition "produce os cap batch = (if batch = [] then os else os\<lparr> outpu := (outpu os)(out cap := outpu os (out cap) @ map (\<lambda> x. (x, time cap)) batch), produ := produ os @ [(out cap, time cap, length batch)] \<rparr>)"

definition "consume os p t len = (if len = 0 then os else os\<lparr> consu := consu os @ [(p, t, len)] \<rparr>)"

abbreviation "choice4 op1 op2 op3 op4 \<equiv> choice2 (choice2 op1 op2) (choice2 op3 op4)"

abbreviation "choice5 op1 op2 op3 op4 op5 \<equiv> choice3 (choice2 op1 op2) (choice2 op3 op4) op5"

definition "mint_cap os p t = os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"
definition \<open>mint os caps p t = (if t \<in> set (caps p) then (caps, os) else (caps(p := caps p @ [t]), mint_cap os p t))\<close>


definition "produces os batch = os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"
abbreviation "send_progress op st \<equiv> Write op None (Inl (Inl st))"

definition "obtain_progress os = (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"

fun remove_last where
  "remove_last x [] = []"
| "remove_last x xs = (if last xs = x then butlast xs else remove_last x (butlast xs) @ [last xs])"

lemma mset_remove_last[simp]:
  \<open>mset (remove_last x xs) = mset xs - {#x#}\<close>
proof (induction x xs rule: remove_last.induct)
  case 1
  thus ?case
    by simp
next
  case 2
  thus ?case
    using add_diff_cancel_right' append_butlast_last_id diff_union_single_conv2 list.simps(3) mset.simps(1,2)
      mset_append mset_right_cancel_elem remove_1_mset_id_iff_notin remove_last.elims by (smt (verit))
qed

lemma set_remove_lastD:
  \<open>y \<in> set (remove_last x xs) \<Longrightarrow> y \<in> set xs\<close>
  using in_diffD mset_remove_last set_mset_mset by metis

fun list_diff where
  "list_diff ys [] = ys"
| "list_diff ys (x # xs) = list_diff (remove_last x ys) xs"

lemma mset_list_diff[simp]:
  \<open>mset (list_diff ys xs) = mset ys - mset xs\<close>
  by (induction ys xs rule: list_diff.induct) simp_all

lemma list_diff_Nil[simp]:
  \<open>list_diff xs xs = []\<close>
  using mset_list_diff Multiset.diff_cancel mset_zero_iff by metis

definition "drop_cap os cap = os\<lparr> inter := inter os @ [(out cap, time cap, -1)], ocaps := (ocaps os) ((out cap) := remove_last (time cap) (ocaps os (out cap))) \<rparr>"

definition "drop_caps os caps = os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, -1)) caps, ocaps := (\<lambda> p. list_diff (ocaps os p) (map time (filter (\<lambda> cap. out cap = p) caps))) \<rparr>"

definition "add_cap os p t = os\<lparr> inter := inter os @ [(p, t, 1)], ocaps := (ocaps os) (p := ocaps os p @ [t])  \<rparr>"

definition "add_caps os caps = os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, 1)) caps, ocaps := (\<lambda> p. ocaps os p @ map time (filter (\<lambda> cap. out cap = p) caps))  \<rparr>"

definition "consumes os p t d = add_caps (os\<lparr> consu := consu os @ [(p, t, 1)], input := BENQ p (d, t) (input os) \<rparr>) (concat (map (\<lambda> p'. map (\<lambda> t'. Cap (t -+- t') p') (intsum os p p')) enum_class.enum))"

lemma outpu_consumes[simp]:
  "outpu (consumes os p t d) p' = outpu os p'"
  unfolding consumes_def BENQ_def add_caps_def
  by (auto simp add: operator_state.defs)


definition "has_progress os = (consu os \<noteq> [] \<or> inter os \<noteq> [] \<or> produ os \<noteq> [])"

(* All timely operators are defined using this function. The logic is passed as argument. This is the only corec we need *)
corec builder_op where
  \<open>builder_op fb ips ops os logic =
  ( choice5
    (if initia os \<and> (\<exists>p. ocaps os p \<noteq> []) then
      Choice (cimage (\<lambda>os. Silent (builder_op fb ips ops os logic)) (logic os))
    else \<oslash>)
    (Choice (cimage (\<lambda>p. case outpu os p of
      x # xs \<Rightarrow> send_output (builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic) p x)
      (cfilter (\<lambda>p. outpu os p \<noteq> []) ops)))
    (if fb then Read None (\<lambda>x. case x of
      Inl (Inr f) \<Rightarrow> builder_op fb ips ops (os\<lparr>front := f, initia := True, nfron := \<exists>p. f p \<noteq> front os p\<rparr>) logic
    | _ \<Rightarrow> Code.abort (STR ''Builder_op breaks contract'') (\<lambda>_. \<oslash>))
     else \<oslash>)
    (Choice (cimage (\<lambda>p. Read (Some p) (\<lambda>x. case x of
      Inr (d, t) \<Rightarrow> builder_op fb ips ops (consumes os p t d) logic
    | Inl _ \<Rightarrow> Code.abort (STR ''Builder_op breaks contract'') (\<lambda> _. \<oslash>))) ips))
    (if has_progress os then
      let (os', st) = obtain_progress os in send_progress (builder_op fb ips ops os' logic) st
    else \<oslash>))\<close>


lemma step_builder_op_elim:
  assumes \<open>step io (builder_op fb ips ops os logic) op\<close>
  obtains (read_end_None) x where \<open>io = Inp None x\<close> \<open>is_Inr x \<or> is_Inl x \<and> is_Inl (projl x)\<close> \<open>op = \<oslash>\<close>
  | (read_frontier) f where \<open>io = Inp None (Inl (Inr f))\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>front := f, initia := True, nfron := \<exists>p. f p \<noteq> front os p\<rparr>) logic\<close> \<open>fb\<close>
  | (read_end_Some) p x where \<open>io = Inp (Some p) x\<close> \<open>p |\<in>| ips\<close> \<open>is_Inl x\<close> \<open>op = \<oslash>\<close>
  | (read_data) p d t where \<open>io = Inp (Some p) (Inr (d, t))\<close> \<open>p |\<in>| ips\<close>
    \<open>op = builder_op fb ips ops (consumes os p t d) logic\<close>
  | (write_state) os' st where \<open>io = Out None (Inl (Inl st))\<close>
    \<open>has_progress os\<close> \<open>(os', st) = obtain_progress os\<close>
    \<open>op = builder_op fb ips ops os' logic\<close>
  | (write_data) p x xs where \<open>io = Out (Some p) (Inr x)\<close> \<open>p |\<in>| ops\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic\<close>
  | (silent) os' where \<open>io = Tau\<close> \<open>initia os\<close> \<open>\<exists>p. ocaps os p \<noteq> []\<close>
    \<open>os' |\<in>| logic os\<close> \<open>op = builder_op fb ips ops os' logic\<close>
proof (cases io)
  case (Inp p x)
  show ?thesis
  proof (cases p)
    case None
    consider (unexpected) \<open>is_Inr x \<or> is_Inl x \<and> is_Inl (projl x)\<close> | (frontier) f where \<open>x = Inl (Inr f)\<close>
      by (metis is_Inl.simps(1) is_Inr.simps(1) sum.sel(1) sumE)
    thus ?thesis
    proof cases
      case unexpected
      hence \<open>op = \<oslash>\<close> using assms Inp None
        apply -
        apply (subst (asm) builder_op.code)
        apply (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def split: if_splits list.splits sum.splits)
        done
        thus ?thesis using read_end_None Inp None unexpected by blast
    next
      case frontier
      show ?thesis
      proof (cases \<open>initia os\<close>)
        case True
        hence \<open>fb \<and> op = builder_op fb ips ops (os\<lparr>front := f, initia := True, nfron := \<exists>p. f p \<noteq> front os p\<rparr>) logic\<close>
          using assms Inp None frontier by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
        thus ?thesis using read_frontier Inp None frontier True by blast
      next
        case False
        hence \<open>fb \<and> op = builder_op fb ips ops (os\<lparr>front := f, initia := True, nfron := \<exists>p. f p \<noteq> front os p\<rparr>) logic\<close>
          using assms Inp None frontier by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
        thus ?thesis using read_frontier Inp None frontier False by blast
      qed
    qed
  next
    case (Some p')
    consider (unexpected) \<open>is_Inl x\<close> | (data) d t where \<open>x = Inr (d, t)\<close>
      using is_Inl.simps(1) obj_sumE surj_pair by metis
    thus ?thesis
    proof cases
      case unexpected
      hence \<open>p' |\<in>| ips \<and> op = \<oslash>\<close> using assms Inp Some by (subst (asm) builder_op.code)
          (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits sum.splits)
      thus ?thesis using read_end_Some Inp Some unexpected by simp
    next
      case data
      hence \<open>p' |\<in>| ips \<and> op = builder_op fb ips ops (consumes os p' t d) logic\<close> using assms Inp Some
        by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
      thus ?thesis using read_data Inp Some data by blast
    qed
  qed
next
  case (Out p x)
  show ?thesis
  proof (cases p)
    case None
    hence progress: \<open>has_progress os\<close> using assms Out
      by (subst (asm) builder_op.code) (auto 0 0 simp add:  split: if_splits list.splits)
    obtain os' st where os'_st: \<open>(os', st) = obtain_progress os\<close> unfolding obtain_progress_def by blast
    hence \<open>x = Inl (Inl st) \<and> op = builder_op fb ips ops os' logic\<close> using assms Out None progress
      by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
    thus ?thesis using write_state Out None progress os'_st by blast
  next
    case (Some p')
    then obtain x' xs where x'_xs: \<open>x = Inr x'\<close> \<open>outpu os p' = x' # xs\<close> using assms Out
      apply -
      apply (subst (asm) builder_op.code)
      apply (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
      done
    have \<open>p' |\<in>| ops \<and> op = builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p' := xs)\<rparr>) logic\<close>
      using assms Out Some x'_xs by (subst (asm) builder_op.code)
        (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
    thus ?thesis using write_data Out Some x'_xs by blast
  qed
next
  case Tau
  hence initialized: \<open>initia os\<close> 
    using assms apply -
    apply (subst (asm) builder_op.code)
    apply (auto split: if_splits list.splits prod.splits)
    done
  moreover from this have \<open>\<exists>p. ocaps os p \<noteq> []\<close> using Tau assms
    by (subst (asm) builder_op.code) (auto split: if_splits list.splits simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def )
  moreover obtain os' where \<open>os' |\<in>| logic os\<close> \<open>op = builder_op fb ips ops os' logic\<close>
  proof -
    have \<open>Silent op |\<in>| choices (builder_op fb ips ops os logic)\<close> using Tau assms step_choicesE by blast
    thus ?thesis using that
      by (subst (asm) builder_op.code) (auto 0 0 simp add: initialized neq_Nil_conv drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits)
  qed
  ultimately show ?thesis using silent Tau by blast
qed

lemma step_builder_op_Read_None[intro]:
  assumes \<open>io = Inp None (Inl (Inr f))\<close> \<open>fb\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>front := f, initia := True, nfron := \<exists>p. f p \<noteq> front os p\<rparr>) logic\<close>
  shows \<open>step io (builder_op fb ips ops os logic) op\<close>
proof -
  let ?g = \<open>\<lambda>x. case x of Inl (Inr f) \<Rightarrow> builder_op fb ips ops (os\<lparr>front := f,initia := True, nfron := \<exists>p. f p \<noteq> front os p\<rparr>) logic | _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read None ?g |\<in>| choices (builder_op fb ips ops os logic)\<close> using assms
    by (subst (2) builder_op.code) force
  moreover have \<open>?g (Inl (Inr f)) = op\<close> using assms by simp
  ultimately show ?thesis using assms(1) by blast
qed

lemma step_builder_op_Read_Some[intro]:
  assumes \<open>io = Inp (Some p) (Inr (d, t))\<close> \<open>p |\<in>| ips\<close>
    \<open>op = builder_op fb ips ops (consumes os p t d) logic\<close>
  shows \<open>step io (builder_op fb ips ops os logic) op\<close>
proof -
  let ?f = \<open>\<lambda>x. case x of Inr (d, t) \<Rightarrow> builder_op fb ips ops (consumes os p t d) logic | Inl _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read (Some p) ?f |\<in>| choices (builder_op fb ips ops os logic)\<close> using assms(2,3)
    by (subst (2) builder_op.code) fastforce
  moreover have \<open>?f (Inr (d, t)) = op\<close> using assms by simp
  ultimately show ?thesis using assms(1) by blast
qed

lemma step_builder_op_Write_None[intro]:
  \<open>io = Out None (Inl (Inl st)) \<Longrightarrow> has_progress os \<Longrightarrow>
  (os', st) = obtain_progress os \<Longrightarrow> op = builder_op fb ips ops os' logic \<Longrightarrow>
  step io (builder_op fb ips ops os logic) op\<close>
  by (subst builder_op.code) (auto simp add: has_progress_def obtain_progress_def)

lemma step_builder_op_Write_Some[intro]:
  assumes \<open>io = Out (Some p) (Inr x)\<close> \<open>p |\<in>| ops\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic\<close>
  shows \<open>step io (builder_op fb ips ops os logic) op\<close>
  using assms
proof -
  have \<open>send_output op p x |\<in>| choices (builder_op fb ips ops os logic)\<close> using assms(2-)
    by (subst builder_op.code) force
  thus ?thesis using assms(1) by blast
qed

lemma steps_builder_op_Write_Some[intro]:
  assumes \<open>p |\<in>| ops\<close> \<open>outpu os p = xs @ ys\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p := ys)\<rparr>) logic\<close>
  shows \<open>steps (map (\<lambda> x. Out (Some p) (Inr x)) xs) (builder_op fb ips ops os logic) op\<close>
  using assms apply -
  apply (induct xs arbitrary: os logic op ys rule: rev_induct)
  apply auto[1]
  apply fastforce
  done

lemma step_builder_op_Silent[intro]:
  assumes \<open>io = Tau\<close> \<open>initia os\<close> \<open>ocaps os p \<noteq> []\<close> \<open>os' |\<in>| logic os\<close>
    \<open>op = builder_op fb ips ops os' logic\<close>
  shows \<open>step io (builder_op fb ips ops os logic) op\<close>
proof -
  have \<open>Silent op |\<in>| choices (builder_op fb ips ops os logic)\<close> using assms(2-)
    by (subst builder_op.code) auto
  thus ?thesis using assms(1) by blast
qed

lemma step_builder_op_n_Silents[intro]:
  assumes 
    \<open>os' |\<in>| ((\<lambda> oss. (cUnion (cimage logic (cfilter (\<lambda> os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) oss)))) ^^ n) {| os |}\<close>
    \<open>op = builder_op fb ips ops os' logic\<close>
  shows \<open>(step Tau ^^ n) (builder_op fb ips ops os logic) op\<close>
  using assms apply -
  apply (induct n arbitrary: os os' op)
  subgoal
    by auto
  subgoal premises prems for n os os' op
    using prems(2-) apply -
    apply (clarsimp simp flip: cin.rep_eq)
    apply (intro relcomppI)
    apply hypsubst_thin
     apply (rule prems(1)[rotated])
      apply (rule refl)
    defer
     apply (rule step_builder_op_Silent)
    apply simp_all
    done
  done

definition notifier_op where
  "notifier_op ips ops os logic = (builder_op True ips ops os
   (\<lambda> os.
    if nfron os then
    logic (os\<lparr> nfron := False \<rparr>) (\<lambda> p. filter (\<lambda> t. \<not> frontier_less_equal (front os p) t) (ocaps os p))
    else {||}))"




fun zmset where
  "zmset [] = {#}\<^sub>z"
| "zmset ((x, d) # xs) = update_zmultiset (zmset xs) x d"

lemma update_zmultiset_plus[simp]:
  "update_zmultiset (A + B) x n = update_zmultiset A x n + B"
  apply transfer
  apply (auto simp: equiv_zmset_def)
  subgoal for A B A' B'
    apply (auto simp add: multiset_eq_iff split: if_splits)
    done
  done

lemma zmset_append[simp]:
  "zmset (xs @ ys) = zmset xs + zmset ys"
  apply (induct xs arbitrary: ys)
   apply auto
  done

lemma minus_zmset:
  "- zmset ys = zmset (map (\<lambda>(x, m). (x, - m)) ys)"
  apply (induct ys rule: rev_induct)
   apply clarsimp+
  apply (smt (verit, del_insts) Executable.update_zmultiset_plus Timely_Infrastructure.update_zmultiset_plus add.commute add.inverse_distrib_swap add_cancel_left_left minus_unique)
  done

lemma zmset_minus:
  "zmset xs - zmset ys = zmset (xs @ map (\<lambda> (x, m). (x, -m)) ys)"
  apply (induct xs arbitrary: ys)
   apply (clarsimp simp add: minus_zmset)+
  apply (metis add_uminus_conv_diff minus_zmset)
  done

lemma zmset_concat:
  "zmset (concat xs) = sum_list (map zmset xs)"
  by (induct xs) auto

lemma update_zmultiset_plus_comm:
  "update_zmultiset A x n + B = A + update_zmultiset B x n"
  apply transfer
  apply (auto simp: equiv_zmset_def)
  subgoal for A B A' B'
    apply (auto simp add: multiset_eq_iff split: if_splits)
    done
  done

lemma zmset_map_neg[simp]:
  "zmset (map (\<lambda> (t, m). (t, - m)) xs) = - zmset xs"
  apply (induct xs)
   apply clarsimp+
  apply (metis Executable.update_zmultiset_plus add_eq_0_iff update_zmultiset_plus_comm update_zmultiset_simps(1))
  done

lemma zmset_map_alt[simp]:
  "zmset (map (\<lambda>x. (fst (snd x), snd (snd x))) xs) = zmset (map snd xs)"
  apply (induct xs)
   apply clarsimp+
  done

lemma zmset_neg_alt[simp]:
  "zmset (map (\<lambda>x. (fst (snd x), - snd (snd x))) xs) = - zmset (map snd xs)"
  apply (induct xs)
   apply clarsimp+
  apply (metis Executable.update_zmultiset_plus add_eq_0_iff update_zmultiset_plus_comm update_zmultiset_simps(1))
  done

lemma zcount_zmset_ge_0I:
  "(\<forall> (x, m) \<in> set xs. 0 \<le> m) \<Longrightarrow>
   zcount (zmset xs) t \<ge> 0"
  by (induct xs) 
    (auto simp add: zcount_update_zmultiset)
lemma zcount_zmset_le_0I:
  "(\<forall> (x, m) \<in> set xs. x = t \<longrightarrow> 0 \<ge> m) \<Longrightarrow>
   zcount (zmset xs) t \<le> 0"
  by (induct xs) 
    (auto simp add: zcount_update_zmultiset)
lemma zcount_zmset_eq_0I:
  "(\<forall> (t', m) \<in> set xs. t' \<noteq> t) \<Longrightarrow>
   zcount (zmset xs) t = 0"
  by (induct xs) 
    (auto simp add: zcount_update_zmultiset)

lemma gt_0_zcount_msetD:
  "0 < zcount (zmset (map snd (filter ((=) p \<circ> fst) xs))) t \<Longrightarrow>
   \<exists> m. (p, t, m) \<in> set xs \<and> 0 < m"
  apply (induct xs)
   apply (auto simp add: zcount_update_zmultiset  split: if_splits)
  subgoal for x xs'
    apply (cases "0 < zcount (zmset (map snd (filter ((=) p \<circ> fst) xs'))) t")
     apply auto
    done
  done

lemma zcount_zmset_gt_0I:
  "(\<forall> (x, m) \<in> set xs. 0 \<le> m) \<Longrightarrow>
   (t, m) \<in> set xs \<Longrightarrow>
   0 < m \<Longrightarrow>
   zcount (zmset xs) t > 0"
  apply (induct xs) 
   apply (clarsimp simp add: zcount_update_zmultiset split: prod.splits)+
  apply (smt (verit, best) case_prodI2 zcount_zmset_ge_0I)
  done

lemma zmset_replicate[simp]:
  "zmset (replicate n (x, m)) = update_zmultiset {#}\<^sub>z x (n * m)"
  by (induct n)
    (auto simp add: Groups.add_ac(2) distrib_right)

lemma sum_sum_product:
  "(\<Sum>x\<in>A. \<Sum>y\<in>B. f x y) = (\<Sum>x\<in>A \<times> B. f (fst x) (snd x))"
  by (metis (mono_tags, lifting) case_prod_unfold sum.cartesian_product sum.cong)

lemma filter_if_const[simp]:
  "filter (\<lambda>x. p = fst x) (if P p then xs else []) =
   filter (\<lambda>x. p = fst x \<and> P p) xs"
  by auto

lemma sum_if:
  "finite S \<Longrightarrow>
   Collect f \<subseteq> S \<Longrightarrow>
   sum Z (Collect f) = sum (\<lambda> x. if f x then Z x else 0) S"
  apply (subst Groups_Big.comm_monoid_add_class.sum.inter_filter[symmetric])
   apply assumption
  apply (metis basic_trans_rules(31) mem_Collect_eq)
  done

lemma sum_list_zmset:
  "(\<Sum>x\<leftarrow>xs. zmset (f x)) = (zmset (concat (map f xs)))"
  apply (induct xs)
   apply auto
  done

lemma c_pts_change_multiplicities:
  "c_pts (change_multiplicities su xs c) = (\<lambda> l. c_pts c l + zmset (map snd (filter (\<lambda> (l', t, d). l = l') xs)))"
  apply (induct xs arbitrary: c)
   apply simp
  subgoal for x xs c
    apply (rule ext)+
    apply (cases x)
    apply (auto split: if_splits prod.splits simp add: change_multiplicities_simp_alt update_zmultiset_plus_comm) 
    done
  done

lemma zmset_emptyI:
  "xs = [] \<Longrightarrow> zmset xs = {#}\<^sub>z"
  by auto


lemma concat_map_time_filter_out[simp]:
  "distinct ps \<Longrightarrow> p \<in> set ps \<Longrightarrow> concat (map (\<lambda>x. map time (filter (\<lambda>x. out x = p) (map (\<lambda>t'. Cap (t -+- t') x) (xs x)))) ps) = map ((-+-) t) (xs p)"
  apply (induct ps)
   apply simp
  subgoal premises prems for p' ps'
    apply (cases "p = p'")
    subgoal
      apply hypsubst_thin
      apply (clarsimp simp add: comp_def filter_empty_conv)
      using prems(2) apply -
      subgoal
        by (meson distinct.simps(2))
      done
    subgoal
      using prems apply -
      apply auto
      done
    done
  done

lemma zmset_map_filter_aux[simp]:
  "finite S \<Longrightarrow> 
   nid \<in> S \<Longrightarrow>
  (\<Sum>x\<in>S. zmset (map snd (filter (\<lambda>xa. nid = x) (filter (\<lambda>xa. p = fst xa) (xs x))))) = zmset (map snd (filter (\<lambda>x. p = fst x) (xs nid)))"
  apply (induct S rule: finite_induct)
   apply auto
  subgoal
    apply (rule comm_monoid_add_class.sum.neutral)
    apply clarsimp
    apply (rule zmset_emptyI)
    apply (auto simp add: filter_empty_conv)
    done
  subgoal
    by (metis (mono_tags, lifting) arith_extra_simps(12) diff_zero filter_False list.map(1) zmset.simps(1))
  done

lemma sum_zmset_neg[simp]:
  "(\<Sum>x\<in>S. - zmset (xs x)) = - (\<Sum>x\<in>S. zmset (xs x))"
  by (metis (mono_tags, lifting) add_eq_0_iff sum.distrib sum.not_neutral_contains_not_neutral)


lemma zmset_map_filter[simp]:
  "finite S \<Longrightarrow>
   nid \<in> S \<Longrightarrow>
   (\<Sum>x\<in>S. zmset (map snd ((filter (\<lambda>xa. nid = x \<and> p = fst xa) (xs x))))) = 
   zmset (map snd (filter (\<lambda>x. p = fst x) (xs nid)))"
  apply (subst conj.commute)
  apply (clarsimp simp add: simp flip: filter_filter)+
  done

lemma zmset_map_one[simp]:
  "zmset (map (\<lambda> x. (f x, 1)) xs) = to_zmset (map f xs)"
  apply (induction xs) 
   apply clarsimp+
  using update_zmultiset_one(2) apply fastforce
  done
lemma zmset_map_minus_one[simp]:
  "zmset (map (\<lambda> x. (f x, -1)) xs) = - to_zmset (map f xs)"
  apply (induction xs) 
   apply clarsimp+
  apply (metis add_zmset_add_single neg_neg_multiset update_zmultiset_one(1))
  done


lemma sum_list_zmset_emptyI[intro]:
  "(\<forall> nid \<in> set nids. xs nid = []) \<Longrightarrow>
   (\<Sum>x\<leftarrow>nids. zmset (map snd (xs x))) = {#}\<^sub>z"
  apply (induct nids)
   apply auto
  done

lemma sum_list_filter[simp]:
  "distinct nids \<Longrightarrow>
   nid \<in> set nids \<Longrightarrow>
   g [] = {#}\<^sub>z \<Longrightarrow>
   (\<Sum>x\<leftarrow>nids. g (map f (filter (\<lambda>xa. nid = x) (xs x)))) = g (map f (xs nid))"
  apply (induct nids)
   apply clarsimp+
  apply (elim disjE)
  subgoal for nids' 
    by (smt (verit, best) List.empty_filter_conv filter_id_conv group_cancel.rule0 list.simps(8) sum.not_neutral_contains_not_neutral sum_list_distinct_conv_sum_set)
  subgoal for nid' nids'
    by (metis (mono_tags, lifting) add_cancel_right_left filter_empty_conv list.map(1))
  done


lemma consu_consumes[simp]:
  "consu (consumes os p t d) = consu os @ [(p, t, 1)]"
  unfolding consumes_def BENQ_def add_caps_def
  apply auto
  done
lemma produ_consumes[simp]:
  "produ (consumes os p t d) = produ os"
  unfolding consumes_def BENQ_def add_caps_def
  by auto
lemma inter_consumes[simp]:
  "inter (consumes os p t d) = inter os @ concat (map (\<lambda> p'. map (\<lambda> t'. (p', t + t', 1)) (intsum os p p')) enum_class.enum)"
  unfolding consumes_def BENQ_def add_caps_def
  by (auto simp add: map_concat comp_def)
lemma front_consumes[simp]:
  "front (consumes (os nid) p t d) p' = front (os nid) p'"
  unfolding consumes_def add_caps_def
  apply auto
  done
lemma consu_add_caps[simp]:
  "consu (add_caps os caps) = consu os"
  unfolding add_caps_def
  apply auto
  done
lemma inter_add_caps[simp]:
  "inter (add_caps os caps) = inter os @ map (\<lambda>cap. (out cap, time cap, 1)) caps"
  unfolding add_caps_def
  apply auto
  done
lemma produ_add_caps[simp]:
  "produ (add_caps os caps) = produ os"
  unfolding add_caps_def
  apply auto
  done
lemma outpu_obtain_progress[simp]:
  "outpu (fst (obtain_progress os)) = outpu os"
  unfolding obtain_progress_def by simp
lemma inter_obtain_progress[simp]:
  "inter (fst (obtain_progress os)) = []"
  unfolding obtain_progress_def by simp
lemma produ_obtain_progress[simp]:
  "produ (fst (obtain_progress os)) = []"
  unfolding obtain_progress_def by simp
lemma consu_obtain_progress[simp]:
  "consu (fst (obtain_progress os)) = []"
  unfolding obtain_progress_def by simp
lemma set_zmset_zmset_of_mset_set[simp]:
  "finite S \<Longrightarrow>
   set_zmset (zmset_of (mset_set S)) = S"
  unfolding set_zmset_def
  by clarsimp
lemma extract_progress_obtain_progress_obtain_progress[simp]:
  "extract_progress nid su (snd (obtain_progress (fst (obtain_progress (os nid))))) = []"
  unfolding obtain_progress_def extract_progress_def
  by auto
lemma intsum_consumes[simp]:
  "intsum (consumes os p t d) = intsum os"
  unfolding consumes_def add_caps_def
  apply auto
  done

lemma frontier_less_equal_ifrontierI:
  "dataflow_topology su (-+-) \<Longrightarrow>
   t' \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (frontier (c_pts c l)) t \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') (t + t')"
  apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_less_equal_sumI[where l=l])
     apply simp_all
   apply (simp add: sum_nonneg zcount_sum)
  apply (rule frontier_less_equal_sumI[of _ _ t'])
     apply simp_all
  using member_antichain.rep_eq apply blast
  unfolding frontier_less_equal_iff2
  apply clarsimp
  subgoal for t''
    apply (rule exI[of _ "t'' + t'"])
    apply clarsimp
    apply (rule in_frontierI)
     apply auto
     apply (metis frontier_idempotent in_frontier_iff pos_zcount_image_zmset zmset_of_mset_set_ge_zero)
    apply (metis (no_types, lifting) add_less_cancel_right dataflow_topology_from_tree.in_frontier_least frontier_idempotent pos_image_zmset_obtain_pre zmset_of_mset_set_ge_zero)
    done
  done

lemma frontier_less_equal_ifrontierI_alt:
  "dataflow_topology su (-+-) \<Longrightarrow>
   (\<exists> t'\<le>t''. t' \<in>\<^sub>A graph.path_weight su l l') \<Longrightarrow>
   frontier_less_equal (frontier (c_pts c l)) t \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') (t + t'')"
  by (meson add_left_mono frontier_less_equal_ifrontierI frontier_less_equal_trans)


lemma frontier_less_equal_le_frontier:
  "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (f l) t) \<Longrightarrow>
   f l \<le> frontier (zmset (map snd (filter (\<lambda>(l', t, d). l = l') A)))"
  apply (induct A rule: rev_induct)
   apply simp
  apply (clarsimp split: prod.splits)
  apply (smt (verit, del_insts) frontier_le_add frontier_less_equal_iff2 less_eq_antichain_def member_frontier_pos_zmset zcount_empty zcount_update_zmultiset)
  done

lemma in_frontier_zmset_image:
  "(\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   t \<in>\<^sub>A frontier {#t -+- s. t \<in>#\<^sub>z M#} \<longleftrightarrow> (\<exists> t'. t = t' -+- s \<and> t' \<in>\<^sub>A frontier M)"
  apply transfer
  apply (auto simp add: minimal_antichain_def)
    apply (metis (no_types, lifting) add_strict_right_mono pos_image_zmset_obtain_pre pos_zcount_image_zmset)
   apply (meson pos_zcount_image_zmset)
  apply (metis add_less_cancel_right pos_image_zmset_obtain_pre)
  done

lemma frontier_less_equal_ifrontierE:
  "frontier_less_equal (ifrontier su (-+-) c l') t \<Longrightarrow> 
   dataflow_topology su (-+-) \<Longrightarrow>
   \<exists> l s t'. s \<in>\<^sub>A graph.path_weight su l l' \<and> frontier_less_equal (frontier (c_pts c l)) t' \<and> t = t' + s"
  apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply simp_all
  apply (drule frontier_less_equal_sumE)
   apply clarsimp+
  apply (drule frontier_less_equal_sumE)
   apply clarsimp+
  subgoal for l s
    apply (rule exI[of _ l])
    apply (rule exI[of _ s])
    apply (intro conjI)
    using member_antichain.rep_eq apply blast
    subgoal premises prems
      using prems(3) apply -
      unfolding frontier_less_equal_iff2
      apply (clarsimp simp add: in_frontier_zmset_image)
      apply (metis add.commute add.left_commute dataflow_topology_from_tree.le_plus(2) less_eqE)
      done
    done
  done


lemma frontier_add_le_l:
  "frontier A \<le> X \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> X"
  using frontier_below_eq_frontier_plus_pos order_trans_rules(23) by blast
lemma frontier_add_le_r:
  "frontier B \<le> X \<Longrightarrow>
   (\<forall> t. zcount A t \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> X"
  using frontier_below_eq_frontier_plus_pos order_trans_rules(23) by (metis Groups.add_ac(2))

lemma frontier_le_image_gen:
  "frontier M \<le> frontier M' \<Longrightarrow>
   (\<forall> t. zcount M' t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   s \<le> s' \<Longrightarrow>
   frontier {#t -+- s. t \<in>#\<^sub>z M#} \<le> frontier {#t -+- s'. t \<in>#\<^sub>z M'#}"
  unfolding less_eq_antichain_def
  apply clarsimp
  apply (metis dataflow_topology_from_tree.results_in_mono_raw in_frontier_zmset_image)
  done

lemma sum_zmset:
  "finite S \<Longrightarrow>
   (\<Sum>s\<in>S. {#t -+- s#}\<^sub>z) = zmset_of (mset_set (((-+-) t) ` S))"
  apply (induct S rule: finite_induct)
   apply simp_all
  subgoal for x S
    by (metis (no_types, lifting) add_left_imp_eq finite_imageI imageE mset_set.insert zmset_of_add_mset)
  done


lemma frontier_less_equal_ifrontier_trans:
  "dataflow_topology su (-+-) \<Longrightarrow>
   t' \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) t \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') (t -+- t')"
  apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (drule frontier_less_equal_ifrontierE)
   apply assumption
  apply clarsimp+
  subgoal for l' s t''
    apply (frule Graph.graph.path_weight_elem_trans[rotated, of s])
      apply assumption+
    using dataflow_topology.axioms(1) apply blast
    apply clarsimp
    subgoal for u
      apply (rule frontier_less_equal_sumI[of _ _ l'])
         apply (simp_all add: sum_nonneg zcount_sum)
      apply (rule frontier_less_equal_sumI[of _ _ u])
         apply (simp_all add: sum_nonneg zcount_sum)
      using member_antichain.rep_eq apply blast
      unfolding frontier_less_equal_iff2
      apply (clarsimp simp add: in_frontier_zmset_image)
      apply (metis dataflow_topology_from_tree.plus_mono group_cancel.add1)
      done
    done
  done

lemma frontier_less_equal_ifrontier_trans_alt:
  "dataflow_topology su (-+-) \<Longrightarrow>
   (\<exists>t'\<le>t''. t' \<in>\<^sub>A graph.path_weight su l l') \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) t \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') (t -+- t'')"
  by (meson add_le_cancel_left frontier_less_equal_ifrontier_trans frontier_less_equal_trans)


lemma frontier_less_equal_ifrontier_trans_alt2:
  "dataflow_topology su (-+-) \<Longrightarrow>
   s \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) t \<Longrightarrow>
   t -+- s \<le> t' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') t'"
  using frontier_less_equal_ifrontier_trans frontier_less_equal_trans by blast


lemma frontier_le_image:
  "frontier M \<le> frontier M' \<Longrightarrow>
   (\<forall> t. zcount M' t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   frontier {#t -+- s. t \<in>#\<^sub>z M#} \<le> frontier {#t -+- s. t \<in>#\<^sub>z M'#}"
  unfolding less_eq_antichain_def
  apply clarsimp
  apply (metis add.commute add_left_mono in_frontier_zmset_image)
  done

lemma frontier_eq_image:
  "frontier M = frontier M' \<Longrightarrow>
   (\<forall> t. zcount M' t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   frontier {#t -+- s. t \<in>#\<^sub>z M#} = frontier {#t -+- s. t \<in>#\<^sub>z M'#}"
  by (auto simp add: ac_eq_iff in_frontier_zmset_image)

lemma ifrontier_le_all_le:
  "dataflow_topology su (-+-) \<Longrightarrow>
   (\<forall> l' t'. t' \<in>\<^sub>A graph.path_weight su l' l \<longrightarrow> frontier (c_pts c l') \<le> frontier (c_pts c' l')) \<Longrightarrow>
   ifrontier su (-+-) c l \<le> ifrontier su (-+-) c' l"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_sum_le)
    apply simp_all
  subgoal
    apply (intro allI)
    apply (rule frontier_sum_le)
      apply simp_all
    subgoal for loc'
      apply (intro ballI)
      subgoal for s
        apply (drule spec[of _ loc'])
        apply (drule mp)
        using set_antichain1 apply blast
        apply (rule frontier_le_image)
          apply simp_all
        done
      done
    done
  subgoal
    by (simp add: sum_nonneg zcount_sum)
  done

lemma ifrontier_eq_all_le:
  "dataflow_topology su (-+-) \<Longrightarrow>
   (\<forall> l' t'. t' \<in>\<^sub>A graph.path_weight su l' l \<longrightarrow> frontier (c_pts c l') = frontier (c_pts c' l')) \<Longrightarrow>
   ifrontier su (-+-) c l = ifrontier su (-+-) c' l"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_sum_eq)
     apply (simp_all add: sum_nonneg zcount_sum)
  apply (metis dataflow_topology_from_tree.elems_eq_sum_eq member_antichain.rep_eq)
  done



definition "cset_from_list = cset_of_llist o llist_of"

lemma cset_from_list_Nil[simp]:
  "cset_from_list [] = {||}"
  unfolding cset_of_llist_def cset_from_list_def
  by (clarsimp simp flip: cin.rep_eq bot_cset_def)
lemma cset_from_list_Cons[simp]:
  "cset_from_list (x # xs) = cinsert x (cset_from_list xs)"
  unfolding cset_from_list_def
  apply (clarsimp simp flip: cin.rep_eq)
  apply (metis cinsert_code)
  done
lemma cset_from_list_append[simp]:
  "cset_from_list (xs @ ys) = cUn (cset_from_list xs) (cset_from_list ys)"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done
lemma cset_from_list_map[simp]:
  "cset_from_list (map f xs) = (f |`| (cset_from_list xs))"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done
lemma cset_from_list_concat[simp]:
  "cset_from_list (concat xs) = cUnion (cset_from_list |`| (cset_from_list xs))"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  apply (meson in_cset_of_llist_llist_of rev_cBexI)
  done
lemma cset_from_list_rmdups[simp]:
  "cset_from_list (rmdups {} xs) = cset_from_list xs"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done
lemma cset_from_list_filter[simp]:
  "cset_from_list (filter p xs) = cfilter p (cset_from_list xs)"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done
lemma rcset_cset_from_list[simp]:
  "rcset (cset_from_list xs) = set xs"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done
lemma in_cset_from_list[simp]:
  "x |\<in>| (cset_from_list xs) \<longleftrightarrow> x \<in> set xs"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done
lemma in_cimage_cset_from_list[simp]:
  "x |\<in>| (f |`| (cset_from_list xs)) \<longleftrightarrow> x \<in> f ` set xs"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done

end