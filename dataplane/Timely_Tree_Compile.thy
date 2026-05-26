theory Timely_Tree_Compile

imports
  Timely_Base
begin

section \<open>Compilation From Dataflow Trees\<close>

text \<open>
  This section connects a compositional dataflow-tree syntax with executable operator and
  graph-level representations used by the progress-tracking control plane.
\<close>


datatype ('id, 'p, 's, 'd, 't) dataflow_tree =
  "apply": Logic "('p option, 'p option, 's + 'd) op" "'p \<Rightarrow> 'p \<Rightarrow> 't list"
  | Comp "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option" "('id, 'p, 's, 'd, 't) dataflow_tree" "('id, 'p, 's, 'd, 't) dataflow_tree"
  | Loop "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option" "('id, 'p, 's, 'd, 't) dataflow_tree"

fun dataflow_tree_to_operator_aux where
  "dataflow_tree_to_operator_aux n chns (Logic op su) = (
    n + 1,
    map_op (case_option (Inl n) (\<lambda> p. Inr (n, p))) (case_option (Inl n) (\<lambda> p. Inr (n, p))) op)"
| "dataflow_tree_to_operator_aux n chns (Comp wire dt1 dt2) = (
    let (n', op1) = dataflow_tree_to_operator_aux n chns dt1 in
    let (n'', op2) = dataflow_tree_to_operator_aux n' chns dt2 in
    (n'', map_op 
     (case_sum id id)
     (case_sum id id)
     (comp_op
      (case_sum (\<lambda> _. None) (\<lambda> (nid, p). case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (Inr (n' + offset, q))))
      ((\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (d, t)) (chns x)))
       op1 op2))
   )"
| "dataflow_tree_to_operator_aux n chns (Loop wire dt) = (
   let (n', op) = dataflow_tree_to_operator_aux n chns dt in
   (n', 
   (loop_op 
    (case_sum (\<lambda> _. None) (\<lambda> (nid, p). case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (Inr (n + offset, q)))) 
    ((\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (d, t)) (chns x)))
    op)))"

definition "dataflow_tree_to_operator chns df = snd (dataflow_tree_to_operator_aux 0 chns df)"

fun dataflow_tree_to_graph_aux where
  "dataflow_tree_to_graph_aux n (Logic op su) =
    (n+ 1, \<lambda> l1 l2. if n = node l1 \<and> n = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) then su (idp (port l1)) (idp (port l2)) else [])"
| "dataflow_tree_to_graph_aux n (Comp wire dt1 dt2) = (
    let (n', summary1) = dataflow_tree_to_graph_aux n dt1 in
    let (n'', summary2) = dataflow_tree_to_graph_aux n' dt2 in
        (n'', \<lambda> l1 l2.
         if node l1 \<ge> n \<and> node l1 < n' \<and> node l2 \<ge> n \<and> node l2 < n' then summary1 l1 l2
         else (if node l1 \<ge> n' \<and> node l2 \<ge> n' then summary2 l1 l2
         else (if node l1 \<ge> n \<and> node l1 < n' \<and> node l2 \<ge> n' \<and> is_Src (port l1) \<and> is_Trg (port l2)
               then (case wire (node l1 - n, idp (port l1)) of
                       None \<Rightarrow> []
                     | Some (offset, q) \<Rightarrow> (if node l2 = n' + offset \<and> q = idp (port l2) then [0] else []))
               else []))
         )
   )"
| "dataflow_tree_to_graph_aux n (Loop wire dt) = (
   let (n', summary) = dataflow_tree_to_graph_aux n dt in
   (n', \<lambda> l1 l2. if node l1 \<ge> n \<and> node l2 \<ge> n
                 then (if is_Src (port l1) \<and> is_Trg (port l2) then
                 (case wire (node l1 - n, idp (port l1)) of
                    None \<Rightarrow> summary l1 l2
                  | Some (offset, q) \<Rightarrow> (if node l2 = n + offset \<and> q = idp (port l2) then trace (STR ''Found loop!'') [0] else []))
                 else summary l1 l2)
                 else Code.abort (STR ''Summary out of bounds'') (\<lambda> _. [])))"

term "trace (STR ''outs: '')"

(* (if node l2 = n' + offset \<and> q = idp (port l2) then trace (STR ''Found loop!'') [0] else [])) *)

fun nodes_count where
  "nodes_count (Logic op su) = (1 :: nat)"
| "nodes_count (Comp wire dt1 dt2) = nodes_count dt1 + nodes_count dt2"
| "nodes_count (Loop wire dt) = nodes_count dt"



fun op_conn where
  "op_conn su (nid, p) (nid', p') = (su (Loc nid (Src p)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A)"

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
  subgoal for x1 df n n'' intsum
    apply (clarsimp simp add: port.case_eq_if split: list.splits if_splits option.splits prod.splits; hypsubst_thin?)
    apply metis
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

lemma dataflow_tree_to_graph_aux_Src_Trg_zero:
  "dataflow_tree_to_graph_aux n dt = (m, su) \<Longrightarrow>
   (su (Loc nid (Src p)) (Loc nid' (Trg p'))) \<noteq> [] \<Longrightarrow>
   x \<in> set (su (Loc nid (Src p)) (Loc nid' (Trg p'))) \<Longrightarrow>
   x = 0"
  apply (induct dt arbitrary: n m su)
   apply (clarsimp simp add:  antichain_from_list_singleton split: list.splits prod.splits if_splits option.splits)
  apply simp
   apply (fastforce simp add: if_distrib  antichain_from_list_singleton split: prod.splits if_splits option.splits)
  apply (simp add: if_distrib  antichain_from_list_singleton split: prod.splits if_splits option.splits)
  unfolding trace_simp
   apply (fastforce simp add: if_distrib  antichain_from_list_singleton split: prod.splits if_splits option.splits)
  done


lemma dataflow_tree_to_graph_Src_Trg_zero:
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

lemma graph_path_weight_Trg_Src:
  assumes G: " Graph.graph (\<lambda>x xa. antichain_from_list (su x xa))"
  shows "(s :: 't :: {ordered_ab_semigroup_monoid_add_imp_le}) \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) (Loc nid (Trg p)) l \<Longrightarrow>
   l \<noteq> Loc nid (Trg p) \<Longrightarrow>
   (m, su) = dataflow_tree_to_graph_aux n dt \<Longrightarrow>
    \<exists>t p'.
       t \<in> set (su (Loc nid (Trg p)) (Loc nid (Src p'))) \<and>
       (\<exists>s'. s' \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) (Loc nid (Src p')) l \<and> s = t + s') "
  apply (drule path_weight_Trg_decompose[OF G])
     apply simp_all
  apply (metis antichain_from_list_empty_antichain dataflow_tree_to_graph_aux_no_inp_and_out_connection
      dataflow_tree_to_graph_aux_no_inp_to_other_operator_connection)
  apply (metis antichain_from_list_empty_antichain
      dataflow_tree_to_graph_aux_no_inp_to_other_operator_connection)
  apply clarsimp
  using in_antichain_from_listD apply blast
  done

lemma dataflow_tree_to_graph_aux_no_out_to_inp_connection:
  "dataflow_tree_to_graph_aux n dt = (m, su) \<Longrightarrow>
   su (Loc nid (Src p)) (Loc nid' (Src p')) = []"
  apply (induct dt arbitrary: n m su)
   apply (auto simp add: if_distrib split: if_splits prod.splits list.splits option.splits)
  done

global_interpretation dataflow_topology_from_tree: enum_dataflow_topology "antichain_from_list oo (dataflow_tree_to_graph (df :: (_, _, _, _, 't :: {bot,ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}) dataflow_tree))" "(+)"
  for df
  defines take_step' = "enum_dataflow_topology.take_step (antichain_from_list oo (dataflow_tree_to_graph df)) (+)"
    and after_summary = "dataflow_topology.after_summary (+) :: 't zmultiset \<Rightarrow> 't antichain \<Rightarrow> 't zmultiset"
  by simp

text \<open>
  Path-weight decomposition for compiled tree graphs: any non-trivial path starting from
  a target port must first pass through a source port of the same node.
\<close>
lemma dataflow_tree_to_graph_Trg_decompose:
  "(s :: _ :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) (Loc nid (Trg p)) l \<Longrightarrow>
   l \<noteq> Loc (nid :: _ :: {enum,minus,one,plus,zero,hashable,linorder}) (Trg (p :: _ :: {enum,hashable,linorder})) \<Longrightarrow>
   su = dataflow_tree_to_graph dt \<Longrightarrow>
    \<exists>t p'.
       t \<in> set (su (Loc nid (Trg p)) (Loc nid (Src p'))) \<and>
       (\<exists>s'. s' \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) (Loc nid (Src p')) l \<and> s = t + s') "
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

notation dataflow_topology_from_tree.followed_by (infixl \<open>-+-\<close> 65)
notation dataflow_topology_from_tree.after_summary (infixl \<open>+++\<close> 65)

abbreviation AF where
  "AF \<equiv> dataflow_topology.after_summary (-+-)"

notation "AF" (infixl \<open>-++-\<close> 65)



end
