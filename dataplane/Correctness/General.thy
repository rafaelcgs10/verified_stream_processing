theory General

imports
  Dataplane.Timely_Stream
  Dataplane.Timely_Infrastructure
begin

declare cin.rep_eq[simp del]
declare enum_class.enum_UNIV[simp] enum_class.enum_distinct[simp]


(* FIXME: move me *)
lemma is_empty_antichain_iff:
  "is_empty_antichain A \<longleftrightarrow> A = {}\<^sub>A"
  by (metis Timely_Infrastructure.is_empty_antichain_plus antichain_sum_empty_2 empty_antichain.abs_eq empty_is_empty_antichain)

definition "c_pts_inv c caps = (\<forall> l. c_pts c l = caps l)"
definition "Src_caps_inv caps os = (\<forall> nid p. caps (Loc nid (Src p)) = to_zmset (ocaps (os nid) p))"
definition "Trg_caps_inv caps bufs = (\<forall> nid p. caps (Loc nid (Trg p)) = to_zmset (map snd (bufs (nid, p))))"
definition "extract_prog xs eds os = concat (map (\<lambda> nid. extract_progress nid eds (snd (obtain_progress (os nid)))) xs)"
definition "front_inv os c = (\<forall> nid p. front (os nid) p \<le> frontier (c_imp c (Loc nid (Trg p))))"
definition "imp_front_inv su c = (\<forall> l. frontier (c_imp c l) \<le> ifrontier su (+) c l)"
definition "chnls_imp_front_inv su c chns = (\<forall> nid p. \<forall> t \<in> snd ` set (chns (nid, p)). frontier_less_equal (ifrontier su (+) c (Loc nid (Trg p))) t)"


definition "propagation_inv su c = 
  (dataflow_topology.inv_imps_work_sum su (-+-) c \<and>
   dataflow_topology.inv_implications_nonneg c \<and>
   dataflow_topology.inv_imp_plus_work_nonneg c)"

definition "change_deltas_inv os = (\<forall> nid p t d. ((p, t, d) \<in> set (consu (os nid)) \<union> set (produ (os nid)) \<longrightarrow> d > 0) \<and> ((p, t, d) \<in> set (inter (os nid)) \<longrightarrow> d \<noteq> 0))"
definition "changes_above_impl_inv su c cgs = 
  ((\<forall>(l, t, d)\<in>set cgs. frontier_less_equal (ifrontier su (+) c l) t))"

lemma changes_above_impl_inv_empty[simp]:
  "changes_above_impl_inv su c []"
  unfolding changes_above_impl_inv_def by auto

definition "extract_progress_inv su ed os c = 
 (\<forall> nid nid'.
   nid \<noteq> nid' \<longrightarrow>
   (\<forall>(l, t, m)\<in>set (extract_progress nid ed ((snd o obtain_progress) (os nid))).
   frontier_less_equal (ifrontier su (+) (change_multiplicities su (extract_progress nid' ed ((snd o obtain_progress) (os nid'))) c) l) t))"


definition "outputs_at_target su os = (\<lambda> (nid, p). let S = {(nid', p'). op_conn su (nid', p') (nid, p)} in if S = {} then [] else let (nid', p') = Set.the_elem S in outpu (os nid') p')"

definition "inputs_at_target os = (\<lambda> (nid, p). input (os nid) p)"

lemma outputs_at_target_consumes[simp]:
  "outputs_at_target su (os(nid := consumes (os nid) p' t d)) = outputs_at_target su os"
  unfolding outputs_at_target_def consumes_def  add_caps_def
  apply (rule ext)+
  apply (auto split: if_splits prod.splits)
  done

lemma outputs_at_target_obtain_progress[simp]:
  "outputs_at_target su (os(nid := fst (obtain_progress (os nid)))) = outputs_at_target su os"
  unfolding outputs_at_target_def consumes_def add_caps_def
  apply (rule ext)+
  apply (auto split: if_splits prod.splits)
  done

lemma inputs_at_target_obtain_progress[simp]:
  "inputs_at_target (os(nid := fst (obtain_progress (os nid)))) = inputs_at_target os"
  unfolding inputs_at_target_def obtain_progress_def
  apply (rule ext)+
  apply (auto split: if_splits prod.splits)
  done
lemma inputs_at_target_consumes[simp]:
  "inputs_at_target (os(nid := consumes (os nid) p t d)) = BENQ (nid, p) (d, t) (inputs_at_target os)"
  unfolding inputs_at_target_def consumes_def add_caps_def BENQ_def
  by (auto split: if_splits)

definition "ty1_check os bufs = (\<forall> p. (\<forall> x \<in> fst ` set (input os p) \<union> fst ` set (bufs p) \<union> fst ` set (outpu os p). is_en1 os x))"
definition "ty2_check os bufs = (\<forall> p. (\<forall> x \<in> fst ` set (input os p) \<union> fst ` set (bufs p). is_en1 os x) \<and> (\<forall> x \<in> fst ` set (outpu os p). is_en2 os x))"

find_consts  name: index name: find

term index

definition "produ_consu_inter_supported nt os c =
    ((\<forall> nid p t m. (p, t, m) \<in> set (produ (os nid)) \<longrightarrow> (zcount (c_pts c (Loc nid (Src p))) t > 0 \<or> (\<exists>m'>0. (p, t, m') \<in> set (inter (os nid))))) \<and>
     (\<forall> nid p t m. (p, t, m) \<in> set (consu (os nid)) \<longrightarrow>
                   (zcount (c_pts c (Loc nid (Trg p)) + zmset (concat (map (\<lambda> (nid', p'). (map snd (filter (\<lambda> (p'', _, _). nt (nid', p'') = Some (nid, p) \<and> p' = p'') (produ (os nid'))))) Enum.enum))) t > 0)) \<and>
     (\<forall> nid p t m. (p, t, m) \<in> set (inter (os nid)) \<longrightarrow> 
                   ((\<exists> t'\<le>t. zcount (c_pts c (Loc nid (Src p))) t' > 0) \<or>
     (\<exists> t' p' s. \<exists>m'>0. (p', t', m') \<in> set (consu (os nid)) \<and> s \<in> set (intsum (os nid) p' p ) \<and> t \<ge> t' -+- s))))"

definition "extract_prog_changes_above_impl_inv su nt c os =
   (\<forall> nid xs. distinct xs \<longrightarrow> nid \<notin> set xs \<longrightarrow> 
     changes_above_impl_inv su (change_multiplicities su (extract_prog xs nt os) c)
     (extract_progress nid nt (snd (obtain_progress (os nid)))))"

definition "dataplane_tracker_inv os cbufs sg = 
   (\<exists> c c' cgs chns caps.
     c = pt_tr sg \<and>
     cgs = extract_prog Enum.enum (nxt sg) os \<and>
     chns = outputs_at_target (summ sg) os >> cbufs \<and>
     Src_caps_inv caps os \<and>
     Trg_caps_inv caps chns \<and>
     c' = change_multiplicities (summ sg) cgs c \<and>
     c_pts_inv c' caps \<and>
     front_inv os c \<and>
     imp_front_inv (summ sg) c \<and>
     chnls_imp_front_inv (summ sg) c chns \<and>
     change_deltas_inv os \<and>
     propagation_inv (summ sg) c \<and>
     extract_prog_changes_above_impl_inv (summ sg) (nxt sg) c os  \<and>
     (produ_consu_inter_supported (nxt sg) os c))"


definition "graph_summar_nt su nt os = (
  (\<forall> nid p p' t. t \<in> set (intsum (os nid) p p') \<longrightarrow> (\<exists> t'\<le>t. t' \<in>\<^sub>A graph.path_weight su (Loc nid (Trg p)) (Loc nid (Src p')))) \<and>
  (\<forall> nid nid' p p'. nt (nid', p') = Some (nid, p) \<longrightarrow> 0 \<in>\<^sub>A su (Loc nid' (Src p')) (Loc nid (Trg p))) \<and>
  (\<forall> nid p p'. distinct (intsum (os nid) p p')) \<and>
  (\<forall> nid p p'. \<forall> t \<in> set (intsum (os nid) p p'). \<not> (\<exists> t' \<in> set (intsum (os nid) p p'). t' < t)) \<and>
  (\<forall> s nid p l. 
      s \<in>\<^sub>A graph.path_weight su (Loc nid (Trg p)) l \<longrightarrow>
      l \<noteq> Loc nid (Trg p) \<longrightarrow> (\<exists> t p' s'. t \<in> set (intsum (os nid) p p') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p')) l \<and> s = t -+- s')) \<and>
   inj_on nt (Map.dom nt) \<and>
   bi_unique (op_conn su) \<and>
   (\<forall> nid nid' p p'. su (Loc nid (Trg p)) (Loc nid' (Trg p')) = {}\<^sub>A) \<and>
   (\<forall> nid nid' p p' t. t \<in>\<^sub>A su (Loc nid (Trg p)) (Loc nid' (Src p')) \<longrightarrow> nid' = nid \<and> t \<in> set (intsum (os nid) p p')) \<and>
   (\<forall> nid nid' p p'. su (Loc nid (Src p)) (Loc nid' (Src p')) = {}\<^sub>A)
  )"


lemma path_weight_direct_0path:
  assumes G: "Graph.graph su"
  shows "(0 :: 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A su l1 l2 \<Longrightarrow>
   0 \<in>\<^sub>A graph.path_weight su l1 l2"
  apply (subst graph.path_weight_def[OF G])
  apply clarsimp
  apply (subst member_antichain.abs_eq)
  apply (clarsimp simp add: eq_onp_def)
  apply (rule graph.finite_minimal_antichain_path_weightp[OF G])
  unfolding minimal_antichain_def
  apply clarsimp
  apply (subst graph.path_weightp_def[OF G])
  apply clarsimp
  apply (rule exI[of _ "[(l1, 0, l2)]"])
  apply clarsimp
  apply (rule graph.path.intros(2)[where xs=Nil, simplified, OF G])
  apply (rule graph.path.intros(1)[OF G])
  apply auto
  done

lemma in_antichain_singleton[simp]:
  "x \<in>\<^sub>A antichain {x}"
  by (metis ID.set_finite in_antichain_minimal_antichain insertI1 minimal_antichain_singleton)


lemma find_SomeD':
  "find P xs = Some x \<Longrightarrow> P x \<and> x\<in>set xs"
  by (auto dest: find_SomeD)
lemma find_SomeD'':
  "Some x = find P xs \<Longrightarrow> P x \<and> x\<in>set xs"
  using find_SomeD' by metis

lemma single_valued_inv_to_nxt_inj_on:
  "bi_unique (op_conn su) \<Longrightarrow>
   inj_on (graph_to_nxt su) (dom (graph_to_nxt su))"
  unfolding graph_to_nxt_def inj_on_def 
  apply (clarsimp simp add: enum_class.enum_UNIV is_empty_antichain_iff dest!: find_SomeD' split: prod.splits)
  subgoal for aa ba x1 x2 ac bc x1a x2a
    apply (cases "find (\<lambda>(nid', p'). su (Loc x1 (Src x2)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A) enum_class.enum")
    subgoal
      by (auto simp add: enum_class.enum_UNIV is_empty_antichain_iff find_None_iff2 dest!: find_SomeD' split: prod.splits)
    subgoal for a
      apply (cases "find (\<lambda>(nid', p'). su (Loc x1a (Src x2a)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A) enum_class.enum")
      apply (auto simp add: bi_unique_def enum_class.enum_UNIV is_empty_antichain_iff dest!: find_SomeD' find_SomeD'' split: prod.splits)
      done
    done
  done

lemma graph_summar_nt:
  assumes
    \<open>raw_s = dataflow_tree_to_graph (dt :: ('a :: {enum,minus,one,plus,zero,hashable,linorder}, 'b :: {enum,hashable,linorder}, 'c, 'd, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) dataflow_tree)\<close>
    \<open>summ sg = antichain_from_list oo raw_s\<close>
    \<open>\<forall> n. intsum (os n) = (\<lambda> p1 p2. raw_s (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    \<open>nxt sg = graph_to_nxt (summ sg)\<close>
  shows \<open>graph_summar_nt (summ sg) (nxt sg) os\<close>
  using assms apply -
  apply simp
  unfolding graph_summar_nt_def
  apply (intro conjI allI impI)
  apply simp_all
  subgoal for nid p p' t
    unfolding comp_def
    apply (rule summary_in_path_weight)
    subgoal
      by standard
    apply assumption
    subgoal
      unfolding dataflow_tree_to_graph_def
      apply (simp split: if_splits prod.splits)
      done
    done
  subgoal premises prems for nid nid' p p'
    using prems(5) apply -
    unfolding graph_to_nxt_def
    apply (auto 0 0 simp add: comp_def dest!: find_SomeD(1)  split: if_splits prod.splits)
    apply (drule dataflow_tree_to_graph_Src_Trg_zero[OF prems(2)[symmetric], unfolded prems(2) comp_def, simplified, of _ _ nid p])
    apply simp
    done
  subgoal
    unfolding dataflow_tree_to_graph_def
    apply (simp split: if_splits prod.splits)
    done
  subgoal
    unfolding dataflow_tree_to_graph_def
    apply (clarsimp simp add:  incomparable_def split: if_splits prod.splits)
    apply fast
    done
  subgoal for s nid p l
    unfolding comp_def
    using dataflow_tree_to_graph_Trg_decompose 
    by blast
  subgoal premises prems
    apply (rule single_valued_inv_to_nxt_inj_on)
    apply (auto simp add: comp_def dataflow_tree_to_graph_def  split: if_splits prod.splits)
    unfolding bi_unique_def
    apply auto
    done
  subgoal premises prems
    apply (auto simp add: comp_def dataflow_tree_to_graph_def split: if_splits prod.splits)
    unfolding bi_unique_def
    apply auto
    done
  subgoal for nid nid' p p'
    unfolding dataflow_tree_to_graph_def
    apply (simp split: if_splits prod.splits)
    subgoal premises prems for rs x2
      apply (cases "nid = nid'")
      subgoal
        using dataflow_tree_to_graph_aux_no_inp_and_out_connection[OF prems(3)]
        by (simp add: comp_def)
      subgoal
        using dataflow_tree_to_graph_aux_no_inp_to_other_operator_connection[OF prems(3)]
        by fastforce
      done
    subgoal premises prems
      using prems
      by blast
    done
  subgoal for nid nid' p p' t
    unfolding dataflow_tree_to_graph_def
    apply (simp split: if_splits prod.splits)
    using dataflow_tree_to_graph_aux_no_inp_to_other_operator_connection
    apply (metis in_antichain_from_listD in_set_simps(3))
    done
  subgoal for nid nid' p p'
    unfolding dataflow_tree_to_graph_def
    apply (simp split: if_splits prod.splits)
    using dataflow_tree_to_graph_aux_no_inp_to_other_operator_connection
    apply (metis in_antichain_from_listD in_set_simps(3))
    done
  subgoal
    unfolding dataflow_tree_to_graph_def
    apply (simp split: if_splits prod.splits)
    using dataflow_tree_to_graph_aux_no_out_to_inp_connection
    apply (metis antichain_from_list_empty_antichain)+
    done
  done


(* ======> FIXME: move me \<le>====== *)
lemma sum_eq_singleton:
  "finite A \<Longrightarrow> f a = b \<Longrightarrow> a \<in> A \<Longrightarrow> (\<forall> c \<in> A. c \<noteq> a \<longrightarrow> f c = 0) \<Longrightarrow> sum f A = b"
  by (metis Diff_iff dataflow_topology_from_tree.sum_singleton empty_subsetI insert_iff insert_subset sum.mono_neutral_right)
lemma zcount_zmset_gt_0_set_Ex:
  "0 < zcount (zmset xs) x \<Longrightarrow> \<exists> m. (x, m) \<in> set xs \<and> m > 0"
  apply (induct xs)
  apply clarsimp+
  apply (smt (verit, ccfv_SIG) zcount_update_zmultiset)
  done
lemma count_list_gt_0[simp]:
  "0 < count_list xs x \<longleftrightarrow> x \<in> set xs"
  by (induct xs) auto
lemma zcount_zimageD:
  "zcount {#f t. t \<in>#\<^sub>z A#} t > 0 \<Longrightarrow>
   (\<exists> t'. zcount A t' > 0 \<and> t = f t')"
  apply transfer
  apply clarsimp
  apply (metis count_image_mset_lt_imp_lt)
  done
lemma zcount_to_zmset_gt_0[simp]:
  "zcount (to_zmset xs) t > 0 \<longleftrightarrow> t \<in> set xs"
  by (induct xs) (simp_all add: to_zmset_nenneg)
lemma sum_le_0I:
  "finite A \<Longrightarrow> (\<forall> x\<in>A. f x \<le> (0 :: int)) \<Longrightarrow> (\<Sum>x\<in>A. f x)\<le> 0"
  apply (induct A rule: finite_induct)
  apply simp_all
  done
lemma in_frontier_minusD:
  "x \<in>\<^sub>A frontier (A - B) \<Longrightarrow> 
   (\<forall> y. zcount B y \<ge> 0) \<Longrightarrow>
   (\<exists> y. y \<in>\<^sub>A frontier A \<and> y \<le> x)"
  using frontier_below_eq_frontier_minus less_eq_antichain_def by blast
lemma in_frontier_minus_altD:
  "x \<in>\<^sub>A frontier (A + B) \<Longrightarrow> 
   (\<forall> y. zcount B y \<le> 0) \<Longrightarrow>
   (\<exists> y. y \<in>\<^sub>A frontier A \<and> y \<le> x)"
  using frontier_below_eq_frontier_minus less_eq_antichain_def
  using frontier_below_eq_frontier_plus_neg by blast

lemma in_frontier_minusI:
  "t \<in>\<^sub>A frontier A \<Longrightarrow>
   t \<noteq> t' \<Longrightarrow>
   t \<in>\<^sub>A frontier (A - {#t'#}\<^sub>z)"
  apply transfer'
  unfolding minimal_antichain_def
  apply auto
  done
lemma in_frotier_sum_le_exI:
  "finite A \<Longrightarrow>
   (\<forall> a\<in>A. \<forall> t. zcount (f a) t \<ge> 0)\<Longrightarrow>
   t' \<in>\<^sub>A frontier (f a) \<Longrightarrow>
   a \<in> A \<Longrightarrow>
   t' \<le> t \<Longrightarrow>
   \<exists> t'. t' \<in>\<^sub>A frontier (sum f A) \<and> t' \<le> t"
  apply (induct A rule: finite_induct)
  apply simp_all
  apply clarsimp
  apply (elim disjE)
  subgoal
    using fronteier_lt_add_ex
    by (metis (lifting) sum_nonneg zcount_sum)
  subgoal
    by (metis Groups.add_ac(2) fronteier_lt_add_ex)
  done
lemma sum_subtractf_zmultiset:
  "finite A \<Longrightarrow>
   (\<Sum>x\<in>A. f x - g x) = sum (f :: 'b \<Rightarrow> 'a zmultiset) A - sum g A"
  apply (induct A rule: finite_induct)
  apply simp_all
  apply (metis (no_types, lifting) add_diff_eq diff_add_zmset uminus_add_add_uminus)
  done
lemma int_sum_minus_cases:
  "(0 :: int) < V \<Longrightarrow> V = n + m - p \<Longrightarrow> 0 \<le> p \<Longrightarrow> 0 < n \<or> 0 < m"
  by auto
lemma sum_list_pos_ex_elem_pos: "(0::int) < (\<Sum>m\<leftarrow>M. f m) \<Longrightarrow> \<exists>m\<in>set M. 0 < f m"
  by (smt (verit, ccfv_threshold) sum_list_0 sum_list_mono)
lemma zcount_zmset:
  "zcount (zmset xs) t = sum_list (map snd (filter (\<lambda> (t', x). t = t') xs))"
  by (induct xs) (auto simp add: zcount_update_zmultiset)
lemma sum_gt_0I:
  "xs \<noteq> [] \<Longrightarrow>
   (\<forall> x \<in> set xs. 0 < x) \<Longrightarrow>
   (0 :: int) < sum_list xs"
  apply (induct xs)
  apply auto
  subgoal for a xs
    apply (cases xs)
    apply auto
    done
  done      

lemma extract_prog_obtain_progress_remove1:
  "distinct xs \<Longrightarrow>
   extract_prog xs su (os(nid := fst (obtain_progress (os nid)))) =
   extract_prog (remove1 nid xs) su os"
  unfolding extract_prog_def
  apply simp
  apply (induct xs)
  apply simp
  subgoal for nid' xs
    apply clarsimp
    apply hypsubst_thin
    apply (drule sym)
    apply simp
    subgoal premises prems
      using prems(1) apply -
      apply (induct xs)
      apply auto
      done
    done
  done

lemma change_multiplicities_extract_prog_obtain_progress_remove1_append:
  "distinct xs \<Longrightarrow>
   nid \<in> set xs \<Longrightarrow>
   change_multiplicities su (extract_prog xs nt os) =
   change_multiplicities su (extract_progress nid nt (snd (obtain_progress (os nid))) @ extract_prog (remove1 nid xs) nt os)"
  apply (rule ext)
  subgoal for c
    apply (induct xs arbitrary: c)
    apply (clarsimp simp add: extract_prog_def)+
    apply (metis (no_types, lifting) change_multiplicities_append_alt change_multiplicities_comm)
    done
  done


(* FIXME: move me *)
lemma cUnion_cUn_distrib[simp]:
  "cUnion (cUn A B) = cUn (cUnion A) (cUnion B)"
  apply transfer
  apply (auto simp add:  cin.rep_eq)
  done



lemma frontier_zmset_of_remove1_mset[simp]:
  "frontier (zmset_of (remove1_mset t C)) = frontier (zmset_of C - {# t #}\<^sub>z)"
  apply transfer'
  unfolding minimal_antichain_def
  apply auto
  done

lemma time_monotone_frontier_less_equal:
  "x \<in> lset inps \<Longrightarrow>
   timely_monotone inps C \<Longrightarrow>
   is_Data x \<Longrightarrow>
   frontier_less_equal (frontier (zmset_of C)) (event.time x)"
  unfolding  frontier_less_equal_iff2
  apply (cases x; clarsimp; hypsubst_thin?)
  subgoal for t d
    apply (induct inps arbitrary: C rule: lset_induct)
    subgoal
      apply (erule timely_monotone.cases)
      apply clarsimp+
      apply (meson mem_zmset_of zcount_gt_0_in_frontierD zcount_zmset_of_nonneg zmset_elem_nonneg)
      done
    subgoal for x' xs C
      apply (erule timely_monotone.cases; clarsimp; hypsubst_thin?)
      subgoal for t'
        apply (drule meta_spec)
        apply (drule meta_mp)
        apply assumption
        apply clarsimp
        using in_frontier_minusD apply fastforce
        done
      subgoal for t' t''
        apply (drule meta_spec)
        apply (drule meta_mp)
        apply assumption
        apply clarsimp
        apply (smt (verit, del_insts) in_frontier_iff mem_zmset_of order_trans_rules(23) trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_add_zmset zcount_ne_zero_iff zcount_zmset_of_nonneg)
        done
      done
    done
  done

lemma timely_input_stream_frontier_less_equal:
  "timely_input_stream inps C \<Longrightarrow>
   (\<forall> x. x \<in> lset inps \<longrightarrow> is_Data x \<longrightarrow> frontier_less_equal (frontier (zmset_of C)) (event.time x))"
  unfolding timely_input_stream_def
  using time_monotone_frontier_less_equal by blast



lemma extract_prog_append[simp]:
  "extract_prog (xs @ ys) nt os = extract_prog xs nt os @ extract_prog ys nt os"
  unfolding extract_prog_def by auto
lemma extract_prog_Cons[simp]:
  "extract_prog (x#xs) nt os = extract_progress x nt (snd (obtain_progress (os x))) @ extract_prog xs nt os"
  unfolding extract_prog_def by auto
lemma extract_prog_skip_update[simp]:
  "nid \<notin> set xs \<Longrightarrow>
   extract_prog xs nt (os(nid := A)) = extract_prog xs nt os"
  unfolding extract_prog_def
  apply (induct xs)
  apply auto
  done
lemma extract_prog_empty[simp]:
  "extract_prog [] nt os = []"
  unfolding extract_prog_def by auto


lemma frontier_less_equal_ifrontier_from_Src:
  assumes D: "dataflow_topology su (-+-)"
  shows  "frontier_less_equal
     (frontier (c_pts (change_multiplicities su (extract_progress nid nt (snd (obtain_progress (os nid)))) c) (Loc nid (Src p)))) t \<Longrightarrow>
   s \<in>\<^sub>A graph.path_weight su (Loc nid (Src p)) l \<Longrightarrow>
   extract_prog_changes_above_impl_inv su nt c os \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) (t -+- s)"
  apply (subst (asm) frontier_less_equal_iff2)
  apply clarsimp
  subgoal for t'
    apply (simp add: c_pts_change_multiplicities)
    apply (drule in_frontier_addD)
    apply (elim disjE exE)
    subgoal
      apply clarsimp
      apply (rule frontier_less_equal_ifrontierI[OF D, of s "Loc nid (Src p)", simplified])
      apply assumption
      unfolding frontier_less_equal_iff2
      subgoal for t''
        apply (rule exI[of _ t''])
        apply auto
        done
      done
    subgoal
      apply clarsimp
      apply (subst (asm) obtain_progress_def)
      apply (subst (asm) extract_progress_def)
      apply (clarsimp simp add: filter_map split_beta comp_def List.map_filter_def split: option.splits)
      unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def
      apply (drule spec[of _ nid])
      apply (drule spec[of _ "[]"])
      apply simp
      apply (drule zcount_zmset_gt_0_set_Ex)
      apply clarsimp
      subgoal for t'' m
        apply (drule bspec[of _ _ "(Loc nid (Src p), t', m)"])
        subgoal
          unfolding extract_progress_def obtain_progress_def
          by (fastforce simp add: Misc.set_map_filter image_iff split_beta split: option.splits)
        subgoal
          apply simp
          apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
          apply assumption+
          apply auto
          done
        done
      done
    done
  done


lemma frontier_less_equal_ifrontier_from_Trg:
  assumes D: "dataflow_topology su (-+-)"
  shows  "frontier_less_equal
     (frontier (c_pts (change_multiplicities su (extract_progress nid nt (snd (obtain_progress (os nid)))) c) (Loc nid (Trg p)))) t \<Longrightarrow>
   s \<in>\<^sub>A graph.path_weight su (Loc nid (Trg p)) l \<Longrightarrow>
   extract_prog_changes_above_impl_inv su nt c os \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) (t -+- s)"
  apply (subst (asm) frontier_less_equal_iff2)
  apply clarsimp
  subgoal for t'
    apply (simp add: c_pts_change_multiplicities)
    apply (drule in_frontier_addD)
    apply (elim disjE exE)
    subgoal
      apply clarsimp
      apply (rule frontier_less_equal_ifrontierI[OF D, of s "Loc nid (Trg p)", simplified])
      apply assumption
      unfolding frontier_less_equal_iff2
      subgoal for t''
        apply (rule exI[of _ t''])
        apply auto
        done
      done
    subgoal
      apply clarsimp
      apply (subst (asm) obtain_progress_def)
      apply (subst (asm) extract_progress_def)
      apply (drule zcount_zmset_gt_0_set_Ex)
      apply (clarsimp simp add: image_iff filter_map split_beta comp_def List.map_filter_def split: option.splits)
      unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def
      apply (drule spec[of _ nid])
      apply (drule spec[of _ "[]"])
      apply simp
      apply clarsimp
      subgoal for t'' m
        apply (drule bspec[of _ _ "(Loc nid (Trg p), t', m)"])
        subgoal
          unfolding extract_progress_def obtain_progress_def
          by (fastforce simp add: Misc.set_map_filter image_iff split_beta split: option.splits)
        subgoal
          apply simp
          apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
          apply assumption+
          apply auto
          done
        done
      done
    done
  done

(* FIXME: move me *)
lemma to_zmset_concat:
  "to_zmset (concat xs) = sum_list (map to_zmset xs)"
  by (induct xs) auto
lemma distinct_rmdups[simp]:
  "distinct (rmdups A xs)"
  by (induct xs arbitrary: A) auto
lemma image_zmset_comp:
  "image_zmset f (image_zmset g M) = image_zmset (f o g) M"
  apply transfer
  apply (auto simp add: equiv_zmset_def)
  done
lemma zcount_image_zmset_image_zmset[simp]:
  "zcount (Auxiliary.image_zmset f (Auxiliary.image_zmset g (M t))) t = zcount {#f (g xa). xa \<in>#\<^sub>z M t#} t"
  apply transfer
  apply (auto simp add: split_beta)
  done
lemma image_zmset_sum_image_zmset:
  "finite S \<Longrightarrow>
  {#f x . x \<in>#\<^sub>z \<Sum>x\<in> S. {#g xa x. xa \<in>#\<^sub>z M x#}#} = (\<Sum>x\<in> S. {#f (g xa x). xa \<in>#\<^sub>z M x#})"
  unfolding comp_def
  apply (induct S  rule: finite_induct)
  apply simp
  subgoal for t S
    unfolding zmultiset_eq_iff
    apply (auto simp add: equiv_zmset_def split_beta zcount_sum)
    subgoal premises for t'
      apply transfer
      apply (auto simp add: split_beta)
      done
    done
  done


lemma zmset_map_filter_Trg_extract_prog:
  "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog Enum.enum (nxt sg) os))) = 
   (\<Sum>x\<in>UNIV. zmset (List.map_filter (\<lambda> (p', t, d). case_option None (\<lambda> (nid'', p''). if nid'' = nid \<and> p'' = p then Some (t, d) else None) (nxt sg (x, p'))) (produ (os x))))
     - zmset (map snd (filter (((=) (p :: 'p :: enum)) o fst) (consu (os nid)))) "
  unfolding extract_prog_def extract_progress_def obtain_progress_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits if_splits option.splits)
  apply (subst (1) monoid_add_class.sum_list_distinct_conv_sum_set)
  apply (clarsimp simp add: sum_subtractf uminus_add_conv_diff_mset split_beta filter_map map_filter_def comp_def sum_diff comm_monoid_add_class.sum.distrib enum_class.enum_distinct enum_class.enum_UNIV split: prod.splits if_splits option.splits)+
  apply (subst sum_subtractf_zmultiset)
  apply simp_all
  apply (rule arg_cong2[where f="(-)"])
  apply simp_all
  apply (rule sum.cong)
  apply simp_all
  subgoal for pp
    apply (rule arg_cong[where f="zmset"])
    apply (rule map_cong)
    apply (rule filter_cong)
    apply auto
    done
  done

lemma filter_loc_Trg_extract_prof_consumes_diff_nids[simp]:
  "nid \<noteq> nid' \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum (edges sg) (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum (edges sg) os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
  apply auto
  done

lemma filter_loc_extract_prof_consumes_diff_ports[simp]:
  "p \<noteq> p' \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum (edges sg) (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum (edges sg) os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
  apply auto
  done

lemma zmset_map_filter_Src_extract_prog[simp]:
  "distinct xs \<Longrightarrow>
   nid \<in> set xs \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p) = l') (extract_prog xs (edges sg) os))) = 
   zmset (map snd (filter (((=) (p :: 'p :: enum)) o fst) (inter (os nid)))) "
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (subst conj.commute)
  apply (simp add: List.map_filter_def sum.distrib sum_list_distinct_conv_sum_set flip: filter_filter split: option.splits)+
  done

lemma set_extract_prog_consumesD:
  "(l, t', m) \<in> set (extract_prog Enum.enum (edges sg) (os(nid := consumes (os nid) p t d))) \<Longrightarrow>
   (l, t', m) \<in> set (extract_prog Enum.enum (edges sg) os) \<or>
   (l = Loc nid (Trg p) \<and> t = t' \<and> m = -1) \<or>
   (\<exists> p' t''. t'' \<in> set (intsum (os nid) p p') \<and> l = Loc nid (Src p') \<and> t' = t + t'' \<and> m = 1)"
  unfolding extract_prog_def obtain_progress_def consumes_def extract_progress_def add_caps_def
  apply (auto del: disjCI simp add: List.map_filter_def image_iff split_beta if_distrib split: option.splits prod.splits if_splits)
  apply fastforce
  apply fastforce
  apply (metis Pair_inject the_default.simps(1))
  apply fastforce
  apply fastforce
  apply (metis Pair_inject the_default.simps(1))
  done

lemma data_in_channel_justifies_c_pts:
  "Trg_caps_inv caps chnls \<Longrightarrow>
   c_pts_inv (change_multiplicities su (extract_prog Enum.enum ed os) c) caps \<Longrightarrow> 
   t \<in> snd ` set (chnls (nid, p)) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (produ (os n)). m \<ge> 0) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (consu (os n)). m \<ge> 0) \<Longrightarrow>
   zcount (c_pts c (Loc nid (Trg p))) t > 0 \<or> (\<exists> nid' p'. zcount (zmset (map snd ((filter ((=) p' o fst)) (produ (os nid'))))) t > 0 \<and> (ed (nid', p') = Some (nid, p)))"
  unfolding Trg_caps_inv_def
  apply (drule spec[of _ nid])
  apply (drule spec[of _ p])
  unfolding c_pts_inv_def
  apply (drule spec[of _ "Loc nid (Trg p)"])
  apply (simp add: c_pts_change_multiplicities)
  subgoal premises prems3
    using prems3(1,5) apply -
    unfolding extract_prog_def obtain_progress_def extract_progress_def
    apply (simp add:  BULK_BENQ_def zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
    apply (subst (asm) (1) monoid_add_class.sum_list_distinct_conv_sum_set)
    apply (simp_all add: enum_distinct enum_UNIV)
    apply (subst (asm) Groups.ab_group_add_class.ab_diff_conv_add_uminus)
    apply (subst (asm) comm_monoid_add_class.sum.distrib)
    apply (simp add: zmultiset_eq_iff)
    apply (drule spec[of _ t])+
    apply (simp add: zcount_sum)
    apply (subgoal_tac "zcount (to_zmset (map snd (chnls (nid, p)))) t > 0")
    subgoal
      apply (drule sym)
      apply simp
      apply (drule int_sum_minus_cases[where n="zcount (c_pts c (Loc nid (Trg p))) t" and
            m="(\<Sum>x\<in>UNIV. zcount (zmset (List.map_filter (\<lambda> (p', t, d). case_option None (\<lambda> (nid'', p''). if nid'' = nid \<and> p'' = p then Some (t, d) else None) (ed (x, p'))) (produ (os x)))) t)" and p="zcount (zmset (map snd (filter (\<lambda>x. p = fst x) (consu (os nid))))) t"])
      subgoal
        apply (clarsimp simp add: map_concat filter_concat filter_map comp_def List.map_filter_def split_beta split: if_splits prod.splits option.splits)
        apply (rule sum.cong)
        apply simp_all
        apply (rule arg_cong2[where f=zcount])
        apply simp_all
        apply (rule arg_cong[where f=zmset])
        apply (rule map_cong)
        apply simp_all
        apply (rule filter_cong)
        apply auto
        done
      apply (rule zcount_zmset_ge_0I)
      apply simp
      using prems3(3) apply blast
      apply (elim disjE)
      apply simp
      apply (rule disjI2)
      apply (drule sum_pos_ex_elem_pos)
      apply (clarsimp simp add: List.map_filter_def comp_def)+
      apply (drule zcount_zmset_gt_0_set_Ex)
      apply (clarsimp split: prod.splits)
      subgoal for _ nid' _ p' x m
        apply (rule exI[of _ nid'])
        apply (rule exI[of _ p'])
        apply (auto simp add: map_filter_map_filter)
        apply (rule zcount_zmset_gt_0I)
        apply (auto simp flip: map_filter_map_filter)
        using prems3(2) apply auto[1]
        apply (rule image_eqI[rotated])
        apply clarsimp
        apply fastforce
        apply (auto simp add: map_replicate_const split: prod.splits option.splits if_splits)
        done
      done
    subgoal
      apply (auto simp add: zcount_to_zmset)
      done
    done
  done

lemma plus_minus_gt:
  "A + (B - C) > X \<Longrightarrow> C \<ge> (0 :: int) \<Longrightarrow>  A + B > X"
  by force


lemma data_in_channel_justifies_c_pts_alt:
  "Trg_caps_inv caps chnls \<Longrightarrow>
   c_pts_inv (change_multiplicities su (extract_prog Enum.enum nt os) c) caps \<Longrightarrow> 
   t \<in> snd ` set (chnls (nid, p)) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (produ (os n)). m \<ge> 0) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (consu (os n)). m \<ge> 0) \<Longrightarrow>
   inj_on nt (dom nt) \<Longrightarrow>
   zcount (c_pts c (Loc nid (Trg p)) + zmset (concat (map (\<lambda> (nid', p'). (map snd (filter (\<lambda> (p'', _, _). nt (nid', p'') = Some (nid, p) \<and> p' = p'') (produ (os nid'))))) Enum.enum))) t > 0"
  unfolding Trg_caps_inv_def
  apply (drule spec[of _ nid])
  apply (drule spec[of _ p])
  unfolding c_pts_inv_def
  apply (drule spec[of _ "Loc nid (Trg p)"])
  apply (simp add: c_pts_change_multiplicities)
  subgoal premises prems3
    using prems3(1,6) apply -
    unfolding extract_prog_def obtain_progress_def extract_progress_def
    apply (simp add:  BULK_BENQ_def zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
    apply (subst (asm) (1) monoid_add_class.sum_list_distinct_conv_sum_set)
    apply (simp_all)
    apply (subst (asm) Groups.ab_group_add_class.ab_diff_conv_add_uminus)
    apply (subst (asm) comm_monoid_add_class.sum.distrib)
    apply (subgoal_tac 
        "((\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (List.map_filter (\<lambda>(p, t, m). case nt (x, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os x))))))) =
  (\<Sum>x\<leftarrow>enum_class.enum. zmset (map snd (filter (\<lambda>(p'', ab). nt (fst x, p'') = Some (nid, p) \<and> snd x = p'') (produ (os (fst x))))))")
    subgoal
      apply (simp add: zmultiset_eq_iff)
      apply (drule spec[of _ t])+
      apply (simp add:  comp_def split_beta monoid_add_class.sum_list_distinct_conv_sum_set zcount_sum)
      apply (subgoal_tac "zcount (to_zmset (map snd (chnls (nid, p)))) t > 0")
      subgoal
        apply (drule sym)
        apply simp
        apply (drule plus_minus_gt)
        subgoal
          apply (rule zcount_zmset_ge_0I)
          using prems3  apply auto
          done
        subgoal
          by auto
        done
      subgoal
        apply (auto simp add: zcount_to_zmset)
        done
      done
    subgoal premises prems4
      apply (auto simp add: comp_def filter_map zcount_sum monoid_add_class.sum_list_distinct_conv_sum_set List.map_filter_def split_beta split: option.splits)
      apply (cases "\<exists> nid' p'. nt (nid', p') = Some (nid, p)")
      subgoal
        apply clarsimp
        subgoal for nid' p'
          apply (subst comm_monoid_add_class.sum.subset_diff[of "{nid'}"])
          apply simp_all
          apply (subst comm_monoid_add_class.sum.neutral)
          subgoal
            apply (intro ballI)
            apply (auto simp add: filter_empty_conv split: prod.splits intro!: zmset_emptyI)
            using prems3(4)
            apply (metis domI inj_on_contraD not_Some_eq2 prod.simps(1))
            done
          apply simp
          apply (subst comm_monoid_add_class.sum.subset_diff[of "{(nid', p')}"])
          apply simp_all
          apply (subst comm_monoid_add_class.sum.neutral)
          subgoal
            apply (intro ballI)
            apply (auto simp add: filter_empty_conv split: prod.splits intro!: zmset_emptyI)
            using prems3(4)
            apply (metis domI inj_on_contraD not_Some_eq2 prod.simps(1))+
            done
          apply simp
          apply (rule arg_cong[where f=zmset])
          apply (rule map_cong)
          subgoal
            apply (rule filter_cong)
            apply auto
            using prems3(4)
            apply (metis domI inj_on_contraD not_Some_eq2 prod.simps(1))
            done
          apply auto
          done
        done
      subgoal
        apply (subst comm_monoid_add_class.sum.neutral)
        subgoal
          apply (intro ballI)
          apply (auto simp add: filter_empty_conv split: prod.splits intro!: zmset_emptyI)
          apply (metis not_Some_eq2)
          done
        apply (subst comm_monoid_add_class.sum.neutral)
        subgoal
          apply (intro ballI)
          apply (auto simp add: filter_empty_conv split: prod.splits intro!: zmset_emptyI)
          done
        apply auto
        done
      done
    done
  done

lemma set_extract_progress_consumesD:
  "(l, t, m) \<in> set (extract_progress nid ed (snd (obtain_progress (consumes (os nid) p t' d)))) \<Longrightarrow>
   (l, t, m) \<in> set (extract_progress nid ed (snd (obtain_progress (os nid)))) \<or> 
   (\<exists> m'. l = Loc nid (Trg p) \<and> m = -1 \<and> t = t') \<or>
   (\<exists> p' s. l = Loc nid (Src p') \<and> m = 1 \<and> t = t' + s \<and> s \<in> set (intsum (os nid) p p'))"
  unfolding extract_progress_def obtain_progress_def
  apply (auto simp add: split_beta image_iff enum_class.enum_UNIV)
  done

lemma zmset_filter_extract_progress_Trg_consumes_alt:
  "zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p) = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p) = l) (extract_progress nid nt (snd (obtain_progress (os nid)))))) - {# t #}\<^sub>z"
  unfolding extract_progress_def obtain_progress_def
  apply simp
  apply (metis update_zmultiset_one(1))
  done
lemma zmset_filter_extract_progress_Trg_consumes_diff_p:
  "p \<noteq> p' \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (os nid))))))"
  unfolding extract_progress_def obtain_progress_def
  apply simp
  done
lemma zmset_filter_extract_progress_Trg_consumes_diff_nid:
  "nid \<noteq> nid' \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (os nid))))))"
  unfolding extract_progress_def obtain_progress_def
  apply simp
  done
lemma zmset_filter_extract_progress_Trg_consumes_diff:
  "nid' = nid \<longrightarrow> p' \<noteq> p \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (os nid))))))"
  unfolding extract_progress_def obtain_progress_def
  apply auto
  done
lemma zmset_filter_extract_progress_Src_consumes:
  "zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Src p') = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Src p') = l) (extract_progress nid nt (snd (obtain_progress (os nid)))))) + to_zmset (map ((-+-) t) (intsum (os nid) p p'))"
  by (clarsimp simp add: extract_progress_def obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat)
lemma zmset_filter_extract_progress_Src_consumes_no_intsum:
  "nid' = nid \<longrightarrow> intsum (os nid) p p' = [] \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid' (Src p') = l') (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid' (Src p') = l') (extract_progress nid nt (snd (obtain_progress (os nid))))))"
  apply (clarsimp simp add: monoid_add_class.sum_list_distinct_conv_sum_set extract_progress_def obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat)
  apply (smt (verit) filter.simps(1) filter_empty_conv list.map(1) sum.neutral to_zmset.simps(1))
  done

lemma zmset_filter_extract_progress_Src_consumes_diff:
  "nid' \<noteq> nid \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Src p') = l) (extract_progress nid nt oss))) = 
   {#}\<^sub>z"
  by (clarsimp simp add: List.map_filter_def split_beta extract_progress_def obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat split: option.splits)

lemma zmset_filter_Trg_not_nid:
  "(\<Sum>x\<in>UNIV - {nid}. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress x nt (snd (obtain_progress (os x))))))) =
   (\<Sum>x\<in>UNIV - {nid}. zmset (List.map_filter (\<lambda>(p', t, d). case nt (x, p') of None \<Rightarrow> None | Some (nid'', p'') \<Rightarrow> if nid'' = nid \<and> p'' = p then Some (t, d) else None) (produ (os x))))"
  apply (clarsimp simp add: extract_progress_def List.map_filter_def obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat split: prod.splits if_splits option.splits)
  apply (rule sum.cong)
  apply simp
  apply (clarsimp simp add: extract_progress_def split_beta obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat split: prod.splits if_splits option.splits)
  apply (rule arg_cong[where f=zmset])
  apply (rule map_cong)
  apply (rule filter_cong)
  apply (auto simp add: extract_progress_def split_beta obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat split: prod.splits if_splits option.splits)
  apply (metis not_Some_eq2 option.sel option.simps(3))+
  done

lemma t_in_buf_cases:
  "cbufs (nid, p) = (d, t) # xs \<Longrightarrow>
   Trg_caps_inv caps (outputs_at_target su os >> cbufs) \<Longrightarrow>
   c_pts_inv (change_multiplicities su (extract_prog enum_class.enum nt os) c) caps \<Longrightarrow>
   0 < zcount (c_pts c (Loc nid (Trg p)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress nid nt (snd (obtain_progress (os nid))))))) t \<or>
   0 < zcount
         (\<Sum>x\<in>UNIV - {nid}.
            zmset (List.map_filter (\<lambda>(p', t, d). case nt (x, p') of None \<Rightarrow> None | Some (nid'', p'') \<Rightarrow> if nid'' = nid \<and> p'' = p then Some (t, d) else None) (produ (os x))))
         t"
  unfolding Trg_caps_inv_def
  apply (drule spec[of _ nid])
  apply (drule spec[of _ p])
  unfolding c_pts_inv_def
  apply (drule spec[of _ "Loc nid (Trg p)"])
  apply (simp add: c_pts_change_multiplicities extract_prog_def filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)
  apply (subst (asm) comm_monoid_add_class.sum.subset_diff[of "{nid}"])
  apply simp_all
  unfolding zmultiset_eq_iff
  apply (drule spec[of _ t])+
  apply (subgoal_tac  "zcount
       (c_pts c (Loc nid (Trg p)) +
        ((\<Sum>x\<in>UNIV - {nid}. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress x nt (snd (obtain_progress (os x))))))) +
         zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress nid nt (snd (obtain_progress (os nid))))))))
       t > 0")
  subgoal premises prems3
    using prems3(4) 
    by (auto simp add: zmset_filter_Trg_not_nid)
  subgoal
    unfolding outputs_at_target_def BULK_BENQ_def
    apply (auto simp add: to_zmset_nenneg split: option.splits prod.splits)
    done
  done

lemma frontier_less_equal_sumI_alt:
  "finite S \<Longrightarrow>
   frontier_less_equal (frontier (sum f S)) t \<Longrightarrow>
   (\<forall> x\<in>S. frontier_less_equal (frontier (f x)) t \<longrightarrow> (\<exists> x'. frontier_less_equal (frontier (f' x)) t) ) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f' l) t \<ge> 0) \<Longrightarrow>
   frontier_less_equal (frontier (sum f' S)) t"
  apply (drule frontier_less_equal_sumE)
  apply assumption
  apply clarsimp
  apply (rule frontier_less_equal_sumI)
  apply simp_all
  apply blast
  done

lemma frontier_filter_pos:
  "frontier M = frontier (filter_zmset (\<lambda> t. zcount M t > 0) M)"
  apply transfer'
  apply (auto simp add: minimal_antichain_def)
  done

lemma pos_zcount_image_zmset_inj: 
  "0 < zcount M t \<Longrightarrow>inj f \<Longrightarrow>  0 < zcount (image_zmset f M) (f t)"
  apply transfer
  subgoal for M t f
    apply (induct M)
    subgoal for Mp Mn
      apply simp
      apply (metis basic_trans_rules(22) count_image_mset_ge_count count_image_mset_inj)
      done
    done
  done

lemma in_frontier_zmset_imageD:
  "t \<in>\<^sub>A frontier {#t -+- s. t \<in>#\<^sub>z M#} \<Longrightarrow> (\<exists> t'. t = t' -+- s \<and> t' \<in>\<^sub>A frontier M)"
  apply transfer'
  apply (auto simp add: zcount_sum minimal_antichain_def)
  subgoal for t s M
    apply (drule zcount_zimageD)
    apply clarsimp
    subgoal for t'' t'
      apply (drule spec[of _ "t' -+- s"])
      apply (drule mp)
      apply (rule pos_zcount_image_zmset_inj)
      apply auto
      done
    done
  done

lemma frontier_less_equal_image_zmsetD:
  "frontier_less_equal (frontier {#t -+- s. t \<in>#\<^sub>z A#}) t \<Longrightarrow>
   \<exists> t'. frontier_less_equal (frontier A) t' \<and>t' -+- s \<le> t"
  unfolding frontier_less_equal_iff2
  apply clarsimp
  apply (drule in_frontier_zmset_imageD)
  apply auto
  done

lemma change_multiplicities_extract_progress_consumes:
  "change_multiplicities su (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))) =
   change_multiplicities su (extract_progress nid nt (snd (obtain_progress (os nid))) @ [(Loc nid (Trg p), t, -1)] @ concat (map (\<lambda> p'. map (\<lambda> t'. (Loc nid (Src p'),  (t -+- t'), 1)) (intsum (os nid) p p')) enum_class.enum))"
  unfolding extract_progress_def consumes_def obtain_progress_def
  apply (simp add: comp_def map_concat)
  apply (rule ext)
  subgoal for c
    using change_multiplicities_comm 
    by (smt (verit, ccfv_SIG) change_multiplicities_append_alt change_multiplicities_simp_alt)
  done

lemma change_multiplicities_extract_progress_updates:
  "change_multiplicities su (extract_progress nid nt (snd (obtain_progress
                  (os nid
                   \<lparr>outpu := OP, ocaps := OC, input := IP, produ := produ (os nid) @ produs,
                      inter := operator_state.inter (os nid) @ interr, nfron := V\<rparr>)))) = 
   change_multiplicities su (extract_progress nid nt (snd (obtain_progress (os nid))) @
   (List.map_filter (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) produs) @
   map (\<lambda>(p, y). (Loc nid (Src p), y)) interr)"
  apply (rule ext)
  unfolding obtain_progress_def extract_progress_def
  apply (clarsimp simp add: comp_def map_concat)
  apply (smt (verit) change_multiplicities_append_alt change_multiplicities_comm)
  done

lemma change_multiplicities_extract_prog_updates:
  "nid \<in> set xs \<Longrightarrow>
   distinct xs \<Longrightarrow>
   change_multiplicities su (extract_prog xs nt
           (os(nid := os nid \<lparr>outpu := OP, ocaps := OC, input := IP, produ := produ (os nid) @ produs,
                      inter := operator_state.inter (os nid) @ interr, nfron := V\<rparr>))) = 
   change_multiplicities su (extract_prog xs nt os @
   (List.map_filter (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) produs) @
   map (\<lambda>(p, y). (Loc nid (Src p), y)) interr)"
  apply (rule ext)
  apply (subst (1) change_multiplicities_extract_prog_obtain_progress_remove1_append)
  apply assumption+
  apply (simp add: change_multiplicities_append_alt)
  apply (subst (2) change_multiplicities_extract_prog_obtain_progress_remove1_append)
  apply assumption+
  apply (subst change_multiplicities_extract_progress_updates)
  apply (simp add: change_multiplicities_append_alt)
  apply (smt (verit) change_multiplicities_append_alt change_multiplicities_comm) 
  done

find_theorems remove1 extract_prog

lemma change_multiplicities_extract_prog_consumes:
  "nid \<in> set xs \<Longrightarrow>
   distinct xs \<Longrightarrow>
   change_multiplicities su (extract_prog xs nt (os(nid := consumes (os nid) p t d))) =
   change_multiplicities su (extract_prog xs nt os @ [(Loc nid (Trg p), t, -1)]@ concat (map (\<lambda> p'. map (\<lambda> t'. (Loc nid (Src p'),  (t -+- t'), 1)) (intsum (os nid) p p')) enum_class.enum))"
  apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append)
  apply assumption+
  apply (simp add: change_multiplicities_append flip: change_multiplicities_append)
  apply (rule ext)
  apply (subst change_multiplicities_comm)
  apply (subst change_multiplicities_comm change_multiplicities_append)
  apply (subst change_multiplicities_comm)
  apply (simp add: change_multiplicities_append change_multiplicities_extract_progress_consumes)
  apply (smt (verit, best) change_multiplicities_append change_multiplicities_comm change_multiplicities_extract_prog_obtain_progress_remove1_append)
  done

lemma frontier_less_equal_trans_subset:
  "frontier_less_equal (frontier N) t' \<Longrightarrow>
   t' \<le> t \<Longrightarrow>
   N \<subseteq>#\<^sub>z M \<Longrightarrow>
   frontier_less_equal (frontier M) t"
  using frontier_less_equal_le_trans frontier_less_equal_trans frontier_lt_subseq by blast

lemma filter_Trg_extract_prog_produ:
  "distinct xs \<Longrightarrow>
   inj_on nt (dom nt) \<Longrightarrow>
   nid \<notin> set xs \<Longrightarrow>
   nid' \<in> set xs \<Longrightarrow>
   nt (nid', p') = Some (nid , p) \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog xs nt os) =
   map (\<lambda> (p'', t, m). (Loc nid (Trg p), t, m)) (filter (\<lambda> (p'', _, _). p'' = p') (produ (os nid')))"
  unfolding extract_prog_def obtain_progress_def extract_progress_def
  apply (clarsimp simp add: List.map_filter_def map_concat filter_concat comp_def filter_map split_beta split: option.splits)
  apply (induct xs rule: rev_induct)
  apply (auto simp add: List.map_filter_def map_concat filter_concat comp_def filter_map split_beta split: option.splits)
  subgoal for xs'
    apply (subst HOL.iffD2[OF concat_eq_Nil_conv])
    subgoal
      apply (auto simp add: filter_empty_conv)
      apply (metis Pair_inject domI inj_on_eq_iff not_Some_eq2)
      done
    apply simp
    apply (rule map_cong)
    subgoal
      apply (rule filter_cong)
      apply auto
      apply (metis domI inj_onD prod.inject)
      done
    apply auto
    done
  subgoal
    apply (auto simp add: filter_empty_conv)
    apply (metis (no_types, opaque_lifting) Pair_inject domIff inj_on_contraD not_Some_eq2)
    done
  done

lemma filter_Trg_extract_prog_produ_empty:
  "distinct xs \<Longrightarrow>
   inj_on nt (dom nt) \<Longrightarrow>
   nid \<notin> set xs \<Longrightarrow>
   nid \<notin> fst ` (ran nt) \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog xs nt os) = []"
  unfolding extract_prog_def obtain_progress_def extract_progress_def
  apply (auto simp add: filter_empty_conv List.map_filter_def map_concat filter_concat comp_def filter_map split_beta split: option.splits)
  apply (metis img_fst ranI)
  done

lemma in_frontier_c_pts_change_multiplicities_consumes_Trg:
  "ft \<in>\<^sub>A frontier (c_pts (change_multiplicities su (extract_progress nid nt (snd (obtain_progress (os nid)))) c) (Loc nid (Trg p))) \<Longrightarrow>
   t \<noteq> ft \<Longrightarrow>
   ft \<in>\<^sub>A frontier (c_pts (change_multiplicities su (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))) c) (Loc nid (Trg p)))"
  apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
  apply (smt (verit, best) Groups.add_ac(2,3) add_diff_cancel diff_add_cancel in_frontier_minusI)
  done


lemma change_multiplicities_extract_prog_extract_progress[simp]:
  "nid \<in> set xs \<Longrightarrow>
   distinct xs \<Longrightarrow>
   st = snd (obtain_progress (os nid)) \<Longrightarrow>
   (change_multiplicities su (extract_prog xs nt (os(nid := fst (obtain_progress (os nid))))) (change_multiplicities su (extract_progress nid nt st) c)) =
   (change_multiplicities su (extract_prog xs nt os) c)"
  apply (induct xs arbitrary: c rule: rev_induct)
  apply simp_all
  subgoal for nid' xs
    apply (elim disjE)
    subgoal
      apply clarsimp
      apply hypsubst_thin
      unfolding extract_prog_def obtain_progress_def extract_progress_def
      apply (simp add: map_concat split_beta)
      apply (smt (verit) change_multiplicities_append_alt change_multiplicities_comm map_eq_conv)
      done
    subgoal
      apply clarsimp
      apply hypsubst_thin
      unfolding extract_prog_def obtain_progress_def extract_progress_def
      apply (auto simp add: change_multiplicities_append_alt map_concat split_beta)
      done
    done
  done

lemma c_imp_change_multiplicities[simp]:
  "c_imp (change_multiplicities su xs c) = c_imp c"
  apply (induct xs arbitrary: c)
  apply simp
  apply (auto split: if_splits prod.splits simp add: change_multiplicities_simp_alt update_zmultiset_plus_comm) 
  done

lemma frontier_le_subset[simp]:
  "frontier A \<le> frontier (zmset_of (mset_set {t' \<in> set_antichain (frontier A). P t'}))"
  unfolding less_eq_antichain_def
  apply auto
  apply transfer'
  apply (auto simp add: minimal_antichain_def)
  done

lemma frontier_less_equal_change_multiplicities_ge_0:
  assumes D: "dataflow_topology su (-+-)"
  shows 
    "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (ifrontier su (+) c l) t \<and> m \<ge> 0) \<Longrightarrow>
   ifrontier su (+) c l \<le> ifrontier su (+) (change_multiplicities su A c) l"
  apply (induct A arbitrary: c l rule: rev_induct)
  apply simp
  subgoal premises prems for a A c l
    using prems(2-) apply -
    apply clarsimp
    subgoal for l2 t m
      apply hypsubst_thin
      apply (subst change_multiplicities_comm)
      apply (subst change_multiplicities_append)
      apply (rule order.trans[rotated])
      apply (rule prems(1))
      apply simp_all
      subgoal
        apply clarsimp
        subgoal for l' t' m'
          apply (drule bspec)
          apply assumption
          apply clarsimp
          apply (rule frontier_less_equal_le_trans)
          apply assumption
          subgoal premises prems2
            using prems2(4) apply -
            apply (rule ifrontier_le_all_le[OF D])
            unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D]
            apply (clarsimp simp add: c_pts_change_multiplicities comp_def)
            apply (rule frontier_below_eq_frontier_plus_pos)
            using prems2(2) apply (simp add: zcount_update_zmultiset)
            done
          done
        done
      subgoal premises prems2
        using prems2(2,3) apply -
        unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D]
        apply (clarsimp simp add: c_pts_change_multiplicities comp_def)
        apply (drule frontier_less_equal_sumE)
        apply simp_all
        apply clarsimp
        apply (drule frontier_less_equal_sumE)
        apply simp_all
        apply clarsimp
        subgoal for l3 s'
          unfolding frontier_less_equal_iff2
          apply clarsimp
          subgoal for ft
            apply (subst (asm) in_frontier_zmset_image)
            apply simp_all
            apply clarsimp
            subgoal for ft'
              apply hypsubst_thin
              apply (cases "zcount (c_pts c l2) t + m > 0")
              subgoal
                apply (subst (1) comm_monoid_add_class.sum.subset_diff[where B="{l2,l3}"])
                apply simp_all
                apply (subst (3) comm_monoid_add_class.sum.subset_diff[where B="{l2,l3}"])
                apply simp_all
                apply (rule frontier_add_add_le)
                apply (simp_all add: zcount_sum sum_nonneg)
                apply (cases "l2 = l3")
                subgoal
                  apply simp
                  apply (rule frontier_sum_le)
                  apply (simp_all add: zcount_sum sum_nonneg)
                  apply clarsimp
                  apply (rule frontier_le_image)
                  apply (simp_all add: zcount_sum sum_nonneg)
                  subgoal
                    by (smt (verit) D Timely_Infrastructure.update_zmultiset_plus add.commute add_empty_zmultiset(2) dataflow_topology.results_in_zero dataflow_topology_from_tree.results_in_mono_raw in_frontier_addD le_iff_add
                        less_eq_antichain_def zcount_union zcount_update_zmultiset)
                      (* slow but ok *)
                  done
                subgoal
                  apply simp
                  apply (cases "frontier_less_equal (frontier (c_pts c l2)) t")
                  subgoal
                    apply (rule frontier_add_add_le)
                    apply (simp_all add: zcount_sum sum_nonneg)
                    apply (rule frontier_sum_le)
                    apply (simp_all add: zcount_sum sum_nonneg)
                    apply clarsimp
                    apply (rule frontier_le_image)
                    apply (simp_all add: zcount_sum sum_nonneg)
                    apply (smt (verit, ccfv_threshold) frontier_below_eq_frontier_plus_pos frontier_less_equal_add_frontier_le_alt group_cancel.rule0 zcount_empty zcount_ne_zero_iff zcount_update_zmultiset)
                    done
                  subgoal
                    apply (subst set_antichain_frontier_add_update_zmultiset_le)
                    apply simp_all
                    apply (subst mset_set.insert)
                    apply simp_all
                    using frontier_less_equal_zcount_pos member_frontier_pos_zmset set_antichain1 apply blast
                    apply (subst add_zmset_add_single)
                    apply (simp only:  comm_monoid_add_class.sum.distrib)
                    apply (subst add.assoc)
                    apply (subst (7) add.commute)
                    apply (simp flip: add.assoc)
                    apply (rule frontier_less_equal_add_frontier_le_alt)
                    subgoal
                      apply auto
                      subgoal for ft
                        apply (rule frontier_less_equal_addI)
                        apply (simp_all add: zcount_sum sum_nonneg)
                        apply (rule disjI2)
                        apply (subst frontier_less_equal_frontier_sum_iff)
                        apply (simp_all add: zcount_sum sum_nonneg)
                        apply (subgoal_tac "\<exists> s. s \<in>\<^sub>A graph.path_weight su l2 l \<and> ft = t -+- s")
                        subgoal
                          apply clarsimp
                          subgoal for s''
                            apply (clarsimp simp flip: member_antichain.rep_eq)
                            apply (drule graph.path_weight_elem_trans[rotated, of s'])
                            apply assumption
                            subgoal
                              apply (rule dataflow_topology.axioms(1))
                              using D apply assumption
                              done
                            apply clarsimp
                            subgoal for u
                              apply (rule bexI[rotated])
                              apply (clarsimp simp flip: member_antichain.rep_eq)
                              apply assumption
                              unfolding frontier_less_equal_iff2
                              apply clarsimp
                              apply (rule exI[of _ "ft' -+- u"])
                              apply (auto simp add: in_frontier_zmset_image)
                              apply (smt (verit, del_insts) Groups.add_ac(2) add_le_imp_le_right add_mono_thms_linordered_semiring(1) group_cancel.add2)
                              done
                            done
                          done
                        subgoal
                          apply (subst (asm) sum_zmset)
                          apply simp_all
                          apply (clarsimp simp flip: member_antichain.rep_eq)
                          done
                        done
                      done
                    apply (rule frontier_add_add_le)
                    apply (simp_all add: zcount_sum sum_nonneg)
                    subgoal
                      apply (rule frontier_sum_le)
                      apply (simp_all add: zcount_sum sum_nonneg)
                      apply clarsimp
                      apply (rule frontier_le_image_gen)
                      apply (simp_all add: zcount_sum sum_nonneg)
                      done
                    done
                  done
                done
              subgoal
                apply (rule frontier_sum_le)
                apply (simp_all add: zcount_sum sum_nonneg)
                apply (rule frontier_sum_le)
                apply (simp_all add: zcount_sum sum_nonneg)
                apply clarsimp
                apply (rule frontier_le_image)
                apply (simp_all add: frontier_add_update_zmultiset_not_le zcount_sum sum_nonneg)
                done
              done
            done
          done
        done
      done
    done
  done

lemma frontier_less_equal_change_multiplicities_lt_0:
  assumes D: "dataflow_topology su (-+-)"
  shows 
    "(\<forall> (l, t, m) \<in> set A. m < 0) \<Longrightarrow>
   ifrontier su (+) c l \<le> ifrontier su (+) (change_multiplicities su A c) l"
  apply (induct A arbitrary: c l rule: rev_induct)
  apply simp
  subgoal premises prems for a A c l
    using prems(2-) apply -
    apply clarsimp
    subgoal for l2 t m
      apply hypsubst_thin
      apply (subst change_multiplicities_comm)
      apply (subst change_multiplicities_append)
      apply (rule order.trans[rotated])
      apply (rule prems(1))
      apply simp_all
      subgoal premises prems2
        using prems2(2-) apply -
        unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D]
        apply (clarsimp simp add: c_pts_change_multiplicities comp_def)
        apply (rule frontier_sum_le)
        apply (simp_all add: zcount_sum sum_nonneg)
        apply (rule frontier_sum_le)
        apply (simp_all add: zcount_sum sum_nonneg)
        apply clarsimp
        apply (rule frontier_le_image)
        apply (simp_all add: zcount_update_zmultiset frontier_add_update_zmultiset_not_le zcount_sum sum_nonneg)
        done
      done
    done
  done

lemma frontier_less_equal_change_multiplicities:
  assumes D: "dataflow_topology su (-+-)"
  shows 
    "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (ifrontier su (+) c l) t) \<Longrightarrow>
     ifrontier su (+) c l \<le> ifrontier su (+) (change_multiplicities su A c) l"
  apply (subgoal_tac "change_multiplicities su A c = change_multiplicities su (filter (\<lambda> (l, t, m). m < 0) A) (change_multiplicities su (filter (\<lambda> (l, t, m). m \<ge> 0) A) c)")
  subgoal premises prems
    apply (subst prems(2))
    apply (rule order.trans)
    apply (rule frontier_less_equal_change_multiplicities_ge_0[OF D, where A="filter (\<lambda>(l, t, m). m \<ge> 0) A"])
    using prems(1)
    apply simp
    apply force
    apply (rule order.trans)
    apply (rule frontier_less_equal_change_multiplicities_lt_0[OF D, where A="filter (\<lambda>(l, t, m). m < 0) A"])
    apply simp_all
    done
  subgoal premises prems
    apply (induct A rule: rev_induct)
    apply auto
    apply (smt (verit, best) change_multiplicities_append change_multiplicities_comm)+
    done
  done


lemma take_step_CM_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   d \<noteq> 0 \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary (CM loc t d)) c)"
  apply (frule Executable.enum_dataflow_topology.CM_next[where delta=d, simplified, unfolded enum_dataflow_topology_def])
  apply assumption+
  apply (elim exE)
  apply (subst take_step_enum_dataflow_topology_take_step)
  apply (simp add: enum_dataflow_topology_def)
  apply (rule Propagate.dataflow_topology.cm_preserves_inv_imps_work_sum)
  apply assumption+
  done

lemma take_step_CM_p_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   d \<noteq> 0 \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary (CM loc t d)) c) \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg ((take_step summary (CM loc t d)) c) \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary (CM loc t d)) c)"
  apply (frule Executable.enum_dataflow_topology.CM_next[where delta=d, simplified, unfolded enum_dataflow_topology_def])
  apply assumption+
  apply (elim exE)
  apply (subst (1 2) take_step_enum_dataflow_topology_take_step)
  apply (simp add: enum_dataflow_topology_def)
  apply (intro conjI)
  apply (rule Propagate.dataflow_topology.cm_preserves_inv_implications_nonneg)
  apply assumption+
  apply (rule Propagate.dataflow_topology.iiws_imp_iipwn)
  apply assumption+
  apply (subst take_step_enum_dataflow_topology_take_step[symmetric])
  apply (simp add: enum_dataflow_topology_def)
  apply (rule take_step_CM_p_preserves_inv_imps_work_sum)
  apply assumption+
  apply auto[1]
  apply (rule take_step_CM_p_preserves_inv_imps_work_sum)
  apply assumption+
  apply auto
  done

lemma change_multiplicities_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   (\<forall> d \<in> snd ` snd ` set xs. d \<noteq> 0) \<Longrightarrow>
   (\<forall> (l, t, d) \<in> set xs. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c l) \<and> t' \<le> t) \<Longrightarrow>
   change_multiplicities summary xs c = c' \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c'"
  apply (induct xs arbitrary: c c')
  apply simp
  subgoal premises prems for a xs c c'
    using prems(2-) apply -
    apply (simp split: prod.splits)
    subgoal for l b t' d t
      apply (subst (asm) change_multiplicities_simps(2)[where summary=summary])
      apply (frule take_step_CM_p_preserves_inv[where loc=l and t=t'])
      apply assumption+
      apply force
      apply (elim conjE)
      using prems(1) apply -
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply assumption
      apply (drule meta_mp)
      apply assumption
      back
      apply (drule meta_mp)
      apply assumption
      apply (drule meta_mp)
      apply blast
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply fastforce
      apply (drule meta_mp)
      apply auto
      done
    done
  done

lemma filter_map_filter:
  "(\<forall> x \<in> set xs. F x \<noteq> None \<longrightarrow> Q x \<and> (the (F x) = g x)) \<Longrightarrow>
   (\<forall> x \<in> set xs. Q x \<longrightarrow> (F x) = Some (g x)) \<Longrightarrow>
   filter P (List.map_filter F xs) = map g (filter (\<lambda>x. Q x \<and> P (g x)) xs)"
  unfolding List.map_filter_def comp_def 
  apply (subst (1) filter_map)
  unfolding filter_filter comp_def
  apply (rule map_cong)
  apply (rule filter_cong)
  apply simp_all
  apply auto
  done

lemma map_snd_filter_List_map_filter:
  "nt (nid, p'') = Some (nid', p') \<Longrightarrow>
   inj_on nt (dom nt) \<Longrightarrow>
   map snd (filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l')
       (List.map_filter (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs)) =
   map snd (filter (\<lambda>(p''a, ab). nt (nid, p''a) = Some (nid', p') \<and> p'' = p''a) xs)"
  apply (induct xs)
  apply simp
  apply (clarsimp split: prod.splits option.splits)
  using inj_on_contraD apply fastforce
  done

lemma gt_0_plusD:
  "0 < a + b \<Longrightarrow> 0 < a \<or> 0 < (b :: int)"
  by auto


lemma find_Some_singleton:
  "{x \<in> set xs . P x} = {x} \<Longrightarrow>
   find P xs = Some x"
  apply (induct xs)
  apply simp_all
  apply (auto 0 0 simp add:)
  apply blast
  apply (smt (verit, best) Collect_cong)
  done

lemma in_op_conn_graph_to_nxt_iff:
  "bi_unique (op_conn su) \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid', p') \<longleftrightarrow> op_conn su (nid, p) (nid', p')"
  unfolding graph_to_nxt_def
  apply (auto simp add: is_empty_antichain_iff split: prod.splits)
  subgoal
    apply (auto simp add: dest!: find_SomeD' split: prod.splits)
    done
  subgoal
    apply (rule find_Some_singleton)
    apply (auto simp add: bi_unique_def split: prod.splits)
    done
  done

lemma graph_to_nxt_Some:
  "graph_summar_nt su (graph_to_nxt su) os \<Longrightarrow>
   s \<in>\<^sub>A su (Loc nid (Src p)) (Loc nid' (Trg p')) \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid', p')"
  unfolding graph_summar_nt_def
  apply clarsimp
  unfolding graph_to_nxt_def is_empty_antichain_iff
  apply simp
  apply (rule find_Some_singleton)
  apply auto
  apply (metis in_op_conn_graph_to_nxt_iff mem_antichain_nonempty_alt op_conn.simps option.simps(1) prod.inject)+
  done

lemma intsum_from_graph:
  "graph_summar_nt su (graph_to_nxt su) os \<Longrightarrow>
   s \<in>\<^sub>A su (Loc nid (Trg p)) (Loc nid' (Src p')) \<Longrightarrow>
   nid = nid' \<and> s \<in> set (intsum (os nid) p p')"
  unfolding graph_summar_nt_def
  apply clarsimp
  unfolding graph_to_nxt_def
  apply fast
  done

lemma graph_to_nxt_Some_alt:
  "graph_summar_nt su (graph_to_nxt su) os \<Longrightarrow>
   su (Loc nid (Src p)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid', p')"
  using graph_to_nxt_Some by (metis ac_eq_iff mem_antichain_nonempty)

lemma summary_SrcEx:
  "graph_summar_nt su (graph_to_nxt su) os \<Longrightarrow>
   s \<in>\<^sub>A su l (Loc nid' (Trg p')) \<Longrightarrow>
   \<exists> nid p. l = Loc nid (Src p)"
  unfolding graph_summar_nt_def
  apply clarsimp
  unfolding graph_to_nxt_def is_empty_antichain_iff
  apply simp
  apply (metis location.exhaust mem_antichain_nonempty port.exhaust)
  done

lemma summary_TrgEx:
  "graph_summar_nt su (graph_to_nxt su) os \<Longrightarrow>
   s \<in>\<^sub>A su l (Loc nid' (Src p')) \<Longrightarrow>
   \<exists> nid p. l = Loc nid (Trg p)"
  unfolding graph_summar_nt_def
  apply clarsimp
  unfolding graph_to_nxt_def is_empty_antichain_iff
  apply simp
  apply (metis location.exhaust mem_antichain_nonempty port.exhaust)
  done

lemma graph_to_nxt_inj:
  "graph_summar_nt su (graph_to_nxt su) os \<Longrightarrow>
   graph_to_nxt su (nid1, p1) = Some (nid, p) \<Longrightarrow>
   graph_to_nxt su (nid2, p2) = Some (nid, p) \<Longrightarrow>
   nid1 = nid2 \<and> p1 = p2"
  unfolding graph_summar_nt_def inj_on_def apply -
  apply clarsimp
  apply (drule sym)
  apply simp
  apply (drule bspec)
  defer
  apply (drule bspec)
  defer
  apply (drule mp)
  apply assumption
  apply clarsimp
  subgoal
    unfolding graph_to_nxt_def
    apply clarsimp
    apply metis
    done
  subgoal
    unfolding graph_to_nxt_def
    apply clarsimp
    apply metis
    done
  done

lemma graph_to_nxt_fun:
  "graph_summar_nt su (graph_to_nxt su) os \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid1, p1) \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid2, p2) \<Longrightarrow>
   nid1 = nid2 \<and> p1 = p2"
  unfolding graph_summar_nt_def inj_on_def apply -
  apply clarsimp
  done

lemma dataplane_tracker_inv_clean:
  "sg = sg'\<lparr> upfro := f \<rparr> \<Longrightarrow>
   (\<forall> nid. intsum (os nid) = intsum (os' nid) \<and> ocaps (os nid) = ocaps (os' nid) \<and> 
   consu (os nid) = consu (os' nid) \<and> inter (os nid) = inter (os' nid) \<and>
   produ (os nid) = produ (os' nid) \<and> input (os nid) = input (os' nid) \<and>
   outpu (os nid) = outpu (os' nid) \<and> front (os nid) = front (os' nid)) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg'"
  unfolding dataplane_tracker_inv_def 
  apply clarsimp
  apply (rule iffI)
  subgoal
    apply clarsimp
    subgoal for caps
      apply (rule exI[of _ caps])
      apply hypsubst_thin
      unfolding propagation_inv_def BULK_BENQ_def  Src_caps_inv_def Trg_caps_inv_def produ_consu_inter_supported_def extract_prog_changes_above_impl_inv_def change_deltas_inv_def front_inv_def c_pts_inv_def chnls_imp_front_inv_def
      apply (auto simp add: obtain_progress_def outputs_at_target_def extract_prog_def extract_progress_def split: prod.splits)
      subgoal
        by (metis (lifting) Un_iff snd_eqD)
      subgoal premises prems for nid p a b aa ba uu_ uua_
        apply (rule prems(7)[rule_format, of "(a, b)", simplified])
        using prems(1,16,17,18) apply auto
        done
      done
    done
  subgoal
    apply clarsimp
    subgoal for caps
      apply (rule exI[of _ caps])
      apply hypsubst_thin
      unfolding propagation_inv_def BULK_BENQ_def  Src_caps_inv_def Trg_caps_inv_def produ_consu_inter_supported_def extract_prog_changes_above_impl_inv_def change_deltas_inv_def front_inv_def c_pts_inv_def chnls_imp_front_inv_def
      apply (auto simp add: obtain_progress_def outputs_at_target_def extract_prog_def extract_progress_def split: prod.splits)
      subgoal
        by (metis (lifting) Un_iff snd_eqD)
      subgoal premises prems for nid p a b aa ba uu_ uua_
        apply (rule prems(7)[rule_format, of "(a, b)", simplified])
        using prems(1,16,17,18) apply auto
        done
      done
    done
  done

lemma the_elem_bi_unique_op_conn:
  "the_elem {(nid', p'). su (Loc nid' (Src p')) (Loc nid (Trg p)) \<noteq> {}\<^sub>A} = (nid', p') \<Longrightarrow>
   su (Loc nid'' (Src p'')) (Loc nid (Trg p)) \<noteq> {}\<^sub>A \<Longrightarrow>
   bi_unique (op_conn su) \<Longrightarrow>
   nid' = nid'' \<and> p' = p''"
  apply (subst (asm) the_elem_image_unique[where f=id, simplified, of _  "(nid'', p'')"])
  apply blast
  unfolding bi_unique_def
  apply auto
  done


lemma outputs_at_target_outpu_if:
  "bi_unique (op_conn su) \<Longrightarrow>
   os' = os(nid := (os nid)\<lparr> outpu := X \<rparr>) \<Longrightarrow>
   outputs_at_target su os' (nid', p') = 
  (let S = {p. op_conn su (nid, p) (nid', p')} in if S \<noteq> {} then let p = the_elem S in X p else outputs_at_target su os (nid', p'))"
  unfolding outputs_at_target_def
  apply (auto split: prod.splits)
  subgoal
    apply (drule the_elem_bi_unique_op_conn)
    apply assumption+
    apply auto
    done
  subgoal for x2 a b x
    apply (subst the_elem_image_unique[where f=id, simplified, of _ "b"])
    apply fast
    unfolding bi_unique_def
    apply auto
    apply (subst (asm) the_elem_image_unique[where f=id, simplified, of _  "(a, b)"])
    apply blast
    apply auto
    done
  subgoal for x2 a b x
    apply (subst the_elem_image_unique[where f=id, simplified, of _ "x"])
    apply fast
    unfolding bi_unique_def
    apply auto
    apply (subst (asm) the_elem_image_unique[where f=id, simplified, of _  "(_, x)"])
    apply blast
    apply auto
    done
  done


definition "ts inps = cimage (\<lambda> e. case e of Data t d \<Rightarrow> t) (cfilter is_Data (cset_of_llist inps))"


definition "coll inps t = list_of (lmap (\<lambda> e. case e of Data t d \<Rightarrow> d) (lfilter (\<lambda> e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps))"

lemma coll_LNil[simp]:
  "coll LNil t = []"
  by (auto simp add: coll_def list_of_LCons_conv)
lemma coll_LCons_Data:
  "lfinite (lfilter (\<lambda>e. event.time e = t) inps) \<Longrightarrow>
   coll (LCons (Data t' e) inps) t = (if t = t' then e # coll inps t else coll inps t)"
  apply (auto simp add: coll_def list_of_LCons_conv)
  apply (rule FalseE)
  apply (subgoal_tac "llength (lfilter (\<lambda>e. event.time e = t') inps) \<ge> llength (lfilter (\<lambda>x. case x of Data t'a d \<Rightarrow> t' = t'a | _ \<Rightarrow> False) inps)")
  subgoal
    by (metis basic_trans_rules(24) enat_ord_simps(3) llength_eq_infty_conv_lfinite)
  subgoal premises
    apply(induct inps)
    apply (auto intro: order_trans split: event.splits)
    apply (smt (verit, best) basic_trans_rules(7) eSuc_ile_mono ile_eSuc lfilter_cong)+
    done
  done
lemma coll_LCons_Drop[simp]:
  "coll (LCons (Drop t') inps) t = coll inps t"
  by (auto simp add: coll_def list_of_LCons_conv)
lemma coll_LCons_Mint[simp]:
  "coll (LCons (Mint t') inps) t = coll inps t"
  by (auto simp add: coll_def list_of_LCons_conv)

lemma coll_append[simp]:
  "coll (llist_of (xs @ ys)) t = coll (llist_of xs) t @ coll (llist_of ys) t"
  apply (simp add: coll_def)
  done

lemma coll_lshift:
  "lfinite (lfilter (\<lambda>e. event.time e = t) inps) \<Longrightarrow>
   coll (xs @@- inps) t = coll (llist_of xs) t @ coll inps t"
  apply (induct xs arbitrary: inps rule: rev_induct)
  apply (simp add: coll_def)
  subgoal for x xs inps
    apply (cases x)
    apply (auto simp add: coll_LCons_Data split: event.splits)
    done
  done


lemma ts_Mint[simp]:
  "ts (LCons (Mint t) inps) = ts inps"
  unfolding  ts_def
  apply (auto split: event.splits)
  apply (metis cinsertE cinsert_code event.inject(1) event.simps(4,6))
  apply (metis cinsert_code cinsert_iff event.inject(1) event.simps(4,6))
  done

lemma ts_Data[simp]:
  "ts (LCons (Data t d) inps) = cinsert t (ts inps)"
  unfolding  ts_def
  apply (auto split: event.splits)
  apply (metis cinsertE cinsert_code event.disc(1) event.inject(1))
  apply (metis cinsert_code cinsert_iff event.inject(1) event.simps(4,7))
  apply (metis cinsert_code cinsert_iff event.inject(1) event.simps(4,7))
  done

lemma ts_Drop[simp]:
  "ts (LCons (Drop t) inps) = ts inps"
  unfolding  ts_def
  apply (auto split: event.splits)
  apply (metis cinsertE cinsert_code event.inject(1) event.simps(4,6))
  apply (metis cinsert_code cinsert_iff event.inject(1) event.simps(5,7))
  done

lemma ts_LNil[simp]:
  "ts LNil = {||}"
  unfolding  ts_def
  by (auto simp add: cset_of_llist.rep_eq split: event.splits)

end
