theory General

imports
  Dataplane.Timely_Stream
  Dataplane.Timely_Infrastructure
begin


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


definition Src_from_Trg where
  "Src_from_Trg su nid p = {(nid', p'). su (Loc nid' (Src p')) (Loc nid (Trg p)) \<noteq> {}\<^sub>A}"

definition "outputs_at_target su os = (\<lambda> (nid, p). let S = Src_from_Trg su nid p in if S = {} then [] else let (nid', p') = Set.the_elem S in outpu (os nid') p')"
definition "inputs_at_target os = (\<lambda> (nid, p). input (os nid) p)"



lemma outputs_at_target_consumes[simp]:
  "outputs_at_target su (os(nid := consumes (os nid) p' t d)) = outputs_at_target su os"
  unfolding outputs_at_target_def consumes_def Src_from_Trg_def add_caps_def
  apply (rule ext)+
  apply (auto split: if_splits prod.splits)
  done

lemma outputs_at_target_obtain_progress[simp]:
  "outputs_at_target su (os(nid := fst (obtain_progress (os nid)))) = outputs_at_target su os"
  unfolding outputs_at_target_def consumes_def Src_from_Trg_def add_caps_def
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

definition "produ_supported su os c = (\<forall> nid p t m. (p, t, m) \<in> set (produ (os nid)) \<longrightarrow> (zcount (c_pts c (Loc nid (Src p))) t > 0 \<or> (\<exists>m'>0. (p, t, m') \<in> set (inter (os nid)))))"

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
     (produ_supported (summ sg) os c))"


definition "graph_summar_nt su nt os = (
  (\<forall> nid p p' t. t \<in> set (intsum (os nid) p p') \<longrightarrow> (\<exists> t'\<le>t. t' \<in>\<^sub>A graph.path_weight su (Loc nid (Trg p)) (Loc nid (Src p')))) \<and>
  (\<forall> nid nid' p p'. nt (nid', p') = Some (nid, p) \<longrightarrow> 0 \<in>\<^sub>A graph.path_weight su (Loc nid' (Src p')) (Loc nid (Trg p))) \<and>
  (\<forall> nid p p'. distinct (intsum (os nid) p p')) \<and>
  (\<forall> nid p p'. \<forall> t \<in> set (intsum (os nid) p p'). \<not> (\<exists> t' \<in> set (intsum (os nid) p p'). t' < t)) \<and>
  (\<forall> s nid p l. 
      s \<in>\<^sub>A graph.path_weight su (Loc nid (Trg p)) l \<longrightarrow>
      l \<noteq> Loc nid (Trg p) \<longrightarrow> (\<exists> t p' s'. t \<in> set (intsum (os nid) p p') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p')) l \<and> s = t -+- s')) \<and>
  inj_on nt (Map.dom nt) 
  )"

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
  subgoal
    apply (rule zero_in_graph_path_weight)
       apply (rule refl)
      apply (rule dataflow_topology.axioms(1))
      apply (rule dataflow_topology_from_tree.dataflow_topology_axioms)
     apply (auto simp add: comp_def)
    apply (metis assms(2) dataflow_tree_to_graph_Src_Trg_zero) 
    done
  subgoal
      unfolding dataflow_tree_to_graph_def
      apply (simp split: if_splits prod.splits)
      done
    subgoal
      unfolding dataflow_tree_to_graph_def
      apply (fastforce simp add:  incomparable_def split: if_splits prod.splits)
      done
  subgoal for s nid p l
    unfolding comp_def
    using dataflow_tree_to_graph_Trg_decompose 
    by blast
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

end