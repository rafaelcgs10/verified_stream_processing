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
  (\<forall> nid nid' p p'. nt (nid', p') = Some (nid, p) \<longrightarrow> 0 \<in>\<^sub>A su (Loc nid' (Src p')) (Loc nid (Trg p))) \<and>
  (\<forall> nid p p'. distinct (intsum (os nid) p p')) \<and>
  (\<forall> nid p p'. \<forall> t \<in> set (intsum (os nid) p p'). \<not> (\<exists> t' \<in> set (intsum (os nid) p p'). t' < t)) \<and>
  (\<forall> s nid p l. 
      s \<in>\<^sub>A graph.path_weight su (Loc nid (Trg p)) l \<longrightarrow>
      l \<noteq> Loc nid (Trg p) \<longrightarrow> (\<exists> t p' s'. t \<in> set (intsum (os nid) p p') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p')) l \<and> s = t -+- s')) \<and>
  inj_on nt (Map.dom nt) \<and>
  (\<forall> nid p. card (Src_from_Trg su nid p) \<le> 1) 
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


lemma Src_from_Trg_graph_to_nxt_inj_on:
  "\<forall>nid p. Src_from_Trg su nid p = {} \<Longrightarrow>
   inj_on (graph_to_nxt su) (dom (graph_to_nxt su) )"
  unfolding graph_to_nxt_def inj_on_def
  apply clarsimp
    unfolding Src_from_Trg_def
    apply clarsimp
    apply (metis find_SomeD(1) split_conv)
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
      apply (fastforce simp add:  incomparable_def split: if_splits prod.splits)
      done
  subgoal for s nid p l
    unfolding comp_def
    using dataflow_tree_to_graph_Trg_decompose 
    by blast
  subgoal premises prems
    apply (rule Src_from_Trg_graph_to_nxt_inj_on)
    unfolding Src_from_Trg_def
    apply (auto simp add: comp_def dataflow_tree_to_graph_def split: if_splits prod.splits)
    unfolding Src_from_Trg_def
    apply auto
    done
  subgoal premises prems for nid p
    unfolding Src_from_Trg_def
    apply (auto simp add: comp_def dataflow_tree_to_graph_def split: if_splits prod.splits)
    unfolding Src_from_Trg_def
    apply auto
    done
  done

lemma card_leq_1_iff:
  "finite {x. P x} \<Longrightarrow>
   card {x. P x} \<le> 1 \<longleftrightarrow> (\<exists>! x. P x) \<or> (\<forall> x. \<not> P x)"
  apply auto
  subgoal for a b c
    unfolding le_eq_less_or_eq
    apply (rule ccontr)
    apply (auto simp add: card_1_singleton_iff)
    apply (metis mem_Collect_eq singletonD)
    done
  subgoal for x
    unfolding le_eq_less_or_eq
    by (auto 10 10 simp add: card_1_singleton_iff)
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
  apply auto
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

end