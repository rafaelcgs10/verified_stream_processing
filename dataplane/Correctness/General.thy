theory General

imports
  "../Timely_Stream"
  Ifrontier
begin


(* FIXME: move me: zmset and list_diff *)
lemma to_zmset_list_diff[simp]:
  "mset ys \<subseteq># mset xs \<Longrightarrow>
   to_zmset (list_diff xs ys) = to_zmset xs - to_zmset ys"
  apply (induct xs ys rule: list_diff.induct)
   apply clarsimp+
  apply (metis add_zmset_diff_bothsides insert_DiffM insert_subset_eq_iff mset_remove_last to_zmset_correct zmset_of_add_mset)
  done

lemma to_zmset_eq_if_mset_eq:
  "mset xs = mset ys \<Longrightarrow> to_zmset xs = to_zmset ys"
  by (metis to_zmset_correct)

declare cin.rep_eq[simp del]
declare enum_class.enum_UNIV[simp] enum_class.enum_distinct[simp]
declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]


section \<open>Core Dataplane Invariants\<close>
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


section \<open>Target I/O Views and Stability\<close>
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

lemma outputs_at_target_drop_caps[simp]:
  \<open>outputs_at_target su (os(nid := drop_caps (os nid) caps)) = outputs_at_target su os\<close>
  unfolding outputs_at_target_def drop_caps_def
  by (simp add: fun_eq_iff split: if_splits prod.splits)

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
lemma inputs_at_target_outpu_update[simp]:
  "inputs_at_target (map_entry p (outpu_update A) os) = inputs_at_target os"
  unfolding inputs_at_target_def
  by auto

lemma inputs_at_target_drop_caps[simp]:
  \<open>inputs_at_target (os(nid := drop_caps (os nid) caps)) = inputs_at_target os\<close>
  unfolding inputs_at_target_def by (simp add: fun_eq_iff)

section \<open>Typing and Support Side Conditions\<close>
definition "ty1_check os bufs = (\<forall> p. (\<forall> x \<in> fst ` set (input os p) \<union> fst ` set (bufs p) \<union> fst ` set (outpu os p). is_en1 os x))"
definition "ty2_check os bufs = (\<forall> p. (\<forall> x \<in> fst ` set (input os p) \<union> fst ` set (bufs p). is_en1 os x) \<and> (\<forall> x \<in> fst ` set (outpu os p). is_en2 os x))"

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

section \<open>The main invariant connecting the control and data planes\<close>
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


lemma dataplane_tracker_inv_clean:
  "(\<forall> nid. intsum (os nid) = intsum (os' nid) \<and> ocaps (os nid) = ocaps (os' nid) \<and> 
   consu (os nid) = consu (os' nid) \<and> inter (os nid) = inter (os' nid) \<and>
   produ (os nid) = produ (os' nid) \<and> input (os nid) = input (os' nid) \<and>
   outpu (os nid) = outpu (os' nid) \<and> front (os nid) = front (os' nid)) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg"
  unfolding dataplane_tracker_inv_def 
  apply clarsimp
  apply (rule iffI)
  subgoal
    apply clarsimp
    subgoal for caps
      apply (rule exI[of _ caps])
      unfolding propagation_inv_def BULK_BENQ_def  Src_caps_inv_def Trg_caps_inv_def produ_consu_inter_supported_def extract_prog_changes_above_impl_inv_def change_deltas_inv_def front_inv_def c_pts_inv_def chnls_imp_front_inv_def
      by (auto simp add: obtain_progress_def outputs_at_target_def extract_prog_def extract_progress_def split: prod.splits cong: if_cong)
    done
  subgoal
    apply clarsimp
    subgoal for caps
      apply (rule exI[of _ caps])
      unfolding propagation_inv_def BULK_BENQ_def  Src_caps_inv_def Trg_caps_inv_def produ_consu_inter_supported_def extract_prog_changes_above_impl_inv_def change_deltas_inv_def front_inv_def c_pts_inv_def chnls_imp_front_inv_def
      by (auto simp add: obtain_progress_def outputs_at_target_def extract_prog_def extract_progress_def split: prod.splits cong: if_cong)
    done
  done

lemma dataplane_tracker_inv_clean_reorder_ocaps:
  "(\<forall> nid. intsum (os nid) = intsum (os' nid) \<and>
     (\<forall> p. mset (ocaps (os nid) p) = mset (ocaps (os' nid) p)) \<and>
     consu (os nid) = consu (os' nid) \<and> inter (os nid) = inter (os' nid) \<and>
     produ (os nid) = produ (os' nid) \<and> input (os nid) = input (os' nid) \<and>
     outpu (os nid) = outpu (os' nid) \<and> front (os nid) = front (os' nid)) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg"
proof -
  assume eqs: "\<forall> nid. intsum (os nid) = intsum (os' nid) \<and>
     (\<forall> p. mset (ocaps (os nid) p) = mset (ocaps (os' nid) p)) \<and>
     consu (os nid) = consu (os' nid) \<and> inter (os nid) = inter (os' nid) \<and>
     produ (os nid) = produ (os' nid) \<and> input (os nid) = input (os' nid) \<and>
     outpu (os nid) = outpu (os' nid) \<and> front (os nid) = front (os' nid)"
  let ?os0 = "\<lambda>nid. (os' nid)\<lparr>ocaps := ocaps (os nid)\<rparr>"
  have clean_eqs:
    "\<forall>nid. intsum (os nid) = intsum (?os0 nid) \<and> ocaps (os nid) = ocaps (?os0 nid) \<and>
      consu (os nid) = consu (?os0 nid) \<and> inter (os nid) = inter (?os0 nid) \<and>
      produ (os nid) = produ (?os0 nid) \<and> input (os nid) = input (?os0 nid) \<and>
      outpu (os nid) = outpu (?os0 nid) \<and> front (os nid) = front (?os0 nid)"
    using eqs by auto
  have clean:
    "dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv ?os0 cbufs sg"
    using dataplane_tracker_inv_clean[OF clean_eqs] .
  have ocaps_reordered:
    "dataplane_tracker_inv ?os0 cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg"
  proof -
    have zm_eq: "\<And>nid p. to_zmset (ocaps (?os0 nid) p) = to_zmset (ocaps (os' nid) p)"
    proof -
      fix nid p
      have "mset (ocaps (os nid) p) = mset (ocaps (os' nid) p)"
        using eqs by blast
      then have "to_zmset (ocaps (os nid) p) = to_zmset (ocaps (os' nid) p)"
        by (rule to_zmset_eq_if_mset_eq)
      then show "to_zmset (ocaps (?os0 nid) p) = to_zmset (ocaps (os' nid) p)"
        by simp
    qed
    show ?thesis
      using eqs zm_eq
      unfolding dataplane_tracker_inv_def Src_caps_inv_def
        outputs_at_target_def extract_prog_def extract_progress_def obtain_progress_def
        front_inv_def change_deltas_inv_def extract_prog_changes_above_impl_inv_def
        produ_consu_inter_supported_def
      by (auto split: prod.splits cong: if_cong)
  qed
  show "dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg"
    using clean ocaps_reordered by simp
qed
(* Like dataplane_tracker_inv_clean but the `input` field is allowed to differ:
   the invariant does not depend on input directly, only through outputs_at_target
   (which is itself input-invariant). *)
lemma dataplane_tracker_inv_clean_no_input:
  "(\<forall> nid. intsum (os nid) = intsum (os' nid) \<and> ocaps (os nid) = ocaps (os' nid) \<and>
     consu (os nid) = consu (os' nid) \<and> inter (os nid) = inter (os' nid) \<and>
     produ (os nid) = produ (os' nid) \<and>
     outpu (os nid) = outpu (os' nid) \<and> front (os nid) = front (os' nid)) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg"
  unfolding dataplane_tracker_inv_def
  apply clarsimp
  apply (rule iffI)
  subgoal
    apply clarsimp
    subgoal for caps
      apply (rule exI[of _ caps])
      unfolding propagation_inv_def BULK_BENQ_def  Src_caps_inv_def Trg_caps_inv_def produ_consu_inter_supported_def extract_prog_changes_above_impl_inv_def change_deltas_inv_def front_inv_def c_pts_inv_def chnls_imp_front_inv_def
      by (auto simp add: obtain_progress_def outputs_at_target_def extract_prog_def extract_progress_def split: prod.splits cong: if_cong)
    done
  subgoal
    apply clarsimp
    subgoal for caps
      apply (rule exI[of _ caps])
      unfolding propagation_inv_def BULK_BENQ_def  Src_caps_inv_def Trg_caps_inv_def produ_consu_inter_supported_def extract_prog_changes_above_impl_inv_def change_deltas_inv_def front_inv_def c_pts_inv_def chnls_imp_front_inv_def
      by (auto simp add: obtain_progress_def outputs_at_target_def extract_prog_def extract_progress_def split: prod.splits cong: if_cong)
    done
  done

lemma dataplane_tracker_inv_input_tl[simp]:
  "dataplane_tracker_inv (os(nid := input_tl (os nid) p)) cbufs sg \<longleftrightarrow>
   dataplane_tracker_inv os cbufs sg"
  by (rule dataplane_tracker_inv_clean_no_input) auto

section \<open>Invariant connection timestamps in the input buffer and ocaps - not all operators do that!\<close>
definition "input_ocaps_inv os = (\<forall> p p'. \<forall> t \<in> snd ` set (input os p). \<forall> s \<in> set ((intsum os) p p'). t -+- s \<in> set (ocaps os p'))" 

section \<open>Graph Summary and Next-Edge Consistency\<close>
text \<open>This section relates graph summaries, extracted next-edge maps, and operator-local
internal summaries. It also records structural uniqueness assumptions.\<close>

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

(* graph_summar_nt only inspects os through intsum. input_tl, drop_caps, produces and
   add_caps all leave intsum unchanged, so the invariant transfers as a simp rewrite. *)
lemma graph_summar_nt_intsum_cong:
  assumes "\<And>nid. intsum (os' nid) = intsum (os nid)"
  shows "graph_summar_nt su nt os' = graph_summar_nt su nt os"
  unfolding graph_summar_nt_def by (simp add: assms)

lemma graph_summar_nt_input_tl[simp]:
  "graph_summar_nt su nt (os(nid := input_tl (os nid) p)) = graph_summar_nt su nt os"
  by (rule graph_summar_nt_intsum_cong) simp

lemma graph_summar_nt_drop_caps[simp]:
  "graph_summar_nt su nt (os(nid := drop_caps (os nid) caps)) = graph_summar_nt su nt os"
  by (rule graph_summar_nt_intsum_cong) simp

lemma graph_summar_nt_produces[simp]:
  "graph_summar_nt su nt (os(nid := produces (os nid) batch)) = graph_summar_nt su nt os"
  by (rule graph_summar_nt_intsum_cong) simp

lemma graph_summar_nt_add_caps[simp]:
  "graph_summar_nt su nt (os(nid := add_caps (os nid) caps)) = graph_summar_nt su nt os"
  by (rule graph_summar_nt_intsum_cong) simp

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
      by (auto simp add: bi_unique_def enum_class.enum_UNIV is_empty_antichain_iff dest!: find_SomeD' find_SomeD'' split: prod.splits)
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
    apply (cases "dataflow_tree_to_graph_aux 0 dt")
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
  apply (auto 0 0)
   apply (metis in_op_conn_graph_to_nxt_iff mem_antichain_nonempty_alt op_conn.simps option.simps(1) prod.inject)+
  done

lemma graph_to_nxt_Some_alt:
  "graph_summar_nt su (graph_to_nxt su) os \<Longrightarrow>
   su (Loc nid (Src p)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid', p')"
  using graph_to_nxt_Some by (metis ac_eq_iff mem_antichain_nonempty)


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


section \<open>Extracted Progress Decomposition\<close>
text \<open>Decomposition lemmas for `extract_prog` and `change_multiplicities` when isolating
one node update from a list of nodes.\<close>
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


section \<open>Extract Progress Filter Characterizations\<close>
lemma zmset_map_filter_Trg_extract_prog:
  "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog Enum.enum nt os))) = 
   (\<Sum>x\<in>UNIV. zmset (List.map_filter (\<lambda> (p', t, d). case_option None (\<lambda> (nid'', p''). if nid'' = nid \<and> p'' = p then Some (t, d) else None) (nt (x, p'))) (produ (os x))))
     - zmset (map snd (filter (((=) (p :: 'p :: enum)) o fst) (consu (os nid)))) "
  unfolding extract_prog_def extract_progress_def obtain_progress_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits if_splits option.splits)
  apply (subst (1) monoid_add_class.sum_list_distinct_conv_sum_set)
   apply (clarsimp simp add: sum_subtractf uminus_add_conv_diff_mset split_beta filter_map map_filter_def comp_def sum_diff comm_monoid_add_class.sum.distrib enum_class.enum_distinct enum_class.enum_UNIV split: prod.splits if_splits option.splits)+
  apply (subst sum_subtractf_zmultiset)
   apply simp_all
  apply (rule arg_cong2[where f="(-)"])
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
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum nt (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum nt os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply auto
  done

lemma filter_loc_extract_prof_consumes_diff_ports[simp]:
  "p \<noteq> p' \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum nt (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum nt os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply auto
  done

lemma zmset_map_filter_Src_extract_prog[simp]:
  "distinct xs \<Longrightarrow>
   nid \<in> set xs \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p) = l') (extract_prog xs nt os))) = 
   zmset (map snd (filter (((=) (p :: 'p :: enum)) o fst) (inter (os nid)))) "
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (subst conj.commute)
  apply (simp add: List.map_filter_def sum.distrib sum_list_distinct_conv_sum_set flip: filter_filter split: option.splits)+
  done

lemma set_extract_progress_consumesD:
  "(l, t, m) \<in> set (extract_progress nid ed (snd (obtain_progress (consumes (os nid) p t' d)))) \<Longrightarrow>
   (l, t, m) \<in> set (extract_progress nid ed (snd (obtain_progress (os nid)))) \<or> 
   (\<exists> m'. l = Loc nid (Trg p) \<and> m = -1 \<and> t = t') \<or>
   (\<exists> p' s. l = Loc nid (Src p') \<and> m = 1 \<and> t = t' + s \<and> s \<in> set (intsum (os nid) p p'))"
  unfolding extract_progress_def obtain_progress_def
  apply (auto simp add: split_beta image_iff enum_class.enum_UNIV)
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


lemma zmset_filter_extract_progress_Trg_consumes_alt:
  "zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p) = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p) = l) (extract_progress nid nt (snd (obtain_progress (os nid)))))) - {# t #}\<^sub>z"
  unfolding extract_progress_def obtain_progress_def
  apply simp
  by (simp add: add.left_commute update_zmultiset_one(1))
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

section \<open>change_multiplicities and extract_prog\<close>
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
                      inter := operator_state.inter (os nid) @ interr\<rparr>)))) = 
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
                      inter := operator_state.inter (os nid) @ interr\<rparr>))) = 
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
          apply (simp add: Misc.set_map_filter image_iff split_beta split: option.splits prod.splits)
          apply (metis split_pairs)
          done
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


section \<open>Event-Encoding Rewrites\<close>
text \<open>Rewrites that connect event-structured lists with their multiset representations,
used when converting operational traces into multiplicity updates.\<close>


(* FIMXE *)
lemma zmset_map_Drop_Mint:
  "(\<forall> x\<in>set xs. \<not> is_Data x) \<Longrightarrow>
   zmset (map (\<lambda>x. snd (case x of Drop t \<Rightarrow> (p, t, - 1) | Mint t \<Rightarrow> (p, t, 1))) xs) =
   zmset_of (event.time `# filter_mset is_Mint (mset xs)) - zmset_of (event.time `# filter_mset is_Drop (mset xs))"
  apply (induct xs)
   apply (auto simp add: zmset_of_plus split: event.splits)
   apply (metis (no_types, lifting) add_zmset_add_single diff_diff_add update_zmultiset_one(1))
  using update_zmultiset_one(2) apply fastforce
  done

lemma zmset_Data_to_zmset:
  "(\<forall>x\<in>set xs. is_Data x) \<Longrightarrow>
   zmset (map (\<lambda>x. snd (case x of Data t d \<Rightarrow> (p, t, 1))) xs) = to_zmset (map (\<lambda>x. snd (case x of Data t d \<Rightarrow> (Inl d, t))) xs)" 
  apply (induct xs)
   apply (clarsimp split: event.splits prod.splits)+
  using update_zmultiset_one(2) apply fastforce
  done

lemma outputs_at_target_updates[simp]:
  "outputs_at_target su (os(nid := (os nid)\<lparr> inter := A, produ := B, ocaps := C, input := D, inter := E  \<rparr>)) = outputs_at_target su os"
  unfolding outputs_at_target_def
  apply (rule ext)
  apply (auto split: prod.splits if_splits)
  done

lemma graph_to_nxt_not_Ex_op_conn[simp]:
  "graph_to_nxt su (nid, p) = None \<longleftrightarrow>
   \<not> (\<exists> nid' p'. op_conn su (nid, p) (nid', p'))"
  unfolding graph_to_nxt_def
  apply (auto simp add: is_empty_antichain_iff find_None_iff dest!: find_SomeD' split: prod.splits)
  done

lemma extract_prog_front_update[simp]:
  "extract_prog xs ne (map_entry nid (front_update f) os) =
   extract_prog xs ne os"
  unfolding extract_prog_def extract_progress_def obtain_progress_def
  apply (clarsimp simp add: sum_list_zmset if_distrib[of "filter _"] if_distrib[of "map _"] if_distrib[of operator_state.inter] monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat map_concat filter_concat comp_def split_beta c_pts_change_multiplicities  split: option.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply simp
  apply (clarsimp simp add: sum_list_zmset if_distrib[of "filter _"] if_distrib[of "map _"] if_distrib[of operator_state.inter] monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat map_concat filter_concat comp_def split_beta c_pts_change_multiplicities  split: option.splits)
  done


lemma change_multiplicities_map_append_event:
  "change_multiplicities su (map (\<lambda>x. (l, event.time x, 1)) (filter is_Mint xs) @ map (\<lambda>x. (l, event.time x, - 1)) (filter is_Drop xs)) c =
   change_multiplicities su (map (\<lambda>x. (l, snd (case x of Drop t \<Rightarrow> (p, t, - 1) | Mint t \<Rightarrow> (p, t, 1)))) (filter (\<lambda>x. \<not> is_Data x) xs)) c"
  apply (induct xs arbitrary: c)
  subgoal
    by simp
  subgoal for e xs' c
    apply (cases e; simp)
    subgoal for t
      by (smt (verit, del_insts) Cons_eq_appendI change_multiplicities_append change_multiplicities_comm empty_append_eq_id)
    subgoal for t
      by (smt (verit, del_insts) Cons_eq_appendI change_multiplicities_append change_multiplicities_comm empty_append_eq_id)
    done
  done



section \<open>Extra things (FIXME: move them)\<close>
lemma frontier_to_zmset_bots[simp]:
  "frontier (to_zmset bots) = antichain (set bots)"  
  unfolding frontier.abs_eq minimal_antichain_def ac_eq_iff less_eq_antichain_def member_antichain.rep_eq 
  apply clarsimp
  done

(* FIXME: move me  *)
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

lemma set_bots_bot_antichain[simp]:
  "antichain (set bots) \<le> F"  
  unfolding  less_eq_antichain_def member_antichain.rep_eq 
  apply clarsimp
  unfolding bots_class.minimal
  apply clarsimp
  subgoal for t2
    apply (cases "(\<forall>y. \<not> y < t2)")
    subgoal
      by auto
    subgoal
      apply clarsimp
      using bots_class.complete[unfolded bots_class.minimal]
      apply auto
      done
    done
  done

lemma antichain_from_list_bots_antichain_set[simp]:
  "antichain_from_list bots = antichain (set bots)"
  by (metis set_antichain2 dual_order.eq_iff in_antichain_from_list_alt incomparable_bots less_eq_antichain_def set_antichain_antichain_set_bots
      set_bots_bot_antichain)




lemma input_ocaps_inv_release_capsI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (release_caps os p)"
proof -
  let ?M = "concat (map (\<lambda>(p', s). map (((+) s) \<circ> snd) (input os p'))
              (concat (map (\<lambda>p'. map (\<lambda>s. (p', s)) (intsum os p' p)) enum_class.enum)))"
  let ?ts = "list_diff (ocaps os p) ?M"
  have release_eq:
    "release_caps os p = drop_caps os (map (\<lambda>t. Cap t p) ?ts)"
    unfolding release_caps_def Let_def trace_simp by simp
  have ocaps_other:
    "\<And>p'. p' \<noteq> p \<Longrightarrow> ocaps (release_caps os p) p' = ocaps os p'"
    unfolding release_eq drop_caps_def by auto
  have ocaps_p_mset:
    "mset (ocaps (release_caps os p) p) =
       mset (ocaps os p) - mset (list_diff (ocaps os p) ?M)"
    unfolding release_eq drop_caps_def by simp
  show ?thesis
    unfolding input_ocaps_inv_def
  proof (intro allI ballI)
    fix p1 p2 t s
    assume t_in: "t \<in> snd ` set (input (release_caps os p) p1)"
      and s_in: "s \<in> set (intsum (release_caps os p) p1 p2)"
    have t_in': "t \<in> snd ` set (input os p1)"
      using t_in by simp
    have s_in': "s \<in> set (intsum os p1 p2)"
      using s_in by simp
    have orig: "t -+- s \<in> set (ocaps os p2)"
      using inv t_in' s_in' unfolding input_ocaps_inv_def by blast
    show "t -+- s \<in> set (ocaps (release_caps os p) p2)"
    proof (cases "p2 = p")
      case False
      then show ?thesis using orig ocaps_other by simp
    next
      case True
      have plus_eq: "t -+- s = s + t"
        by (simp add: add.commute)
      have in_M: "t -+- s \<in> set ?M"
      proof -
        from t_in' obtain d where d_in: "(d, t) \<in> set (input os p1)"
          by auto
        have p1_enum: "p1 \<in> set enum_class.enum"
          by (simp add: enum_UNIV)
        have pair_in:
          "(p1, s) \<in> set (concat (map (\<lambda>p'. map (\<lambda>s. (p', s)) (intsum os p' p)) enum_class.enum))"
          using p1_enum s_in' True by auto
        have apply_eq: "((+) s \<circ> snd) (d, t) = s + t"
          by simp
        from pair_in apply_eq d_in have "s + t \<in> set ?M"
          by (force simp: image_iff)
        then show ?thesis using plus_eq by simp
      qed
      have count_pos:
        "count (mset (ocaps (release_caps os p) p)) (t -+- s) > 0"
      proof -
        let ?O = "mset (ocaps os p)"
        let ?Mm = "mset ?M"
        have step1: "mset (list_diff (ocaps os p) ?M) = ?O - ?Mm"
          by simp
        have countM: "count ?Mm (t -+- s) > 0"
          using in_M by (simp add: count_greater_zero_iff)
        have countO: "count ?O (t -+- s) > 0"
          using orig True by (simp add: count_greater_zero_iff)
        have "count (?O - (?O - ?Mm)) (t -+- s) > 0"
          using countM countO by simp
        then show ?thesis
          using ocaps_p_mset True step1 by simp
      qed
      then have "t -+- s \<in> set_mset (mset (ocaps (release_caps os p) p))"
        by (simp add: count_greater_zero_iff)
      then show ?thesis
        using True by simp
    qed
  qed
qed

lemma input_ocaps_inv_produces[simp]:
  "input_ocaps_inv (produces os batch) = input_ocaps_inv os"
  unfolding produces_def input_ocaps_inv_def
  by auto

(* add_caps only enlarges ocaps (and leaves input/intsum untouched),
   so any required witness remains present. *)

lemma inputs_ocaps_inv_consumes:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (consumes os p t d)\<close>
  unfolding input_ocaps_inv_def
proof (intro allI ballI)
  fix p1 p2 t1 s
  assume t1: \<open>t1 \<in> snd ` set (input (consumes os p t d) p1)\<close>
    and \<open>s \<in> set (intsum (consumes os p t d) p1 p2)\<close>
  hence s: \<open>s \<in> set (intsum os p1 p2)\<close> unfolding consumes_def add_caps_def by simp
  consider (input) \<open>t1 \<in> snd ` set (input os p1)\<close> | (consumed) \<open>p1 = p\<close> \<open>t1 = t\<close>
    using t1 unfolding consumes_def add_caps_def BENQ_def by (auto split: if_splits)
  thus \<open>t1 -+- s \<in> set (ocaps (consumes os p t d) p2)\<close>
  proof cases
    case input
    thus ?thesis using assms s unfolding input_ocaps_inv_def consumes_def add_caps_def by auto
  next
    case consumed
    thus ?thesis using s unfolding consumes_def add_caps_def by force
  qed
qed

(* Adding and then dropping the same caps leaves ocaps unchanged (as multisets,
   hence as sets); input and intsum are untouched throughout, so input_ocaps_inv
   transfers directly. *)
lemma input_ocaps_inv_drop_produces_add_capsI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (drop_caps (produces (add_caps os caps) batch) caps)"
  unfolding input_ocaps_inv_def
proof (intro allI ballI)
  fix p1 p2 t s
  assume t_in: "t \<in> snd ` set (input (drop_caps (produces (add_caps os caps) batch) caps) p1)"
    and s_in: "s \<in> set (intsum (drop_caps (produces (add_caps os caps) batch) caps) p1 p2)"
  have t_in': "t \<in> snd ` set (input os p1)"
    using t_in unfolding drop_caps_def produces_def add_caps_def by simp
  have s_in': "s \<in> set (intsum os p1 p2)"
    using s_in unfolding drop_caps_def produces_def add_caps_def by simp
  have orig: "t -+- s \<in> set (ocaps os p2)"
    using inv t_in' s_in' unfolding input_ocaps_inv_def by blast
  have ocaps_mset:
    "mset (ocaps (drop_caps (produces (add_caps os caps) batch) caps) p2) = mset (ocaps os p2)"
    unfolding drop_caps_def produces_def add_caps_def by simp
  then have set_eq:
    "set (ocaps (drop_caps (produces (add_caps os caps) batch) caps) p2) = set (ocaps os p2)"
    by (metis set_mset_mset)
  show "t -+- s \<in> set (ocaps (drop_caps (produces (add_caps os caps) batch) caps) p2)"
    using orig set_eq by simp
qed

(* input_tl only drops the head of input os p; the remaining input is a subset of
   the original. intsum and ocaps are untouched, so any witness for an element
   still present transfers. *)
lemma input_ocaps_inv_input_tlI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (input_tl os p)"
  unfolding input_ocaps_inv_def
proof (intro allI ballI)
  fix p1 p2 t s
  assume t_in: "t \<in> snd ` set (input (input_tl os p) p1)"
    and s_in: "s \<in> set (intsum (input_tl os p) p1 p2)"
  have t_in': "t \<in> snd ` set (input os p1)"
    using t_in unfolding input_tl_def
    by (auto split: if_splits dest: in_set_tlD)
  have s_in': "s \<in> set (intsum os p1 p2)"
    using s_in unfolding input_tl_def by simp
  have orig: "t -+- s \<in> set (ocaps os p2)"
    using inv t_in' s_in' unfolding input_ocaps_inv_def by blast
  show "t -+- s \<in> set (ocaps (input_tl os p) p2)"
    using orig unfolding input_tl_def by simp
qed



lemma input_ocaps_inv_CONSUMES:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (CONSUMES p xs os)\<close>
  using assms
  by (induct xs arbitrary: os) (auto simp add: inputs_ocaps_inv_consumes split: prod.splits)

lemma ocaps_CONSUMES_other_port:
  fixes os :: \<open>('p :: enum, 'd, 't :: plus) operator_state\<close>
  assumes \<open>intsum os p p' = []\<close>
  shows \<open>ocaps (CONSUMES p xs os) p' = ocaps os p'\<close>
  using assms
proof (induct xs arbitrary: os)
  case Nil
  thus ?case unfolding fold_consumes by simp
next
  case (Cons x xs)
  obtain d t where x_eq: \<open>x = (d, t)\<close> by (cases x)
  let ?os' = \<open>consumes os p t d\<close>
  have intsum_step: \<open>intsum ?os' p p' = intsum os p p'\<close>
    unfolding consumes_def add_caps_def by simp
  have empty_filter: \<open>\<And>p''. filter (\<lambda>cap. out cap = p')
        (map (\<lambda>t'. Cap (t + t') p'') (intsum os p p'')) = []\<close>
  proof -
    fix p''
    show \<open>filter (\<lambda>cap. out cap = p')
              (map (\<lambda>t'. Cap (t + t') p'') (intsum os p p'')) = []\<close>
    proof (cases \<open>p'' = p'\<close>)
      case True
      thus ?thesis using Cons.prems by (simp add: filter_map comp_def filter_True)
    next
      case False
      thus ?thesis by (simp add: filter_map comp_def filter_False)
    qed
  qed
  have ocaps_step: \<open>ocaps ?os' p' = ocaps os p'\<close>
    unfolding consumes_def add_caps_def
    using empty_filter
    by (simp add: enum_class.enum_UNIV filter_concat)
  have \<open>ocaps (CONSUMES p (x # xs) os) p' = ocaps (CONSUMES p xs ?os') p'\<close>
    unfolding fold_consumes x_eq by simp
  also have \<open>... = ocaps ?os' p'\<close>
    using Cons.hyps Cons.prems intsum_step by simp
  also have \<open>... = ocaps os p'\<close>
    using ocaps_step .
  finally show ?case .
qed

lemma input_ocaps_inv_empty_inputsI:
  assumes \<open>\<forall>p. input os p = []\<close>
  shows \<open>input_ocaps_inv os\<close>
  using assms unfolding input_ocaps_inv_def by simp



end
