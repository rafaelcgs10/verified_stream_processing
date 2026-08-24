theory Labels

imports
  Loop
  Input0
begin










lemma label_prop_upd_inv_loop_updatesI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>label_prop_upd_inv os_label_prop'\<close>
  using step INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(2) "1.prems"(4)])
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (subst loop_updates.simps) (use good step1 True in simp)
    show ?thesis
      using "1.prems"(1) loop_eq INV1 by simp
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      by (subst loop_updates.simps) (use good step1 False in simp)
    have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
      using "1.prems"(1) loop_eq by simp
    have LABELS1: \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
      by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(2) "1.prems"(4) "1.prems"(3)])
    have input1_empty: \<open>input os_label_prop1 1 = []\<close>
      by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
    have wf1_msgs:
      \<open>wf_label_prop_updates os_label_prop1
        (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      by (rule label_prop_input1_loop_updates_msgs_invI
          [OF step1[symmetric] "1.prems"(5) "1.prems"(6) "1.prems"(2) "1.prems"(3) "1.prems"(4)])
    have WF1: \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      using input1_empty wf1_msgs by simp
    have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
      using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(5) by simp
    have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
      using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(6) by simp
    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False step_rec INV1 LABELS1 WF1 EN1_1 DE1_1])
  qed
qed
subsection \<open>Auxiliary label-invariant preservation for correctness proof\<close>


lemma labels_inv_loop_updates_allI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>\<forall>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
  using step INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(2) "1.prems"(4)])
  have LABELS1:
    \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(2) "1.prems"(4) "1.prems"(3)])
  have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
    using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(5)
    by simp
  have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
    using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(6)
    by simp
  have input1_empty: \<open>input os_label_prop1 (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have WF1_msgs:
    \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(5) "1.prems"(6) "1.prems"(2) "1.prems"(3) "1.prems"(4)])
  have WF1:
    \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    using WF1_msgs input1_empty by simp
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (subst loop_updates.simps) (use good step1 True in simp)
    show ?thesis
      using "1.prems"(1) loop_eq LABELS1 by simp
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      by (subst loop_updates.simps) (use good step1 False in simp)
    have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
      using "1.prems"(1) loop_eq by simp
    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False step_rec INV1 LABELS1 WF1 EN1_1 DE1_1])
  qed
qed


lemma wf_label_prop_updates_clean_image[simp]:
  \<open>wf_label_prop_updates os ((\<lambda>(d, t). (d, t -+- MyPair 0 g)) ` S) \<longleftrightarrow>
   wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def
  by auto

(* TODO: Move. *)

lemma label_prop_label_batch_cc_of_all_edges:
  assumes \<open>(updated_os :: (_, nat, nat, nat) label_propagation_state) = label_prop_label_record_update (input_tl old_os 1) (myfst t) vertex assigned_label\<close>
    \<open>batch = label_prop_label_batch old_os updated_os (myfst t) vertex assigned_label t\<close>
    \<open>en1 old_os = Inl\<close> \<open>de1 old_os = projl\<close> \<open>label_prop_upd_inv old_os\<close> \<open>(d, cap) \<in> set batch\<close>
    \<open>myfst (capability.time cap) \<le> t'\<close> \<open>(v, w) = de1 old_os d\<close>
    \<open>\<forall>t. labels_inv (all_edges updated_os t) (min_label updated_os t)\<close>
    \<open>assigned_label = min (min_label old_os (myfst t) vertex) l\<close>
    \<open>vertex \<in> edge_vertices (all_edges updated_os (myfst t))\<close>
  shows \<open>w \<in> cc_of (all_edges old_os t') v\<close>
proof -
  let ?t0 = \<open>myfst (capability.time cap)\<close>
  have myfst_t_t': \<open>myfst t \<le> t'\<close> using assms(2-4,6,7)
    by (force simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
  have w_assigned_label: \<open>w = assigned_label\<close> using assms(2-4,6,8)
    by (force simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
  have \<open>v \<in> set (neighbors old_os ?t0 vertex)\<close>
    using assms(2-4,6,8)
    by (force simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
  hence \<open>reachable (all_edges updated_os ?t0) vertex v\<close>
    using neighbors_reachable[OF assms(5)] by (simp add: assms(1))
  hence reachable_vertex_v: \<open>reachable (all_edges updated_os t') vertex v\<close>
    using all_edges_mono[OF assms(7)] reachable_subset by metis
  have \<open>min_label updated_os (myfst t) vertex = assigned_label\<close>
  proof -
    let ?A = \<open>(\<lambda>t'. label updated_os t' vertex) ` {t' \<in> set (timestamps updated_os). t' \<le> myfst t}\<close>
    have \<open>\<forall>l \<in> ?A. assigned_label \<le> l\<close>
      by (simp add: assms(1,10) label_prop_label_record_update_def)
        (insert min_label_le_current_labelI min_label_mono_time  le_trans min.coboundedI1, blast)
    then show ?thesis using Min_insert2[where a=assigned_label and A=\<open>?A\<close>] unfolding min_label_def
      by (force simp add: assms(1) label_prop_label_record_update_def)
  qed
  hence \<open>assigned_label \<in> cc_of (all_edges updated_os (myfst t)) vertex\<close>
    using assms(9,11) unfolding labels_inv_def by fast
  moreover have \<open>all_edges updated_os (myfst t) \<subseteq> all_edges updated_os t'\<close>
    by (rule all_edges_mono[OF myfst_t_t'])
  ultimately have \<open>assigned_label \<in> cc_of (all_edges updated_os t') vertex\<close> using cc_of_mono by blast
  hence \<open>assigned_label \<in> cc_of (all_edges updated_os t') v\<close>
    using cc_of_eq_if_reachable[OF reachable_vertex_v] by blast
  thus ?thesis by (simp add: assms(1) w_assigned_label)
qed


definition label_prop_covered_inv where
  \<open>label_prop_covered_inv os msgs \<longleftrightarrow>
    (\<forall> t \<in> set (timestamps os). \<forall> a b.
      (a, b) \<in> all_edges os t \<union> (all_edges os t)\<inverse> \<longrightarrow>
      \<not> min_label os t a \<le> min_label os t b \<longrightarrow>
      (\<exists> s t' l'. (Inl (a, l'), MyPair s t') \<in> msgs \<and> s \<le> t \<and> l' \<le> min_label os t b))\<close>




lemma label_prop_covered_inv_produces[simp]:
  "label_prop_covered_inv (produces os batch) M = label_prop_covered_inv os M"
  unfolding label_prop_covered_inv_def all_edges_def all_vertices_def neighbors_def min_label_def produces_def
  by simp


lemma label_prop_covered_inv_add_caps[simp]:
  "label_prop_covered_inv (add_caps os caps) M = label_prop_covered_inv os M"
  unfolding label_prop_covered_inv_def all_edges_def all_vertices_def neighbors_def min_label_def add_caps_def
  by simp


lemma label_prop_covered_inv_drop_caps[simp]:
  "label_prop_covered_inv (drop_caps os caps) M = label_prop_covered_inv os M"
  unfolding label_prop_covered_inv_def all_edges_def all_vertices_def neighbors_def min_label_def drop_caps_def
  by simp


lemma label_prop_covered_inv_release_caps[simp]:
  "label_prop_covered_inv (release_caps os p) M = label_prop_covered_inv os M"
  unfolding release_caps_def Let_def by simp





lemma label_prop_covered_inv_msgs_transportI:
  assumes "label_prop_covered_inv os M"
    and "\<And>a l' t t'. (Inl (a, l'), MyPair t t') \<in> M \<Longrightarrow> \<exists>t''. (Inl (a, l'), MyPair t t'') \<in> M'"
  shows "label_prop_covered_inv os M'"
  using assms unfolding label_prop_covered_inv_def by fast


lemma label_prop_covered_inv_cong:
  "timestamps os' = timestamps os \<Longrightarrow> graph os' = graph os \<Longrightarrow>
   vertices os' = vertices os \<Longrightarrow> label os' = label os \<Longrightarrow> M' = M \<Longrightarrow>
   label_prop_covered_inv os' M' = label_prop_covered_inv os M"
  unfolding label_prop_covered_inv_def all_edges_def all_vertices_def neighbors_def min_label_def
  by simp


lemma label_prop_covered_inv_transportI:
  assumes "label_prop_covered_inv os M"
    and "timestamps os' = timestamps os" "graph os' = graph os"
    and "vertices os' = vertices os" "label os' = label os"
    and "\<And>a l' t t'. (Inl (a, l'), MyPair t t') \<in> M \<Longrightarrow> \<exists>t''. (Inl (a, l'), MyPair t t'') \<in> M'"
  shows "label_prop_covered_inv os' M'"
  apply (subst label_prop_covered_inv_cong[OF assms(2-5) refl])
  apply (rule label_prop_covered_inv_msgs_transportI[OF assms(1)])
  by (rule assms(6))


lemma label_prop_covered_inv_consumes[simp]:
  "label_prop_covered_inv (consumes os p t d) M = label_prop_covered_inv os M"
  unfolding consumes_def
  apply (subst label_prop_covered_inv_add_caps)
  apply (rule label_prop_covered_inv_cong)
  by simp_all





lemma min_label_record_update_le:
  fixes t1 t' :: "'t::order"
  assumes "t1 \<in> set (timestamps os)" "t1 \<le> t'"
  shows "min_label (label_prop_label_record_update os t1 v new_l) t' v \<le> new_l"
proof -
  let ?upd = "label_prop_label_record_update os t1 v new_l"
  have "new_l \<in> (\<lambda>s. label ?upd s v) ` {s \<in> set (timestamps ?upd). s \<le> t'}"
    using assms by (force simp add: label_prop_label_record_update_def)
  then show ?thesis
    unfolding min_label_def by (intro Min_le) auto
qed


lemma violated_edge_label_record_updateD:
  fixes t1 t' :: "'t::{order,plus}"
  assumes viol: "\<not> min_label (label_prop_label_record_update os' t1 v new_l) t' a
      \<le> min_label (label_prop_label_record_update os' t1 v new_l) t' b"
    and edge: "(a, b) \<in> all_edges os' t' \<union> (all_edges os' t')\<inverse>"
    and ts_eq: "timestamps os' = timestamps os"
    and graph_eq: "graph os' = graph os"
    and vertices_eq: "vertices os' = vertices os"
    and label_eq: "label os' = label os"
    and t'_ts: "t' \<in> set (timestamps os)"
    and dec: "new_l \<le> label os t1 v"
    and sym_graph: "\<And>s. sym {(x, y). y \<in> set (graph os s x)}"
  shows "((a, b) \<in> all_edges os t' \<union> (all_edges os t')\<inverse> \<and>
      \<not> min_label os t' a \<le> min_label os t' b \<and>
      min_label (label_prop_label_record_update os' t1 v new_l) t' b = min_label os t' b)
    \<or> ((en1 os (a, new_l), Cap (MyPair t' (mysnd et)) (1 :: 2))
        \<in> set (label_prop_label_batch os (label_prop_label_record_update os' t1 v new_l) t1 v new_l et) \<and>
      min_label (label_prop_label_record_update os' t1 v new_l) t' b = new_l)"
proof -
  let ?upd = "label_prop_label_record_update os' t1 v new_l"
  let ?E = "all_edges os t'"
  define A where "A = {s \<in> set (timestamps os). s \<le> t'}"
  have finA: "finite A"
    unfolding A_def by simp
  have lab_u: "label ?upd = (label os)(t1 := (label os t1)(v := new_l))"
    using label_eq by (simp add: label_prop_label_record_update_def)
  have ts_u: "timestamps ?upd = timestamps os"
    using ts_eq by (simp add: label_prop_label_record_update_def)
  have all_vertices_eq: "all_vertices os' t' = all_vertices os t'"
    unfolding all_vertices_def using ts_eq vertices_eq by simp
  have neighbors_eq: "\<And>w. set (neighbors os' t' w) = set (neighbors os t' w)"
    unfolding set_neighbors using ts_eq graph_eq by simp
  have all_edges_eq: "all_edges os' t' = all_edges os t'"
    unfolding all_edges_def using all_vertices_eq neighbors_eq by auto
  have minl: "min_label os t' w = Min (insert (label os t' w) ((\<lambda>s. label os s w) ` A))" for w
    by (simp add: min_label_def A_def)
  have minl_u: "min_label ?upd t' w = Min (insert (label ?upd t' w) ((\<lambda>s. label ?upd s w) ` A))" for w
    by (simp add: min_label_def A_def ts_u ts_eq)
  have upd_other: "min_label ?upd t' w = min_label os t' w" if wv: "w \<noteq> v" for w
  proof -
    have "label ?upd s w = label os s w" for s
      using wv by (simp add: lab_u)
    then show ?thesis
      by (simp add: minl minl_u)
  qed
  have upd_v_le: "min_label ?upd t' v \<le> min_label os t' v"
  proof -
    have "Min (insert (label os t' v) ((\<lambda>s. label os s v) ` A)) \<in> insert (label os t' v) ((\<lambda>s. label os s v) ` A)"
      by (intro Min_in) (use finA in auto)
    then consider "Min (insert (label os t' v) ((\<lambda>s. label os s v) ` A)) = label os t' v"
      | s where "s \<in> A" "Min (insert (label os t' v) ((\<lambda>s. label os s v) ` A)) = label os s v"
      by blast
    then show ?thesis
    proof cases
      case 1
      have "min_label ?upd t' v \<le> label ?upd t' v"
        unfolding minl_u by (intro Min_le) (use finA in auto)
      also have "label ?upd t' v \<le> label os t' v"
        using dec by (auto simp add: lab_u)
      finally show ?thesis
        using 1 minl by simp
    next
      case (2 s)
      have "min_label ?upd t' v \<le> label ?upd s v"
        unfolding minl_u by (intro Min_le) (use finA 2 in auto)
      also have "label ?upd s v \<le> label os s v"
        using dec by (auto simp add: lab_u)
      finally show ?thesis
        using 2 minl by simp
    qed
  qed
  have le_upd_v: "c \<le> min_label ?upd t' v" if c_new: "c \<le> new_l" and c_old: "c \<le> min_label os t' v" for c
  proof -
    have le_all: "c \<le> bb" if b_in: "bb \<in> insert (label ?upd t' v) ((\<lambda>s. label ?upd s v) ` A)" for bb
    proof -
      from b_in have "bb = new_l \<or> bb \<in> insert (label os t' v) ((\<lambda>s. label os s v) ` A)"
        by (auto simp add: lab_u split: if_splits)
      then show ?thesis
      proof
        assume "bb = new_l"
        then show ?thesis using c_new by simp
      next
        assume "bb \<in> insert (label os t' v) ((\<lambda>s. label os s v) ` A)"
        then have "min_label os t' v \<le> bb"
          unfolding minl by (intro Min_le) (use finA in auto)
        then show ?thesis using c_old by simp
      qed
    qed
    show ?thesis
      unfolding minl_u
      by (auto simp add: finA intro: le_all)
  qed
  have upd_v_eq: "min_label ?upd t' v = min_label os t' v" if t1A: "t1 \<notin> A"
  proof -
    have t1t': "t' \<noteq> t1"
      using t1A t'_ts unfolding A_def by auto
    have "(\<lambda>s. label ?upd s v) ` A = (\<lambda>s. label os s v) ` A"
      using t1A by (intro image_cong refl) (auto simp add: lab_u)
    moreover have "label ?upd t' v = label os t' v"
      using t1t' by (auto simp add: lab_u)
    ultimately show ?thesis
      by (simp add: minl minl_u)
  qed
  have upd_le_new: "min_label ?upd t' v \<le> new_l" if t1A: "t1 \<in> A"
  proof -
    have "new_l \<in> (\<lambda>s. label ?upd s v) ` A"
      using t1A by (force simp add: lab_u)
    then show ?thesis
      unfolding minl_u by (intro Min_le) (use finA in auto)
  qed
  have upd_v_min: "min_label ?upd t' v = min new_l (min_label os t' v)" if t1A: "t1 \<in> A"
  proof (rule antisym)
    show "min_label ?upd t' v \<le> min new_l (min_label os t' v)"
      using upd_le_new[OF t1A] upd_v_le by simp
    show "min new_l (min_label os t' v) \<le> min_label ?upd t' v"
      by (rule le_upd_v) simp_all
  qed
  have nb_sym: "x \<in> set (neighbors os t' y)" if "y \<in> set (neighbors os t' x)" for x y
    using that sym_graph[unfolded sym_def] unfolding set_neighbors by fastforce
  have E_sym: "(y, x) \<in> ?E" if "(x, y) \<in> ?E" for x y
    using that nb_sym unfolding all_edges_def by auto
  have edge_os: "(a, b) \<in> ?E \<union> ?E\<inverse>"
    using edge all_edges_eq by simp
  have ab: "a \<noteq> b"
    using viol by auto
  show ?thesis
  proof (cases "b = v")
    case False
    then have b_eq: "min_label ?upd t' b = min_label os t' b"
      by (rule upd_other)
    have viol_os: "\<not> min_label os t' a \<le> min_label os t' b"
    proof (cases "a = v")
      case True
      show ?thesis
      proof
        assume "min_label os t' a \<le> min_label os t' b"
        then have "min_label ?upd t' a \<le> min_label os t' b"
          using True upd_v_le by (metis order_trans)
        then show False
          using viol b_eq by simp
      qed
    next
      case False
      then show ?thesis
        using viol b_eq upd_other[OF False] by simp
    qed
    show ?thesis
      using edge_os viol_os b_eq by blast
  next
    case bv: True
    then have av: "a \<noteq> v"
      using ab by simp
    have a_eq: "min_label ?upd t' a = min_label os t' a"
      by (rule upd_other[OF av])
    show ?thesis
    proof (cases "t1 \<in> A")
      case False
      have b_eq: "min_label ?upd t' b = min_label os t' b"
        using upd_v_eq[OF False] bv by simp
      have viol_os: "\<not> min_label os t' a \<le> min_label os t' b"
        using viol a_eq b_eq by simp
      show ?thesis
        using edge_os viol_os b_eq by blast
    next
      case t1A: True
      then have v_min: "min_label ?upd t' v = min new_l (min_label os t' v)"
        by (rule upd_v_min)
      show ?thesis
      proof (cases "min_label os t' v \<le> new_l")
        case True
        have b_eq: "min_label ?upd t' b = min_label os t' b"
          using v_min True bv by (simp add: min.absorb2)
        have viol_os: "\<not> min_label os t' a \<le> min_label os t' b"
          using viol a_eq b_eq by simp
        show ?thesis
          using edge_os viol_os b_eq by blast
      next
        case False
        then have nl_lt: "new_l < min_label os t' v"
          by (simp add: not_le)
        have b_new: "min_label ?upd t' b = new_l"
          using v_min nl_lt bv by (simp add: min.absorb1)
        have a_gt: "new_l < min_label os t' a"
          using viol a_eq b_new by (simp add: not_le)
        have t1_le: "t1 \<le> t'"
          using t1A unfolding A_def by simp
        have a_nb: "a \<in> set (neighbors os t' v)"
        proof -
          from edge_os bv have "(a, v) \<in> ?E \<or> (v, a) \<in> ?E"
            by auto
          then have "(v, a) \<in> ?E"
            using E_sym by blast
          then show ?thesis

            unfolding all_edges_def by auto
        qed
        have upd_a_gt: "new_l < min_label ?upd t' a"
          using a_gt a_eq by simp
        have "(en1 os (a, new_l), Cap (MyPair t' (mysnd et)) (1 :: 2))
            \<in> set (label_prop_label_batch os ?upd t1 v new_l et)"
          unfolding label_prop_label_batch_def label_prop_neighbor_batch_def Let_def
          using t'_ts t1_le nl_lt a_nb upd_a_gt by fastforce
        then show ?thesis
          using b_new by blast
      qed
    qed
  qed
qed


lemma label_prop_covered_inv_label_batch_updateI:
  fixes t1 :: "'t::{order,plus}"
  assumes cov: "label_prop_covered_inv os M"
    and ts_eq: "timestamps os' = timestamps os"
    and graph_eq: "graph os' = graph os"
    and vertices_eq: "vertices os' = vertices os"
    and label_eq: "label os' = label os"
    and upd: "label_prop_upd_inv os"
    and en1_eq: "en1 os = Inl"
    and nl: "new_l = min (min_label os t1 v) lh"
    and head_t: "myfst et = t1"
    and headM: "\<And>x. x \<in> M \<Longrightarrow> x = (Inl (v, lh), et) \<or> x \<in> M'"
    and batchM: "\<And>x tm. (x, Cap tm (1 :: 2)) \<in> set (label_prop_label_batch os (label_prop_label_record_update os' t1 v new_l) t1 v new_l et)
      \<Longrightarrow> (x, tm) \<in> M'"
    and t1_ts: "t1 \<in> set (timestamps os)"
  shows "label_prop_covered_inv (label_prop_label_record_update os' t1 v new_l) M'"
  unfolding label_prop_covered_inv_def
proof (intro ballI allI impI)
  let ?upd = "label_prop_label_record_update os' t1 v new_l"
  fix t' a b
  assume t'_in: "t' \<in> set (timestamps ?upd)"
    and edge: "(a, b) \<in> all_edges ?upd t' \<union> (all_edges ?upd t')\<inverse>"
    and viol: "\<not> min_label ?upd t' a \<le> min_label ?upd t' b"
  have ts_upd: "timestamps ?upd = timestamps os"
    by (simp add: label_prop_label_record_update_def ts_eq)
  have t'_ts: "t' \<in> set (timestamps os)"
    using t'_in ts_upd by simp
  have edges_upd: "all_edges ?upd t' = all_edges os' t'"
    unfolding all_edges_def all_vertices_def set_neighbors
    by (simp add: label_prop_label_record_update_def)
  have edge': "(a, b) \<in> all_edges os' t' \<union> (all_edges os' t')\<inverse>"
    using edge edges_upd by simp
  have dec: "new_l \<le> label os t1 v"
    unfolding nl by (rule min.coboundedI1[OF min_label_le_label])
  have sym_graph: "\<And>s. sym {(x, y). y \<in> set (graph os s x)}"
    using upd unfolding label_prop_upd_inv_def by blast
  from violated_edge_label_record_updateD[where et=et, OF viol edge' ts_eq graph_eq vertices_eq label_eq t'_ts dec sym_graph]
  show "\<exists>s t'' l'. (Inl (a, l'), MyPair s t'') \<in> M' \<and> s \<le> t' \<and> l' \<le> min_label ?upd t' b"
  proof (elim disjE conjE)
    assume edge_os: "(a, b) \<in> all_edges os t' \<union> (all_edges os t')\<inverse>"
      and viol_os: "\<not> min_label os t' a \<le> min_label os t' b"
      and b_eq: "min_label ?upd t' b = min_label os t' b"
    obtain s t'' l' where w: "(Inl (a, l'), MyPair s t'') \<in> M"
      and s_le: "s \<le> t'"
      and cover: "l' \<le> min_label os t' b"
      using cov[unfolded label_prop_covered_inv_def] t'_ts edge_os viol_os by blast
    from headM[OF w] show ?thesis
    proof
      assume head: "(Inl (a, l'), MyPair s t'') = (Inl (v, lh), et)"
      then have av: "a = v" and llh: "l' = lh" and tt: "et = MyPair s t''"
        by auto
      have t1s: "t1 = s"
        using head_t tt by simp
      have t1t': "t1 \<le> t'"
        using t1s s_le by simp
      have "min_label ?upd t' a \<le> new_l"
        unfolding av
        by (rule min_label_record_update_le) (simp_all add: ts_eq t1_ts t1t')
      also have "new_l \<le> lh"
        unfolding nl by (rule min.cobounded2)
      also have "lh \<le> min_label ?upd t' b"
        using cover llh b_eq by simp
      finally have "min_label ?upd t' a \<le> min_label ?upd t' b" .
      then show ?thesis
        using viol by simp
    next
      assume "(Inl (a, l'), MyPair s t'') \<in> M'"
      then show ?thesis
        using cover b_eq s_le by auto
    qed
  next
    assume elem: "(en1 os (a, new_l), Cap (MyPair t' (mysnd et)) (1 :: 2))
        \<in> set (label_prop_label_batch os ?upd t1 v new_l et)"
      and b_new: "min_label ?upd t' b = new_l"
    have "(Inl (a, new_l), MyPair t' (mysnd et)) \<in> M'"
      using batchM[OF elem[unfolded en1_eq]] by simp
    then show ?thesis
      using b_new by force
  qed
qed





lemma dataplane_tracker_inv_c_imp_frontier_le:
  fixes sg :: "('nid::{enum,linorder}, 'pid::{enum,linorder}, 't::{order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) subgraph"
    and os :: "'nid \<Rightarrow> ('pid, 'd, 't) operator_state"
    and cbufs :: "'nid \<times> 'pid \<Rightarrow> ('d \<times> 't) buf"
  assumes D: "dataflow_topology (summ sg) (-+-)"
    and R: "reachable_locations (summ sg) = UNIV"
    and P: "propagate_all (summ sg) (pt_tr sg) = Some c"
    and DPI: "dataplane_tracker_inv os cbufs sg"
  shows dataplane_tracker_inv_c_imp_frontier_le_chan:
    "\<And>T nid p s L. T \<in> snd ` set ((outputs_at_target (summ sg) os >> cbufs) (nid, p)) \<Longrightarrow>
      s \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) L \<Longrightarrow>
      frontier_less_equal (frontier (c_imp c L)) (T -+- s)"
    and dataplane_tracker_inv_c_imp_frontier_le_ocaps:
    "\<And>T nid p s L. T \<in> set (ocaps (os nid) p) \<Longrightarrow>
      s \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Src p)) L \<Longrightarrow>
      frontier_less_equal (frontier (c_imp c L)) (T -+- s)"
proof -
  let ?su = "summ sg"
  let ?c0 = "pt_tr sg"
  let ?cgs = "extract_prog Enum.enum (nxt sg) os"
  let ?c'' = "change_multiplicities ?su ?cgs ?c0"
  let ?chns = "outputs_at_target ?su os >> cbufs"
  obtain caps where
    SC: "Src_caps_inv caps os" and
    TC: "Trg_caps_inv caps ?chns" and
    CP: "c_pts_inv ?c'' caps" and
    CH: "chnls_imp_front_inv ?su ?c0 ?chns" and
    PI: "propagation_inv ?su ?c0" and
    EX: "extract_prog_changes_above_impl_inv ?su (nxt sg) ?c0 os"
    using DPI unfolding dataplane_tracker_inv_def by blast
  have FRONT: "frontier (c_imp c L') = ifrontier ?su (-+-) ?c0 L'" for L'
    using Propagates.propagate_all_frontier_c_imp_correctness[OF P D R]
      PI[unfolded propagation_inv_def] by blast
  show "frontier_less_equal (frontier (c_imp c L)) (T -+- s)"
    if T_in: "T \<in> snd ` set (?chns (nid, p))"
      and s_in: "s \<in>\<^sub>A graph.path_weight ?su (Loc nid (Trg p)) L"
    for T nid p s L
  proof -
    have "frontier_less_equal (ifrontier ?su (-+-) ?c0 (Loc nid (Trg p))) T"
      using CH T_in unfolding chnls_imp_front_inv_def by blast
    then have "frontier_less_equal (ifrontier ?su (-+-) ?c0 L) (T -+- s)"
      by (rule frontier_less_equal_ifrontier_trans[OF D s_in])
    then show ?thesis
      unfolding FRONT .
  qed
  have cgs_above: "\<forall>(l, tc, m) \<in> set ?cgs. frontier_less_equal (ifrontier ?su (-+-) ?c0 l) tc"
    using EX
    unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def extract_prog_def
    apply clarsimp
    subgoal for y a aa b
      apply (drule spec[of _ y])
      apply (drule spec[of _ "[]"])
      apply fastforce
      done
    done
  show "frontier_less_equal (frontier (c_imp c L)) (T -+- s)"
    if T_in: "T \<in> set (ocaps (os nid) p)"
      and s_in: "s \<in>\<^sub>A graph.path_weight ?su (Loc nid (Src p)) L"
    for T nid p s L
  proof -
    have "0 < zcount (to_zmset (ocaps (os nid) p)) T"
      using T_in by (simp add: to_zmset_correct)
    then have "0 < zcount (c_pts ?c'' (Loc nid (Src p))) T"
      using SC CP unfolding Src_caps_inv_def c_pts_inv_def by simp
    then have "frontier_less_equal (frontier (c_pts ?c'' (Loc nid (Src p)))) T"
      by (rule frontier_less_equal_zcount_pos)
    then have upper: "frontier_less_equal (ifrontier ?su (-+-) ?c'' L) (T -+- s)"
      using frontier_less_equal_ifrontierI[OF D s_in] by blast
    have "ifrontier ?su (-+-) ?c0 L \<le> ifrontier ?su (-+-) ?c'' L"
      using frontier_less_equal_change_multiplicities[OF D cgs_above] by blast
    then have "frontier_less_equal (ifrontier ?su (-+-) ?c0 L) (T -+- s)"
      using upper by (rule frontier_less_equal_le_trans[rotated])
    then show ?thesis
      unfolding FRONT .
  qed
qed


lemma not_labels_stable_covered_witnessE:
  assumes "\<not> labels_stable (all_edges osl t) (min_label osl t)"
    and "label_prop_covered_inv osl M"
    and "t \<in> set (timestamps osl)"
  obtains a s t' l' where "(Inl (a, l'), MyPair s t') \<in> M" and "s \<le> t"
  using assms unfolding label_prop_covered_inv_def labels_stable_def by fast



(* Auxiliary lemmas for label_prop_covered_inv preservation under edge insertion. *)


lemma min_label_edge_record_update_not_le:
  fixes t1 t' :: "'t::order"
  assumes ts_eq: "timestamps os' = t1 # timestamps os"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(x := l))"
    and not_le: "\<not> t1 \<le> t'"
  shows "min_label os' t' w = min_label os t' w"
proof -
  have set_eq: "{r \<in> set (timestamps os'). r \<le> t'} = {r \<in> set (timestamps os). r \<le> t'}"
    using ts_eq not_le by auto
  have img: "(\<lambda>r. label os' r w) ` {r \<in> set (timestamps os). r \<le> t'}
      = (\<lambda>r. label os r w) ` {r \<in> set (timestamps os). r \<le> t'}"
    by (intro image_cong refl) (use label_eq not_le in auto)
  have lab_cur: "label os' t' w = label os t' w"
    using label_eq not_le by auto
  show ?thesis
    unfolding min_label_def set_eq img lab_cur ..
qed


lemma min_label_edge_record_update_other:
  fixes t1 t' :: "'t::order"
  assumes ts_eq: "timestamps os' = t1 # timestamps os"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(x := l))"
    and inv: "label_prop_upd_inv os"
    and w_neq: "w \<noteq> x"
  shows "min_label os' t' w = min_label os t' w"
proof (cases "t1 \<le> t'")
  case False
  then show ?thesis using assms min_label_edge_record_update_not_le by metis
next
  case True
  have lab_w: "\<And>r. label os' r w = label os r w"
    using label_eq w_neq by simp
  have S'_eq: "insert (label os' t' w) ((\<lambda>r. label os' r w) ` {r \<in> set (timestamps os'). r \<le> t'})
    = insert (label os t1 w) (insert (label os t' w) ((\<lambda>r. label os r w) ` {r \<in> set (timestamps os). r \<le> t'}))"
    using ts_eq True lab_w by auto
  have le1: "min_label os t' w \<le> label os t1 w"
  proof (cases "t1 \<in> set (timestamps os)")
    case True2: True
    then have "label os t1 w \<in> (\<lambda>r. label os r w) ` {r \<in> set (timestamps os). r \<le> t'}"
      using \<open>t1 \<le> t'\<close> by auto
    then show ?thesis unfolding min_label_def by (intro Min_le) auto
  next
    case False2: False
    then have lt1: "label os t1 w = w"
      using inv unfolding label_prop_upd_inv_def by blast
    have "min_label os t' w \<le> label os t' w"
      unfolding min_label_def by (intro Min_le) auto
    also have "label os t' w \<le> w"
      using inv unfolding label_prop_upd_inv_def by blast
    finally show ?thesis using lt1 by simp
  qed
  have "min_label os' t' w = Min (insert (label os t1 w)
      (insert (label os t' w) ((\<lambda>r. label os r w) ` {r \<in> set (timestamps os). r \<le> t'})))"
    unfolding min_label_def using S'_eq by simp
  also have "\<dots> = min (label os t1 w) (min_label os t' w)"
    unfolding min_label_def by (subst Min_insert) auto
  also have "\<dots> = min_label os t' w"
    using le1 by (simp add: min.absorb2)
  finally show ?thesis .
qed


lemma min_label_edge_record_update_chosen:
  fixes t1 t' :: "'t::order"
  assumes ts_eq: "timestamps os' = t1 # timestamps os"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(x := l))"
    and t1_le: "t1 \<le> t'"
    and l_le: "l \<le> min_label os t1 x"
  shows "min_label os' t' x = min l (min_label os t' x)"
proof -
  let ?S' = "insert (label os' t' x) ((\<lambda>r. label os' r x) ` {r \<in> set (timestamps os'). r \<le> t'})"
  let ?S = "insert (label os t' x) ((\<lambda>r. label os r x) ` {r \<in> set (timestamps os). r \<le> t'})"
  have l_lab_t1: "l \<le> label os t1 x"
    using l_le min_label_le_current_labelI[of os t1 x] by (rule order_trans)
  have l_in: "l \<in> ?S'"
  proof -
    have "t1 \<in> set (timestamps os')" using ts_eq by simp
    moreover have "label os' t1 x = l" using label_eq by simp
    ultimately show ?thesis using t1_le by force
  qed
  have upper: "\<And>e. e \<in> ?S \<Longrightarrow> \<exists>e' \<in> ?S'. e' \<le> e"
  proof -
    fix e assume "e \<in> ?S"
    then consider (cur) "e = label os t' x"
      | (st) r where "r \<in> set (timestamps os)" "r \<le> t'" "e = label os r x"
      by auto
    then show "\<exists>e' \<in> ?S'. e' \<le> e"
    proof cases
      case cur
      show ?thesis
      proof (cases "t' = t1")
        case True
        then have "e = label os t1 x" using cur by simp
        then show ?thesis using l_in l_lab_t1 by auto
      next
        case False
        then have "label os' t' x = e" using cur label_eq by simp
        then show ?thesis by force
      qed
    next
      case (st r)
      show ?thesis
      proof (cases "r = t1")
        case True
        then have "e = label os t1 x" using st by simp
        then show ?thesis using l_in l_lab_t1 by auto
      next
        case False
        then have "label os' r x = e" using st label_eq by simp
        moreover have "r \<in> set (timestamps os')" using st ts_eq by simp
        ultimately show ?thesis using st by force
      qed
    qed
  qed
  have lower: "\<And>e'. e' \<in> ?S' \<Longrightarrow> min l (min_label os t' x) \<le> e'"
  proof -
    fix e' assume "e' \<in> ?S'"
    then consider (cur) "e' = label os' t' x"
      | (st) r where "r \<in> set (timestamps os')" "r \<le> t'" "e' = label os' r x"
      by auto
    then show "min l (min_label os t' x) \<le> e'"
    proof cases
      case cur
      show ?thesis
      proof (cases "t' = t1")
        case True
        then have "e' = l" using cur label_eq by simp
        then show ?thesis by simp
      next
        case False
        then have "e' = label os t' x" using cur label_eq by simp
        then have "min_label os t' x \<le> e'"
          unfolding min_label_def by (auto intro: Min_le)
        then show ?thesis by (simp add: min.coboundedI2)
      qed
    next
      case (st r)
      show ?thesis
      proof (cases "r = t1")
        case True
        then have "e' = l" using st label_eq by simp
        then show ?thesis by simp
      next
        case False
        then have e'_eq: "e' = label os r x" using st label_eq by simp
        have "r \<in> set (timestamps os)" using st ts_eq False by simp
        then have "label os r x \<in> (\<lambda>r. label os r x) ` {r \<in> set (timestamps os). r \<le> t'}"
          using st by auto
        then have "min_label os t' x \<le> e'"
          unfolding min_label_def e'_eq by (intro Min_le) auto
        then show ?thesis by (simp add: min.coboundedI2)
      qed
    qed
  qed
  show ?thesis
  proof (rule antisym)
    have le_l: "min_label os' t' x \<le> l"
      using l_in unfolding min_label_def by (intro Min_le) auto
    have min_S_in: "Min ?S \<in> ?S" by (intro Min_in) auto
    obtain e' where e'_in: "e' \<in> ?S'" and e'_le: "e' \<le> Min ?S"
      using upper[OF min_S_in] by blast
    have "min_label os' t' x \<le> e'"
      using e'_in unfolding min_label_def by (intro Min_le) auto
    then have "min_label os' t' x \<le> min_label os t' x"
      using e'_le unfolding min_label_def by (rule order_trans)
    then show "min_label os' t' x \<le> min l (min_label os t' x)"
      using le_l by simp
    show "min l (min_label os t' x) \<le> min_label os' t' x"
      unfolding min_label_def by (intro Min.boundedI) (use lower[unfolded min_label_def] in auto)
  qed
qed


lemma all_edges_edge_record_update_not_le:
  fixes t1 t' :: "'t::order"
  assumes ts_eq: "timestamps os' = t1 # timestamps os"
    and graph_eq: "graph os' = (graph os)(t1 := (graph os t1)(v1 := v2 # graph os t1 v1,
      v2 := v1 # graph os t1 v2))"
    and vertices_eq: "vertices os' = (vertices os)(t1 := [v1, v2] @ vertices os t1)"
    and not_le: "\<not> t1 \<le> t'"
  shows "all_edges os' t' = all_edges os t'"
proof -
  have av: "all_vertices os' t' = all_vertices os t'"
    using ts_eq vertices_eq not_le unfolding all_vertices_def
    by (fastforce split: if_splits)
  have nb: "\<And>v. set (neighbors os' t' v) = set (neighbors os t' v)"
    using ts_eq graph_eq not_le unfolding set_neighbors
    by (fastforce split: if_splits)
  show ?thesis
    unfolding all_edges_def av nb ..
qed


lemma all_edges_edge_record_update_le:
  fixes t1 t' :: "'t::order"
  assumes ts_eq: "timestamps os' = t1 # timestamps os"
    and graph_eq: "graph os' = (graph os)(t1 := (graph os t1)(v1 := v2 # graph os t1 v1,
      v2 := v1 # graph os t1 v2))"
    and vertices_eq: "vertices os' = (vertices os)(t1 := [v1, v2] @ vertices os t1)"
    and inv: "label_prop_upd_inv os"
    and t1_le: "t1 \<le> t'"
  shows "all_edges os' t' = all_edges os t' \<union> {(v1, v2), (v2, v1)}"
proof -
  have vt1: "t1 \<notin> set (timestamps os) \<Longrightarrow> set (vertices os t1) = {}"
    and gt1: "\<And>v. t1 \<notin> set (timestamps os) \<Longrightarrow> graph os t1 v = []"
    using inv label_prop_upd_inv_vertices_timestamps_iff
      label_prop_upd_inv_graph_empty_if_not_timestamp by blast+
  have av: "all_vertices os' t' = insert v1 (insert v2 (all_vertices os t'))"
    using ts_eq vertices_eq t1_le vt1 unfolding all_vertices_def
    by (fastforce split: if_splits)
  have nb: "\<And>v. set (neighbors os' t' v) = set (neighbors os t' v)
      \<union> (if v = v1 then {v2} else {}) \<union> (if v = v2 then {v1} else {})"
    using ts_eq graph_eq t1_le gt1 unfolding set_neighbors
    by (fastforce split: if_splits)
  have nbv: "\<And>v w. w \<in> set (neighbors os t' v) \<Longrightarrow> v \<in> all_vertices os t' \<and> w \<in> all_vertices os t'"
    by (rule label_prop_upd_inv_neighborsD[OF inv])
  show ?thesis
    unfolding all_edges_def av nb using nbv by (auto split: if_splits)
qed


lemma min_label_fresh_collapse:
  fixes t' :: nat
  assumes inv: "label_prop_upd_inv os"
    and fresh: "t' \<notin> set (timestamps os)"
    and ne: "{s \<in> set (timestamps os). s \<le> t'} \<noteq> {}"
    and smax: "s = Max {s \<in> set (timestamps os). s \<le> t'}"
  shows min_label_fresh_collapse_in: "s \<in> set (timestamps os)"
    and min_label_fresh_collapse_le: "s \<le> t'"
    and min_label_fresh_collapse_min_label: "min_label os t' y = min_label os s y"
    and min_label_fresh_collapse_all_edges: "all_edges os t' = all_edges os s"
proof -
  have fin: "finite {s \<in> set (timestamps os). s \<le> t'}"
    by simp
  have s_in_filter: "s \<in> {s \<in> set (timestamps os). s \<le> t'}"
    unfolding smax by (intro Max_in fin ne)
  then show s_in: "s \<in> set (timestamps os)" and s_le: "s \<le> t'"
    by auto
  have filter_eq: "{r \<in> set (timestamps os). r \<le> t'} = {r \<in> set (timestamps os). r \<le> s}"
  proof (intro equalityI subsetI)
    fix r assume "r \<in> {r \<in> set (timestamps os). r \<le> t'}"
    then show "r \<in> {r \<in> set (timestamps os). r \<le> s}"
      using smax fin by (auto intro: Max_ge)
  next
    fix r assume "r \<in> {r \<in> set (timestamps os). r \<le> s}"
    then show "r \<in> {r \<in> set (timestamps os). r \<le> t'}"
      using s_le by auto
  qed
  show "min_label os t' y = min_label os s y"
  proof -
    have cur_t': "label os t' y = y"
      using inv fresh unfolding label_prop_upd_inv_def by blast
    have cur_s_le: "label os s y \<le> y"
      using inv unfolding label_prop_upd_inv_def by blast
    have s_img: "label os s y \<in> (\<lambda>r. label os r y) ` {r \<in> set (timestamps os). r \<le> t'}"
      using s_in s_le by auto
    have "min_label os t' y = Min (insert y ((\<lambda>r. label os r y) ` {r \<in> set (timestamps os). r \<le> t'}))"
      unfolding min_label_def cur_t' ..
    also have "\<dots> = Min ((\<lambda>r. label os r y) ` {r \<in> set (timestamps os). r \<le> t'})"
    proof -
      have le_y: "Min ((\<lambda>r. label os r y) ` {r \<in> set (timestamps os). r \<le> t'}) \<le> y"
        using s_img cur_s_le by (auto intro: order_trans[OF Min_le])
      then show ?thesis
        using s_img by (subst Min_insert) (auto simp add: min.absorb2)
    qed
    also have "\<dots> = Min (insert (label os s y) ((\<lambda>r. label os r y) ` {r \<in> set (timestamps os). r \<le> s}))"
      unfolding filter_eq using s_img[unfolded filter_eq] by (simp add: insert_absorb)
    finally show ?thesis
      unfolding min_label_def .
  qed
  have av_eq: "all_vertices os t' = all_vertices os s"
    unfolding all_vertices_def filter_eq ..
  have nb_eq: "\<And>v. set (neighbors os t' v) = set (neighbors os s v)"
    unfolding set_neighbors using filter_eq by auto
  show "all_edges os t' = all_edges os s"
    unfolding all_edges_def av_eq nb_eq ..
qed



lemma violated_edge_edge_record_updateD:
  fixes t1 t' :: nat
  assumes ts_eq: "timestamps os' = t1 # timestamps os"
    and graph_eq: "graph os' = (graph os)(t1 := (graph os t1)(v1 := v2 # graph os t1 v1,
      v2 := v1 # graph os t1 v2))"
    and vertices_eq: "vertices os' = (vertices os)(t1 := [v1, v2] @ vertices os t1)"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(x := l))"
    and inv: "label_prop_upd_inv os"
    and choice: "(x, l) = (if min_label os t1 v2 < min_label os t1 v1
        then (v1, min_label os t1 v2) else (v2, min_label os t1 v1))"
    and t'_in: "t' \<in> set (timestamps os')"
    and edge: "(a, b) \<in> all_edges os' t' \<union> (all_edges os' t')\<inverse>"
    and viol: "\<not> min_label os' t' a \<le> min_label os' t' b"
  shows "(\<exists>s. s \<in> set (timestamps os) \<and> s \<le> t' \<and>
        (a, b) \<in> all_edges os s \<union> (all_edges os s)\<inverse> \<and>
        \<not> min_label os s a \<le> min_label os s b \<and>
        min_label os s b \<le> min_label os' t' b)
    \<or> (a \<in> set (x # neighbors os' t' x) \<and> t1 \<le> t' \<and>
       fold min (map (min_label os t') (neighbors os' t' x)) (min (min_label os t' x) l)
         \<le> min_label os' t' b \<and>
       fold min (map (min_label os t') (neighbors os' t' x)) (min (min_label os t' x) l)
         < min_label os t' a)"
proof -
  have x_or: "x = v1 \<or> x = v2" and l_le: "l \<le> min_label os t1 x"
    using choice by (auto split: if_splits intro: less_imp_le)
  have ab: "a \<noteq> b"
    using viol by auto
  have other: "\<And>w. w \<noteq> x \<Longrightarrow> min_label os' t' w = min_label os t' w"
    by (rule min_label_edge_record_update_other[OF ts_eq label_eq inv])
  note collapse = min_label_fresh_collapse[OF inv]
  have old_case: "(\<exists>s. s \<in> set (timestamps os) \<and> s \<le> t' \<and>
        (a, b) \<in> all_edges os s \<union> (all_edges os s)\<inverse> \<and>
        \<not> min_label os s a \<le> min_label os s b \<and>
        min_label os s b \<le> min_label os' t' b)"
    if edge_os: "(a, b) \<in> all_edges os t' \<union> (all_edges os t')\<inverse>"
      and viol_os: "\<not> min_label os t' a \<le> min_label os t' b"
      and b_eq: "min_label os t' b \<le> min_label os' t' b"
  proof (cases "t' \<in> set (timestamps os)")
    case True
    then show ?thesis
      using edge_os viol_os b_eq by blast
  next
    case False
    have ne: "{s \<in> set (timestamps os). s \<le> t'} \<noteq> {}"
    proof -
      obtain c d where cd: "(c, d) \<in> all_edges os t'"
        using edge_os by auto
      then have "c \<in> all_vertices os t'"
        unfolding all_edges_def by auto
      then show ?thesis
        unfolding all_vertices_def by auto
    qed
    define s where "s = Max {s \<in> set (timestamps os). s \<le> t'}"
    note c = collapse[OF False ne s_def]
    show ?thesis
      apply (rule exI[of _ s])
      using c(1,2) edge_os viol_os b_eq
      unfolding c(3)[symmetric] c(4)[symmetric] by blast
  qed
  show ?thesis
  proof (cases "t1 \<le> t'")
    case False
    have mins: "\<And>w. min_label os' t' w = min_label os t' w"
      by (rule min_label_edge_record_update_not_le[OF ts_eq label_eq False])
    have edges: "all_edges os' t' = all_edges os t'"
      by (rule all_edges_edge_record_update_not_le[OF ts_eq graph_eq vertices_eq False])
    show ?thesis
      using old_case edge viol unfolding mins edges by blast
  next
    case True
    have edges: "all_edges os' t' = all_edges os t' \<union> {(v1, v2), (v2, v1)}"
      by (rule all_edges_edge_record_update_le[OF ts_eq graph_eq vertices_eq inv True])
    have chosen: "min_label os' t' x = min l (min_label os t' x)"
      by (rule min_label_edge_record_update_chosen[OF ts_eq label_eq True l_le])
    have sym': "\<And>s c d. d \<in> set (graph os' s c) \<Longrightarrow> c \<in> set (graph os' s d)"
      using inv graph_eq unfolding label_prop_upd_inv_def sym_def
      by (auto split: if_splits)
    have nb_sym': "\<And>c d. d \<in> set (neighbors os' t' c) \<Longrightarrow> c \<in> set (neighbors os' t' d)"
      using sym' unfolding set_neighbors by fastforce
    have edge_nb: "\<And>c d. (c, d) \<in> all_edges os' t' \<union> (all_edges os' t')\<inverse> \<Longrightarrow>
        d \<in> set (neighbors os' t' c)"
      using nb_sym' unfolding all_edges_def by auto
    let ?m = "fold min (map (min_label os t') (neighbors os' t' x)) (min (min_label os t' x) l)"
    have m_le_l: "?m \<le> l" and m_le_x: "?m \<le> min_label os t' x"
      using fold_min_le_base[of _ "min (min_label os t' x) l"]
      by (auto intro: order_trans simp add: min.coboundedI1 min.coboundedI2)
    have m_le_nb: "\<And>w. w \<in> set (neighbors os' t' x) \<Longrightarrow> ?m \<le> min_label os t' w"
      by (auto intro: fold_min_le_mem)
    show ?thesis
    proof (cases "b = x")
      case b_x: True
      have a_nx: "a \<noteq> x"
        using ab b_x by simp
      have a_nb: "a \<in> set (neighbors os' t' x)"
        using edge_nb[OF edge[unfolded b_x]] by (rule nb_sym')
      have a_eq: "min_label os' t' a = min_label os t' a"
        by (rule other[OF a_nx])
      have m_le_b: "?m \<le> min_label os' t' b"
        unfolding b_x chosen using m_le_l m_le_x by simp
      have m_lt_a: "?m < min_label os t' a"
      proof -
        have "min_label os' t' b < min_label os' t' a"
          using viol by (simp add: not_le)
        from le_less_trans[OF m_le_b this, unfolded a_eq] show ?thesis .
      qed
      show ?thesis
        using a_nb True m_le_b m_lt_a by simp
    next
      case b_nx: False
      have b_eq: "min_label os' t' b = min_label os t' b"
        by (rule other[OF b_nx])
      show ?thesis
      proof (cases "a = x")
        case a_x: True
        have viol': "\<not> min l (min_label os t' a) \<le> min_label os t' b"
          using viol chosen a_x b_eq by simp
        then have viol_os: "\<not> min_label os t' a \<le> min_label os t' b"
          and l_gt: "\<not> l \<le> min_label os t' b"
          by (auto simp add: min_le_iff_disj)
        consider (old) "(a, b) \<in> all_edges os t' \<union> (all_edges os t')\<inverse>"
          | (new) "(a, b) \<in> {(v1, v2), (v2, v1)}"
          using edge unfolding edges by auto
        then show ?thesis
        proof cases
          case old
          show ?thesis
            using old_case[OF old viol_os] b_eq by auto
        next
          case new
          have b_nb: "b \<in> set (neighbors os' t' x)"
            by (rule edge_nb[OF edge[unfolded a_x]])
          have m_le_b: "?m \<le> min_label os' t' b"
            using m_le_nb[OF b_nb] b_eq by simp
          have m_lt_a: "?m < min_label os t' a"
          proof -
            have "min_label os t' b < min_label os t' a"
              using viol_os by (simp add: not_le)
            from le_less_trans[OF m_le_nb[OF b_nb] this] show ?thesis .
          qed
          show ?thesis
            using True m_le_b m_lt_a a_x by simp
        qed
      next
        case a_nx: False
        have a_eq: "min_label os' t' a = min_label os t' a"
          by (rule other[OF a_nx])
        have viol_os: "\<not> min_label os t' a \<le> min_label os t' b"
          using viol a_eq b_eq by simp
        have edge_old: "(a, b) \<in> all_edges os t' \<union> (all_edges os t')\<inverse>"
          using edge x_or a_nx b_nx unfolding edges by auto
        show ?thesis
          using old_case[OF edge_old viol_os] b_eq by auto
      qed
    qed
  qed
qed


lemma label_prop_covered_inv_edge_batch_updateI:
  fixes t1 :: nat
  assumes cov: "label_prop_covered_inv os M"
    and ts_eq: "timestamps os' = t1 # timestamps os"
    and graph_eq: "graph os' = (graph os)(t1 := (graph os t1)(v1 := v2 # graph os t1 v1,
      v2 := v1 # graph os t1 v2))"
    and vertices_eq: "vertices os' = (vertices os)(t1 := [v1, v2] @ vertices os t1)"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(x := l))"
    and inv: "label_prop_upd_inv os"
    and en1_eq: "en1 os = Inl"
    and choice: "(x, l) = (if min_label os t1 v2 < min_label os t1 v1
        then (v1, min_label os t1 v2) else (v2, min_label os t1 v1))"
    and head_t: "myfst et = t1"
    and monoM: "\<And>y. y \<in> M \<Longrightarrow> y \<in> M'"
    and batchM: "\<And>d tm. (d, Cap tm (1 :: 2)) \<in> set (label_prop_edge_batch os os' t1 x l et)
      \<Longrightarrow> (d, tm) \<in> M'"
  shows "label_prop_covered_inv os' M'"
  unfolding label_prop_covered_inv_def
proof (intro ballI allI impI)
  fix t' a b
  assume t'_in: "t' \<in> set (timestamps os')"
    and edge: "(a, b) \<in> all_edges os' t' \<union> (all_edges os' t')\<inverse>"
    and viol: "\<not> min_label os' t' a \<le> min_label os' t' b"
  from violated_edge_edge_record_updateD[OF ts_eq graph_eq vertices_eq label_eq inv choice
      t'_in edge viol]
  show "\<exists>s t'' l'. (Inl (a, l'), MyPair s t'') \<in> M' \<and> s \<le> t' \<and> l' \<le> min_label os' t' b"
  proof (elim disjE conjE exE)
    fix s
    assume s_in: "s \<in> set (timestamps os)" and s_le: "s \<le> t'"
      and edge_os: "(a, b) \<in> all_edges os s \<union> (all_edges os s)\<inverse>"
      and viol_os: "\<not> min_label os s a \<le> min_label os s b"
      and b_le: "min_label os s b \<le> min_label os' t' b"
    obtain s0 t'' l' where w: "(Inl (a, l'), MyPair s0 t'') \<in> M"
      and s0_le: "s0 \<le> s" and cover: "l' \<le> min_label os s b"
      using cov[unfolded label_prop_covered_inv_def] s_in edge_os viol_os by fast
    have "(Inl (a, l'), MyPair s0 t'') \<in> M'"
      using w by (rule monoM)
    then show ?thesis
      using s0_le s_le cover b_le by (blast intro: order_trans)
  next
    let ?m = "fold min (map (min_label os t') (neighbors os' t' x)) (min (min_label os t' x) l)"
    assume a_in: "a \<in> set (x # neighbors os' t' x)" and t1_le: "t1 \<le> t'"
      and m_le_b: "?m \<le> min_label os' t' b"
      and m_lt_a: "?m < min_label os t' a"
    have t'_batch: "t' \<in> set (filter ((\<le>) t1) (timestamps os'))"
      using t'_in t1_le by simp
    have "(en1 os (a, ?m), Cap (MyPair t' (mysnd et)) (1 :: 2))
        \<in> set (label_prop_edge_batch os os' t1 x l et)"
      unfolding label_prop_edge_batch_def Let_def
      using t'_batch a_in m_lt_a by fastforce
    then have "(Inl (a, ?m), MyPair t' (mysnd et)) \<in> M'"
      using batchM[unfolded en1_eq] by (metis en1_eq)
    then show ?thesis
      using m_le_b by blast
  qed
qed
subsection \<open>Covered-invariant preservation for batched updates\<close>


lemma label_prop_covered_inv_CONSUMES_port1[simp]:
  "label_prop_covered_inv (CONSUMES (1 :: 2) xs os) M = label_prop_covered_inv os M"
  unfolding label_prop_covered_inv_def all_edges_def all_vertices_def neighbors_def min_label_def
  by (simp add: fold_consumes)


lemma label_prop_covered_inv_outpu_update[simp]:
  "label_prop_covered_inv (os\<lparr>outpu := f\<rparr>) M = label_prop_covered_inv os M"
  unfolding label_prop_covered_inv_def all_edges_def all_vertices_def neighbors_def min_label_def
  by simp


lemma label_prop_covered_inv_fst_label_prop_input0_batched_prefixI:
  fixes os :: "(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state"
  assumes input0: "input os 0 = msgs @ rest"
    and EN1: "en1 os = Inl"
    and DE1: "de1 os = projl"
    and INV: "label_prop_upd_inv os"
    and WF_input1: "wf_label_prop_updates os (set (input os 1))"
    and COV: "label_prop_covered_inv os (S \<union> set (outpu os 1))"
  shows "label_prop_covered_inv (fst (label_prop_input0_batched os msgs))
      (S \<union> set (outpu (fst (label_prop_input0_batched os msgs)) 1))"
  using input0 EN1 DE1 INV WF_input1 COV
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: "msg = (d, t)"
    by (cases msg)
  have input_step0: "input os 0 = (d, t) # (msgs @ rest)"
    using Cons.prems(1) msg_eq by simp
  let ?step = "label_prop_input0_step_state os d t"
  obtain v1 v2 where de1_eq: "de1 os d = (v1, v2)"
    by (cases "de1 os d")
  define x where "x = (if min_label os (myfst t) v2 < min_label os (myfst t) v1 then v1 else v2)"
  define l where "l = (if min_label os (myfst t) v2 < min_label os (myfst t) v1
    then min_label os (myfst t) v2 else min_label os (myfst t) v1)"
  have xl: "(x, l) = (if min_label os (myfst t) v2 < min_label os (myfst t) v1
      then (v1, min_label os (myfst t) v2) else (v2, min_label os (myfst t) v1))"
    by (simp add: x_def l_def)
  let ?upd = "label_prop_edge_record_update (input_tl os 0) (myfst t) v1 v2 x l"
  let ?batch = "label_prop_edge_batch os ?upd (myfst t) x l t"
  have step_eq: "?step = release_caps (drop_caps (produces (add_caps ?upd (map snd ?batch))
      ?batch) (map snd ?batch)) 1"
    using de1_eq xl unfolding label_prop_input0_step_state_def Let_def
    by (auto split: prod.splits)
  have batch_step: "label_prop_input0_step_batch os d t = ?batch"
    using de1_eq xl unfolding label_prop_input0_step_batch_def Let_def
    by (auto split: prod.splits)
  have COV_step: "label_prop_covered_inv ?step (S \<union> set (outpu ?step 1))"
    unfolding step_eq
    apply (simp only: label_prop_covered_inv_release_caps label_prop_covered_inv_drop_caps
        label_prop_covered_inv_produces label_prop_covered_inv_add_caps)
    apply (rule label_prop_covered_inv_edge_batch_updateI[where et=t,
          OF Cons.prems(6) _ _ _ _ Cons.prems(4) Cons.prems(2) xl refl])
    apply (simp add: label_prop_edge_record_update_def input_tl_def)
    apply (simp add: label_prop_edge_record_update_def input_tl_def)
    apply (simp add: label_prop_edge_record_update_def input_tl_def)
    apply (simp add: label_prop_edge_record_update_def input_tl_def)
    subgoal for y
      unfolding step_eq[symmetric] by (auto simp add: batch_step)
    subgoal for d' tm
      unfolding step_eq[symmetric] by (force simp add: batch_step)
    done
  have input_rec: "input ?step 0 = msgs @ rest"
    using input_step0 by simp
  have EN1_rec: "en1 ?step = Inl"
    using Cons.prems(2) by simp
  have DE1_rec: "de1 ?step = projl"
    using Cons.prems(3) by simp
  have INV_rec: "label_prop_upd_inv ?step"
    by (rule label_prop_upd_inv_label_prop_input0_step_stateI
        [OF Cons.prems(4) input_step0 Cons.prems(5)])
  have WF_rec: "wf_label_prop_updates ?step (set (input ?step 1))"
    by (rule wf_label_prop_updates_label_prop_input0_step_stateI
        [OF Cons.prems(4) Cons.prems(5)])
  have rec: "label_prop_covered_inv (fst (label_prop_input0_batched ?step msgs))
      (S \<union> set (outpu (fst (label_prop_input0_batched ?step msgs)) 1))"
    by (rule Cons.hyps[OF input_rec EN1_rec DE1_rec INV_rec WF_rec COV_step])
  show ?case
    using rec unfolding msg_eq
    by (cases "label_prop_input0_batched ?step msgs") simp
qed


lemma label_prop_covered_inv_fst_label_prop_input1_batched_prefixI:
  fixes os :: "(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state"
  assumes input1: "input os 1 = msgs @ rest"
    and EN1: "en1 os = Inl"
    and DE1: "de1 os = projl"
    and IS1: "\<forall>(d, u) \<in> set (input os 1). \<exists>v l. d = Inl (v, l)"
    and INV: "label_prop_upd_inv os"
    and WF: "wf_label_prop_updates os (set (input os 1))"
    and COV: "label_prop_covered_inv os (set (input os 1) \<union> set (outpu os 1) \<union> E)"
  shows "label_prop_covered_inv (fst (label_prop_input1_batched os msgs))
      (set rest \<union> set (outpu (fst (label_prop_input1_batched os msgs)) 1) \<union> E)"
  using input1 EN1 DE1 IS1 INV WF COV
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: "msg = (d, t)"
    by (cases msg)
  have input_step1: "input os 1 = (d, t) # (msgs @ rest)"
    using Cons.prems(1) msg_eq by simp
  obtain v l where d_eq: "d = Inl (v, l)"
    using Cons.prems(4) input_step1 by fastforce
  have de1_d: "de1 os d = (v, l)"
    using Cons.prems(3) d_eq by simp
  let ?step = "label_prop_input1_step_state os d t"
  let ?l' = "min (min_label os (myfst t) v) l"
  let ?upd = "label_prop_label_record_update (input_tl os 1) (myfst t) v ?l'"
  let ?batch = "label_prop_label_batch os ?upd (myfst t) v ?l' t"
  have step_eq: "?step = release_caps (drop_caps (produces (add_caps ?upd (map snd ?batch))
      ?batch) (map snd ?batch)) 1"
    using de1_d unfolding label_prop_input1_step_state_def Let_def by simp
  have batch_step: "label_prop_input1_step_batch os d t = ?batch"
    using de1_d unfolding label_prop_input1_step_batch_def Let_def by simp
  have t1_ts: "myfst t \<in> set (timestamps os)"
    using Cons.prems(6) input_step1 unfolding wf_label_prop_updates_def by fastforce
  have COV_step: "label_prop_covered_inv ?step (set (msgs @ rest) \<union> set (outpu ?step 1) \<union> E)"
    unfolding step_eq
    apply (simp only: label_prop_covered_inv_release_caps label_prop_covered_inv_drop_caps
        label_prop_covered_inv_produces label_prop_covered_inv_add_caps)
    apply (rule label_prop_covered_inv_label_batch_updateI[where et=t and lh=l,
          OF Cons.prems(7) _ _ _ _ Cons.prems(5) Cons.prems(2) refl refl _ _ t1_ts])
    apply (simp add: input_tl_def)
    apply (simp add: input_tl_def)
    apply (simp add: input_tl_def)
    apply (simp add: input_tl_def)
    subgoal for y
      unfolding step_eq[symmetric]
      by (fastforce simp add: d_eq input_step1 batch_step)
    subgoal for x tm
      unfolding step_eq[symmetric]
      by (force simp add: batch_step)
    done
  have input_rec: "input ?step 1 = msgs @ rest"
    using input_step1 by simp
  have EN1_rec: "en1 ?step = Inl"
    using Cons.prems(2) by simp
  have DE1_rec: "de1 ?step = projl"
    using Cons.prems(3) by simp
  have IS1_rec: "\<forall>(d, u) \<in> set (input ?step 1). \<exists>v l. d = Inl (v, l)"
    using Cons.prems(4) input_step1 input_rec by (auto simp add: input_step1)
  have INV_rec: "label_prop_upd_inv ?step"
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI
        [OF Cons.prems(5) input_step1 Cons.prems(6)])
  have WF_rec: "wf_label_prop_updates ?step (set (input ?step 1))"
    by (rule wf_label_prop_updates_label_prop_input1_step_stateI
        [OF input_step1 Cons.prems(6)])
  have rec: "label_prop_covered_inv (fst (label_prop_input1_batched ?step msgs))
      (set rest \<union> set (outpu (fst (label_prop_input1_batched ?step msgs)) 1) \<union> E)"
    by (rule Cons.hyps[OF input_rec EN1_rec DE1_rec IS1_rec INV_rec WF_rec COV_step[unfolded input_rec[symmetric]]])
  show ?case
    using rec unfolding msg_eq
    by (cases "label_prop_input1_batched ?step msgs") simp
qed


lemma label_prop_covered_inv_label_prop_input1_loop_updatesI:
  fixes os_label_prop :: "(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state"
    and os :: "3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state"
  assumes step: "(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os"
    and EN1: "en1 os_label_prop = Inl"
    and DE1: "de1 os_label_prop = projl"
    and IS1: "\<forall>(d, u) \<in> set (input os_label_prop 1) \<union>
        set (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)). \<exists>v l. d = Inl (v, l)"
    and INV: "label_prop_upd_inv os_label_prop"
    and WF: "wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))"
    and COV: "label_prop_covered_inv os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))"
  shows "label_prop_covered_inv os_label_prop'
      (set (cbufs' (1, 1) @ outpu (os' 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1)))"
proof -
  let ?msgs = "cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)"
  let ?base = "os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>"
  let ?consumed = "CONSUMES 1 ?msgs ?base"
  let ?full = "input ?consumed 1"
  have os'_eq: "os_label_prop' = fst (label_prop_input1_batched ?consumed ?full)"
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have set_full: "set ?full = set (input os_label_prop 1) \<union> set ?msgs"
    by (auto simp add: input_CONSUMES)
  have out_consumed: "outpu ?consumed 1 = []"
    by (simp add: fold_consumes)
  have wf_base_msgs: "wf_label_prop_updates ?base (set ?msgs)"
    using WF[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_consumed: "label_prop_upd_inv ?consumed"
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF _ wf_base_msgs]) (use INV in simp)
  have wf_consumed: "wf_label_prop_updates ?consumed (set (input ?consumed 1))"
    using WF unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)
  have en1_consumed: "en1 ?consumed = Inl"
    using EN1 by (simp add: fold_consumes)
  have de1_consumed: "de1 ?consumed = projl"
    using DE1 by (simp add: fold_consumes)
  have is1_consumed: "\<forall>(d, u) \<in> set (input ?consumed 1). \<exists>v l. d = Inl (v, l)"
    using IS1 set_full by auto
  have cov_consumed: "label_prop_covered_inv ?consumed
      (set (input ?consumed 1) \<union> set (outpu ?consumed 1) \<union> {})"
    using COV set_full out_consumed by (simp add: Un_commute)
  have cov_result: "label_prop_covered_inv os_label_prop'
      (set ([] :: ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) list)
        \<union> set (outpu os_label_prop' 1) \<union> {})"
    unfolding os'_eq
    by (rule label_prop_covered_inv_fst_label_prop_input1_batched_prefixI[where rest="[]",
          OF _ en1_consumed de1_consumed is1_consumed inv_consumed wf_consumed cov_consumed]) simp
  have cbufs11: "cbufs' (1, 1) = []"
    by (rule label_prop_input1_loop_updates_cbufs_11[OF step])
  have cbufs21: "cbufs' (2, 1) = []"
    by (rule label_prop_input1_loop_updates_cbufs_21[OF step])
  have in_os2: "input (os' 2) 1 = []"
    by (rule label_prop_input1_loop_updates_input_os2_1[OF step])
  have out_os2: "outpu (os' 2) 1 = []"
    by (rule label_prop_input1_loop_updates_outpu_os2_1[OF step])
  show ?thesis
    apply (rule label_prop_covered_inv_msgs_transportI[OF cov_result])
    subgoal for a l' s t'
      apply (rule exI[of _ "t' + Suc 0"])
      apply (simp add: cbufs11 cbufs21 in_os2 out_os2)
      apply (rule image_eqI[where x="(Inl (a, l'), MyPair s t')"])
      apply (simp add: plus_myprod_def)
      apply simp
      done
    done
qed


lemma snd_label_prop_input1_batched_Inl:
  fixes os :: "(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state"
  assumes EN1: "en1 os = Inl"
    and mem: "(d, cap) \<in> set (snd (label_prop_input1_batched os msgs))"
  shows "\<exists>v l. d = Inl (v, l)"
proof -
  obtain pre d_in t_in post os_pre where
    "msgs = pre @ (d_in, t_in) # post"
    and os_pre_eq: "os_pre = fst (label_prop_input1_batched os pre)"
    and step_member: "(d, cap) \<in> set (label_prop_input1_step_batch os_pre d_in t_in)"
    using mem by (elim label_prop_input1_batched_batch_memberD)
  obtain v l l' cur_t v' where de1_pre: "de1 os_pre d_in = (v, l)"
    and l'_def: "l' = min (min_label os_pre (myfst t_in) v) l"
    and cur_t_ts_pre: "cur_t \<in> set (timestamps os_pre)"
    and event_le_cur: "myfst t_in \<le> cur_t"
    and neigh: "v' \<in> set (neighbors os_pre cur_t v)"
    and d_eq: "d = en1 os_pre (v', l')"
    and cap_eq: "cap = Cap (MyPair cur_t (mysnd t_in)) 1"
    using step_member by (elim label_prop_input1_step_batch_member_payloadD)
  have en1_pre: "en1 os_pre = Inl"
    using EN1 os_pre_eq by simp
  show ?thesis
    using d_eq en1_pre by auto
qed


lemma outpu_label_prop_input1_loop_updates_Inl:
  fixes os_label_prop :: "(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state"
    and os :: "3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state"
  assumes step: "(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os"
    and EN1: "en1 os_label_prop = Inl"
  shows "\<forall>(d, u) \<in> set (outpu os_label_prop' 1). \<exists>v l. d = Inl (v, l)"
proof -
  let ?msgs = "cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)"
  let ?base = "os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>"
  let ?consumed = "CONSUMES 1 ?msgs ?base"
  let ?full = "input ?consumed 1"
  have os'_eq: "os_label_prop' = fst (label_prop_input1_batched ?consumed ?full)"
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have out_consumed: "outpu ?consumed 1 = []"
    by (simp add: fold_consumes)
  have outpu_eq: "outpu os_label_prop' 1 =
      map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = 1) (snd (label_prop_input1_batched ?consumed ?full)))"
    using os'_eq out_consumed
    by (simp add: outpu_fst_label_prop_input1_batched_eq)
  have en1_consumed: "en1 ?consumed = Inl"
    using EN1 by (simp add: fold_consumes)
  show ?thesis
    unfolding outpu_eq
    using snd_label_prop_input1_batched_Inl[OF en1_consumed] by fastforce
qed


lemma label_prop_covered_inv_loop_updatesI:
  fixes os_label_prop :: "(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state"
    and os :: "3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state"
    and cbufs :: "3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf"
  assumes step: "(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os"
    and INV: "label_prop_upd_inv os_label_prop"
    and LABELS: "\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)"
    and WF: "wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))"
    and EN1: "en1 os_label_prop = Inl"
    and DE1: "de1 os_label_prop = projl"
    and IS1: "\<forall>(d, u) \<in> set (input os_label_prop 1) \<union>
        set (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)). \<exists>v l. d = Inl (v, l)"
    and COV: "label_prop_covered_inv os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))"
  shows "label_prop_covered_inv os_label_prop'
      (set (cbufs' (1, 1) @ outpu (os' 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1)))"
  using step INV LABELS WF EN1 DE1 IS1 COV
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = "cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)"
  let ?good = "label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)"
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    "label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)"
    by (cases "label_prop_input1_loop_updates cbufs os_label_prop os") auto
  have INV1: "label_prop_upd_inv os_label_prop1"
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(2) "1.prems"(4)])
  have LABELS1: "\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)"
    by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(2) "1.prems"(4) "1.prems"(3)])
  have EN1_1: "en1 os_label_prop1 = Inl"
    using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(5) by simp
  have DE1_1: "de1 os_label_prop1 = projl"
    using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(6) by simp
  have input1_empty: "input os_label_prop1 (1 :: 2) = []"
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have WF1_msgs: "wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))"
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(5) "1.prems"(6) "1.prems"(2) "1.prems"(3) "1.prems"(4)])
  have WF1: "wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))"
    using WF1_msgs input1_empty by simp
  have COV1_msgs: "label_prop_covered_inv os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))"
    by (rule label_prop_covered_inv_label_prop_input1_loop_updatesI
        [OF step1[symmetric] "1.prems"(5) "1.prems"(6) "1.prems"(7) "1.prems"(2) "1.prems"(4) "1.prems"(8)])
  have COV1: "label_prop_covered_inv os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))"
    using COV1_msgs input1_empty by simp
  have Inl_out1: "\<forall>(d, u) \<in> set (outpu os_label_prop1 1). \<exists>v l. d = Inl (v, l)"
    by (rule outpu_label_prop_input1_loop_updates_Inl[OF step1[symmetric] "1.prems"(5)])
  have cbufs11_1: "cbufs1 (1, 1) = []"
    by (rule label_prop_input1_loop_updates_cbufs_11[OF step1[symmetric]])
  have cbufs21_1: "cbufs1 (2, 1) = []"
    by (rule label_prop_input1_loop_updates_cbufs_21[OF step1[symmetric]])
  have in_os2_1: "input (os1 2) 1 = []"
    by (rule label_prop_input1_loop_updates_input_os2_1[OF step1[symmetric]])
  have out_os2_1: "outpu (os1 2) 1 = []"
    by (rule label_prop_input1_loop_updates_outpu_os2_1[OF step1[symmetric]])
  have IS1_1: "\<forall>(d, u) \<in> set (input os_label_prop1 1) \<union>
      set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)). \<exists>v l. d = Inl (v, l)"
    using Inl_out1 input1_empty cbufs11_1 cbufs21_1 in_os2_1 out_os2_1 by auto
  show ?case
  proof (cases "outpu os_label_prop1 1 = []")
    case True
    have loop_eq: "loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)"
      by (subst loop_updates.simps) (use good step1 True in simp)
    show ?thesis
      using "1.prems"(1) loop_eq COV1_msgs by simp
  next
    case False
    have loop_eq: "loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1"
      by (subst loop_updates.simps) (use good step1 False in simp)
    have step_rec: "(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1"
      using "1.prems"(1) loop_eq by simp
    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False step_rec INV1 LABELS1 WF1 EN1_1 DE1_1 IS1_1 COV1])
  qed
qed


end
