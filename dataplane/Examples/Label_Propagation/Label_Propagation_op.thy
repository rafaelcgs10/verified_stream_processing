theory Label_Propagation_op

imports
  "../../Timely/Builder_Op"
  Wcc
begin

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del] 
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]
declare if_cong[cong]
declare list_emb_Nil2[simp del] BULK_BENQ_right_empty[simp del] BULK_BENQ_left_empty[simp del]
  filter_True[simp del] filter_False[simp del]
declare cin.rep_eq[simp del]
declare cin.rep_eq[symmetric, simp]


section \<open>The Label-Propagation State\<close>

text \<open>The operator state record and the graph views used by the
  algorithm.\<close>

record ('d, 'v :: linorder, 't1, 't2) label_propagation_state =
  \<open>(2, 'd, 'v \<times> 'v, 'v set set, ('t1, 't2) myprod) operator_state_ty2\<close> +
  timestamps :: \<open>'t1 list\<close> graph :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v list\<close> vertices :: \<open>'t1 \<Rightarrow> 'v list\<close>
  label :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v\<close>

definition neighbors where
  \<open>neighbors os t v = (let ts = filter ((\<ge>) t) (timestamps os) in
  remdups (concat ((map (\<lambda> t. graph os t v) ts))))\<close>

definition all_vertices where
  \<open>all_vertices os t = ((\<Union>t'\<in>{t' \<in> set (timestamps os). t' \<le> t}. set (vertices os t')))\<close>

definition all_edges where
  \<open>all_edges os t = {(v, w) \<in> (all_vertices os t) \<times> (all_vertices os t). w \<in> set (neighbors os t v)}\<close>

definition min_label where
  \<open>min_label os t v =
    Min (insert (label os t v)
      ((\<lambda>t'. label os t' v) ` {t' \<in> set (timestamps os). t' \<le> t}))\<close>



lemma set_neighbors:
  "set (neighbors os t v) = (\<Union>t'\<in>{t' \<in> set (timestamps os). t' \<le> t}. set (graph os t' v))"
  unfolding neighbors_def
  by simp

section \<open>Update Invariants and Frame Rules\<close>

text \<open>The label_prop_upd_inv and wf_label_prop_updates invariants with
  frame rules for every state field.\<close>

definition label_prop_upd_inv where
  "label_prop_upd_inv os \<longleftrightarrow>
    (\<forall>t. t \<in> set (timestamps os) \<longleftrightarrow>
      edge_vertices {(v, w). w \<in> set (graph os t v)} \<noteq> {}) \<and>
    (\<forall>t. set (vertices os t) = edge_vertices {(v, w). w \<in> set (graph os t v)}) \<and>
    (\<forall>t. sym {(v, w). w \<in> set (graph os t v)}) \<and>
    (\<forall>t v. v \<notin> all_vertices os t \<longrightarrow> label os t v = v) \<and>
    (\<forall>t v. t \<notin> set (timestamps os) \<longrightarrow> label os t v = v) \<and>
    (\<forall>t v. label os t v \<le> v)"

lemma label_prop_upd_inv_intsum_update[simp]:
  "label_prop_upd_inv (os\<lparr>intsum := xs\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_consu_update[simp]:
  "label_prop_upd_inv (os\<lparr>consu := xs\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_inter_update[simp]:
  "label_prop_upd_inv (os\<lparr>inter := xs\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_produ_update[simp]:
  "label_prop_upd_inv (os\<lparr>produ := xs\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_outpu_update[simp]:
  "label_prop_upd_inv (os\<lparr>outpu := xs\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_front_update[simp]:
  "label_prop_upd_inv (os\<lparr>front := xs\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_ocaps_update[simp]:
  "label_prop_upd_inv (os\<lparr>ocaps := xs\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_initia_update[simp]:
  "label_prop_upd_inv (os\<lparr>initia := b\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_en1_update[simp]:
  "label_prop_upd_inv (os\<lparr>en1 := f\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_is_en1_update[simp]:
  "label_prop_upd_inv (os\<lparr>is_en1 := f\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_en2_update[simp]:
  "label_prop_upd_inv (os\<lparr>en2 := f\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_de2_update[simp]:
  "label_prop_upd_inv (os\<lparr>de2 := f\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_is_en2_update[simp]:
  "label_prop_upd_inv (os\<lparr>is_en2 := f\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_input_update_port0[simp]:
  "label_prop_upd_inv (os\<lparr>input := (input os)(0 := xs)\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_fold_consumes_port0[simp]:
  "label_prop_upd_inv (fold (\<lambda>(d, t) os. consumes os 0 t d) xs os) = label_prop_upd_inv os"
  unfolding fold_consumes by simp


definition wf_label_prop_updates where
  \<open>wf_label_prop_updates os S \<longleftrightarrow> (\<forall>(d, t) \<in> S. myfst t \<in> set (timestamps os)
    \<and> fst (de1 os d) \<in> all_vertices os (myfst t)
    \<and> (\<forall>t' \<ge> myfst t. snd (de1 os d) \<in> cc_of (all_edges os t') (fst (de1 os d))))\<close>

lemma wf_label_prop_updates_un:
  "wf_label_prop_updates os (S1 \<union> S2) \<longleftrightarrow> wf_label_prop_updates os S1 \<and> wf_label_prop_updates os S2"
  unfolding wf_label_prop_updates_def
  by auto

lemma label_prop_upd_inv_vertices_timestamps_iff:
  assumes "label_prop_upd_inv os"
  shows "t \<notin> set (timestamps os) \<longleftrightarrow> vertices os t = []"
proof -
  let ?E = "{(v, w). w \<in> set (graph os t v)}"
  have ts_eq: "t \<in> set (timestamps os) \<longleftrightarrow> edge_vertices ?E \<noteq> {}"
    using assms unfolding label_prop_upd_inv_def by metis
  have vertices_eq: "set (vertices os t) = edge_vertices ?E"
    using assms unfolding label_prop_upd_inv_def by metis
  show ?thesis
  proof
    assume "t \<notin> set (timestamps os)"
    then have "edge_vertices ?E = {}"
      using ts_eq by blast
    then have "set (vertices os t) = {}"
      using vertices_eq by simp
    then show "vertices os t = []"
      by (simp only: List.set_empty)
  next
    assume "vertices os t = []"
    then have "edge_vertices ?E = {}"
      using vertices_eq by simp
    then show "t \<notin> set (timestamps os)"
      using ts_eq by blast
  qed
qed

lemma label_prop_upd_inv_graph_edgeD:
  assumes "label_prop_upd_inv os"
    and "w \<in> set (graph os t v)"
  shows "v \<in> set (vertices os t) \<and> w \<in> set (vertices os t)"
  using assms unfolding label_prop_upd_inv_def edge_vertices_def Field_def by auto

lemma label_prop_upd_inv_graph_empty_if_not_timestamp:
  assumes inv: "label_prop_upd_inv os"
    and t_notin: "t \<notin> set (timestamps os)"
  shows "graph os t v = []"
proof (rule ccontr)
  assume "graph os t v \<noteq> []"
  then obtain w where "w \<in> set (graph os t v)"
    by (cases "graph os t v") auto
  then have "v \<in> set (vertices os t)"
    using label_prop_upd_inv_graph_edgeD[OF inv] by simp
  moreover have "vertices os t = []"
    using label_prop_upd_inv_vertices_timestamps_iff[OF inv] t_notin by simp
  ultimately show False
    by simp
qed

lemma label_prop_upd_inv_neighbors_ConsD:
  assumes inv: "label_prop_upd_inv (os\<lparr>timestamps := T\<rparr>)"
    and neigh: "w \<in> set (neighbors (os\<lparr>timestamps := t # T\<rparr>) q v)"
  shows "v \<in> all_vertices (os\<lparr>timestamps := t # T\<rparr>) q \<and>
    w \<in> all_vertices (os\<lparr>timestamps := t # T\<rparr>) q"
proof -
  obtain t' where t'_in: "t' \<in> set (t # T)" and t'_le: "t' \<le> q"
    and w_graph: "w \<in> set (graph os t' v)"
    using neigh unfolding set_neighbors by auto
  show ?thesis
  proof (cases "t' \<in> set T")
    case True
    then have "v \<in> set (vertices os t')" and "w \<in> set (vertices os t')"
      using label_prop_upd_inv_graph_edgeD[OF inv, of w t' v] w_graph by simp_all
    then show ?thesis
      using True t'_le unfolding all_vertices_def by auto
  next
    case False
    then have "t' = t"
      using t'_in by simp
    moreover have "graph os t' v = []"
      using label_prop_upd_inv_graph_empty_if_not_timestamp[OF inv, of t' v] False by simp
    ultimately show ?thesis
      using w_graph by simp
  qed
qed

lemma all_edges_Cons_timestamp_eq:
  assumes inv: "label_prop_upd_inv os"
  shows "all_edges (os\<lparr>timestamps := t # timestamps os\<rparr>) q = all_edges os q"
proof -
  have vertices_eq: "all_vertices (os\<lparr>timestamps := t # timestamps os\<rparr>) q = all_vertices os q"
    using label_prop_upd_inv_vertices_timestamps_iff[OF inv, of t]
    unfolding all_vertices_def by auto
  have neighbors_eq:
    "\<And>v. set (neighbors (os\<lparr>timestamps := t # timestamps os\<rparr>) q v) = set (neighbors os q v)"
  proof -
    fix v
    show "set (neighbors (os\<lparr>timestamps := t # timestamps os\<rparr>) q v) = set (neighbors os q v)"
    proof (cases "t \<in> set (timestamps os)")
      case True
      then show ?thesis
        unfolding set_neighbors by auto
    next
      case False
      then have "graph os t v = []"
        using label_prop_upd_inv_graph_empty_if_not_timestamp[OF inv] by simp
      then show ?thesis
        using False unfolding set_neighbors by auto
    qed
  qed
  show ?thesis
    using vertices_eq neighbors_eq unfolding all_edges_def by auto
qed



lemma label_prop_upd_inv_neighborsD:
  assumes inv: "label_prop_upd_inv os"
    and neigh: "w \<in> set (neighbors os t v)"
  shows "v \<in> all_vertices os t \<and> w \<in> all_vertices os t"
proof -
  obtain t' where t'_in: "t' \<in> set (timestamps os)" and t'_le: "t' \<le> t"
    and w_graph: "w \<in> set (graph os t' v)"
    using neigh unfolding set_neighbors by auto
  have vertices_eq:
    "set (vertices os t') = edge_vertices {(v, w). w \<in> set (graph os t' v)}"
    using inv unfolding label_prop_upd_inv_def by metis
  then have "v \<in> set (vertices os t')" and "w \<in> set (vertices os t')"
    using w_graph unfolding edge_vertices_def Field_def by auto
  then show ?thesis
    using t'_in t'_le unfolding all_vertices_def by auto
qed

lemma edge_vertices_all_edges:
  assumes inv: "label_prop_upd_inv os"
  shows "edge_vertices (all_edges os t) = all_vertices os t"
proof (intro equalityI subsetI)
  fix v
  assume "v \<in> edge_vertices (all_edges os t)"
  then show "v \<in> all_vertices os t"
    unfolding edge_vertices_def all_edges_def Field_def by auto
next
  fix v
  assume v_all: "v \<in> all_vertices os t"
  then obtain t' where t'_in: "t' \<in> set (timestamps os)" and t'_le: "t' \<le> t"
    and v_vertices: "v \<in> set (vertices os t')"
    unfolding all_vertices_def by auto
  have vertices_eq:
    "set (vertices os t') = edge_vertices {(v, w). w \<in> set (graph os t' v)}"
    using inv unfolding label_prop_upd_inv_def by metis
  then have "v \<in> edge_vertices {(v, w). w \<in> set (graph os t' v)}"
    using v_vertices by simp
  then obtain u where edge: "u \<in> set (graph os t' v) \<or> v \<in> set (graph os t' u)"
    unfolding edge_vertices_def Field_def by auto
  then show "v \<in> edge_vertices (all_edges os t)"
  proof
    assume u_graph: "u \<in> set (graph os t' v)"
    then have u_all: "u \<in> all_vertices os t"
      using label_prop_upd_inv_neighborsD[OF inv] t'_in t'_le
      unfolding set_neighbors by auto
    have "(v, u) \<in> all_edges os t"
      using v_all u_all u_graph t'_in t'_le
      unfolding all_edges_def set_neighbors by auto
    then show ?thesis
      unfolding edge_vertices_def Field_def by auto
  next
    assume v_graph: "v \<in> set (graph os t' u)"
    then have u_all: "u \<in> all_vertices os t"
      using label_prop_upd_inv_neighborsD[OF inv] t'_in t'_le
      unfolding set_neighbors by auto
    have "(u, v) \<in> all_edges os t"
      using v_all u_all v_graph t'_in t'_le
      unfolding all_edges_def set_neighbors by auto
    then show ?thesis
      unfolding edge_vertices_def Field_def by auto
  qed
qed









lemma min_label_le_current_labelI:
  fixes t :: "'t::order"
  shows "min_label os t v \<le> label os t v"
  unfolding min_label_def by (auto intro: Min_le)



lemma edge_vertices_all_edges_subset_all_vertices:
  "edge_vertices (all_edges os t) \<subseteq> all_vertices os t"
  unfolding edge_vertices_def all_edges_def Field_def by auto


lemma cc_of_mono:
  assumes subset: "A \<subseteq> B"
    and x_cc: "x \<in> cc_of A v"
  shows "x \<in> cc_of B v"
proof -
  have rel_subset: "A \<union> A\<inverse> \<subseteq> B \<union> B\<inverse>"
    using subset by auto
  have "reachable B v x"
  proof -
    have "(v, x) \<in> (A \<union> A\<inverse>)\<^sup>*"
      using x_cc unfolding cc_of_def reachable_def by simp
    then have "(v, x) \<in> (B \<union> B\<inverse>)\<^sup>*"
      using rtrancl_mono[OF rel_subset] by blast
    then show ?thesis
      unfolding reachable_def by simp
  qed

  moreover have "x \<in> edge_vertices B"
    using subset x_cc unfolding cc_of_def edge_vertices_def Field_def by auto
  ultimately show ?thesis
    unfolding cc_of_def by simp
qed

lemma all_edges_mono:
  fixes t q :: "'t::order"
  assumes "t \<le> q"
  shows "all_edges os t \<subseteq> all_edges os q"
  using assms unfolding all_edges_def all_vertices_def set_neighbors by auto


lemma min_label_eq_self_if_not_all_vertices':
  fixes t :: "'t::order"
  assumes inv: "label_prop_upd_inv os"
    and not_vertex: "v \<notin> all_vertices os t"
  shows "min_label os t v = v"
proof -
  have label_self: "\<And>q. q \<le> t \<Longrightarrow> label os q v = v"
  proof -
    fix q
    assume q_le: "q \<le> t"
    have "v \<notin> all_vertices os q"
      using not_vertex q_le unfolding all_vertices_def by auto
    then show "label os q v = v"
      using inv unfolding label_prop_upd_inv_def by blast
  qed
  have stored_self:
    "\<And>q. q \<in> set (timestamps os) \<Longrightarrow> q \<le> t \<Longrightarrow> label os q v = v"
    by (rule label_self)
  have set_eq:
    "insert (label os t v) ((\<lambda>q. label os q v) ` {q \<in> set (timestamps os). q \<le> t}) = {v}"
    using label_self[of t] stored_self by auto
  show ?thesis
    unfolding min_label_def by (simp only: set_eq Min_singleton)
qed

lemma labels_inv_min_label_le:
  fixes t q :: "'t::order"
  assumes labels: "\<And>r. labels_inv (all_edges os r) (min_label os r)"
    and inv: "label_prop_upd_inv os"
    and t_le_q: "t \<le> q"
    and v_in: "v \<in> all_vertices os q"
  shows "min_label os t v \<in> cc_of (all_edges os q) v"
proof (cases "v \<in> all_vertices os t")
  case True
  then have "v \<in> edge_vertices (all_edges os t)"
    using edge_vertices_all_edges[OF inv, of t] by simp
  then have "min_label os t v \<in> cc_of (all_edges os t) v"
    using labels[of t] unfolding labels_inv_def by blast
  moreover have "all_edges os t \<subseteq> all_edges os q"
    using t_le_q by (rule all_edges_mono)
  ultimately show ?thesis
    using cc_of_mono by blast
next
  case False
  then have min_self: "min_label os t v = v"
    using min_label_eq_self_if_not_all_vertices'[OF inv] by simp
  have "v \<in> edge_vertices (all_edges os q)"
    using edge_vertices_all_edges[OF inv, of q] v_in by simp
  then show ?thesis
    using min_self unfolding cc_of_def reachable_def by auto
qed





lemma min_label_input0_update_cases:
  fixes q t1 :: "'t::order"
  assumes t1_le_q: "t1 \<le> q"
    and timestamps_eq: "timestamps os' = t1 # timestamps os"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(v := l))"
    and new_le: "l \<le> min_label os t1 v"
  shows "min_label os' q x = min_label os q x \<or>
    min_label os' q x = min_label os t1 x \<or>
    (x = v \<and> min_label os' q x = l)"
proof (cases "x = v")
  case True
  let ?New = "insert (label os' q x) ((\<lambda>r. label os' r x) ` {r \<in> set (timestamps os'). r \<le> q})"
  let ?Oldq = "insert (label os q x) ((\<lambda>r. label os r x) ` {r \<in> set (timestamps os). r \<le> q})"
  let ?Oldt = "insert (label os t1 x) ((\<lambda>r. label os r x) ` {r \<in> set (timestamps os). r \<le> t1})"
  have l_in_new: "l \<in> ?New"
    using True t1_le_q timestamps_eq label_eq by auto
  have min_in_new: "Min ?New \<in> ?New"
    by (intro Min_in) auto
  have min_le_new: "\<And>y. y \<in> ?New \<Longrightarrow> Min ?New \<le> y"
    by (intro Min_le) auto
  have new_subset: "?New \<subseteq> insert l ?Oldq"
    using True t1_le_q timestamps_eq label_eq by auto
  show ?thesis
  proof (cases "Min ?New = l")
    case True
    then show ?thesis
      using \<open>x = v\<close> unfolding min_label_def by simp
  next
    case False
    then have min_oldq_mem: "Min ?New \<in> ?Oldq"
      using min_in_new new_subset by auto
    have oldq_lower: "\<And>y. y \<in> ?Oldq \<Longrightarrow> Min ?New \<le> y"
    proof -
      fix y
      assume y_oldq: "y \<in> ?Oldq"
      have "y \<in> ?New \<or> y \<in> ?Oldt"
        using y_oldq True t1_le_q timestamps_eq label_eq by auto
      then show "Min ?New \<le> y"
      proof
        assume "y \<in> ?New"
        then show ?thesis
          by (rule min_le_new)
      next
        assume y_oldt: "y \<in> ?Oldt"
        have "Min ?Oldt \<le> y"
          using y_oldt by (intro Min_le) auto
        moreover have "l \<le> Min ?Oldt"
          using new_le True unfolding min_label_def by simp
        ultimately have "l \<le> y"
          by order

        moreover have "Min ?New \<le> l"
          using min_le_new[OF l_in_new] .
        ultimately show ?thesis
          by order
      qed
    qed
    have "Min ?Oldq = Min ?New"
    proof (rule Min_eqI)
      show "finite ?Oldq"
        by auto
      show "\<And>y. y \<in> ?Oldq \<Longrightarrow> Min ?New \<le> y"
        by (rule oldq_lower)
      show "Min ?New \<in> ?Oldq"
        by (rule min_oldq_mem)
    qed
    then have "Min ?New = Min ?Oldq"
      by simp
    then show ?thesis
      unfolding min_label_def by simp

  qed
next
  case False
  let ?New = "insert (label os' q x) ((\<lambda>r. label os' r x) ` {r \<in> set (timestamps os'). r \<le> q})"
  let ?Oldq = "insert (label os q x) ((\<lambda>r. label os r x) ` {r \<in> set (timestamps os). r \<le> q})"
  let ?Oldt = "insert (label os t1 x) ((\<lambda>r. label os r x) ` {r \<in> set (timestamps os). r \<le> t1})"
  have set_eq: "?New = insert (label os t1 x) ?Oldq"
    using False t1_le_q timestamps_eq label_eq by auto
  have min_new: "Min ?New = min (label os t1 x) (Min ?Oldq)"
    using set_eq by (simp add: Min_insert)
  show ?thesis
  proof (cases "label os t1 x < Min ?Oldq")
    case True
    have label_t1_lower: "\<And>y. y \<in> ?Oldt \<Longrightarrow> label os t1 x \<le> y"
    proof -
      fix y
      assume y_oldt: "y \<in> ?Oldt"
      then show "label os t1 x \<le> y"
      proof
        assume "y = label os t1 x"
        then show ?thesis by simp
      next
        assume "y \<in> (\<lambda>r. label os r x) ` {r \<in> set (timestamps os). r \<le> t1}"
        then have "y \<in> ?Oldq"
          using t1_le_q by auto
        then have "Min ?Oldq \<le> y"
          by (intro Min_le) auto
        then show ?thesis
          using True by order

      qed
    qed
    have "Min ?Oldt = label os t1 x"
      by (rule Min_eqI) (auto intro: label_t1_lower)
    then show ?thesis
      using True min_new False unfolding min_label_def by simp
  next
    case False
    have "Min ?Oldq \<le> label os t1 x"
      using False by order
    then have "Min ?New = Min ?Oldq"
      using min_new by simp
    then show ?thesis
      unfolding min_label_def by simp

  qed
qed







lemma all_edges_eq:
  fixes t :: "'t::order"
  assumes V'_def: "V' = map_entry t ((Cons v1) o (Cons v2)) V"
    and sync: "label_prop_upd_inv
    \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
     input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
     initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
     en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
     timestamps = T, graph = G, vertices = V, label = label_sync\<rparr>"



shows "all_edges
   \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = t # T, graph = G(t := (map_entry v1 (Cons v2) (G t))(v2 := v1 # (G t v2))),
    vertices = V', label = label_state\<rparr> t =
   insert (v1, v2) (insert (v2, v1) (all_edges
   \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = T, graph = G, vertices = V, label = label_sync\<rparr> t))"
proof -
  let ?mod = "\<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = t # T, graph = G(t := (map_entry v1 (Cons v2) (G t))(v2 := v1 # (G t v2))),
    vertices = V', label = label_state\<rparr>"


  let ?base = "\<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = t # T, graph = G, vertices = V, label = label_state\<rparr>"
  let ?base_tail = "\<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = T, graph = G, vertices = V, label = label_sync\<rparr>"


  have vertices_mod:
    "all_vertices ?mod t = insert v1 (insert v2 (all_vertices ?base t))"
    using V'_def by (auto simp: all_vertices_def split: if_splits)
  have neighbors_mod:
    "\<And>v. set (neighbors ?mod t v) =
      (if v = v1 then insert v2 (set (neighbors ?base t v))
       else if v = v2 then insert v1 (set (neighbors ?base t v))
       else set (neighbors ?base t v))"
    by (auto simp: neighbors_def split: if_splits)

  have invD: "\<And>v w. w \<in> set (neighbors ?base t v) \<Longrightarrow>
    v \<in> all_vertices ?base t \<and> w \<in> all_vertices ?base t"
  proof -
    fix v w
    assume neigh: "w \<in> set (neighbors ?base t v)"
    have sync': "label_prop_upd_inv (?base_tail\<lparr>timestamps := T\<rparr>)"
      using sync by simp
    have neigh': "w \<in> set (neighbors (?base_tail\<lparr>timestamps := t # T\<rparr>) t v)"
      using neigh by (simp add: neighbors_def)
    have "v \<in> all_vertices (?base_tail\<lparr>timestamps := t # T\<rparr>) t \<and>
      w \<in> all_vertices (?base_tail\<lparr>timestamps := t # T\<rparr>) t"
      using label_prop_upd_inv_neighbors_ConsD[OF sync' neigh'] .

    then show "v \<in> all_vertices ?base t \<and> w \<in> all_vertices ?base t"
      by (simp add: all_vertices_def)
  qed

  have mod_eq_base:
    "all_edges ?mod t = insert (v1, v2) (insert (v2, v1) (all_edges ?base t))"

  proof (intro equalityI subsetI)
    fix e
    assume e: "e \<in> all_edges ?mod t"
    then obtain a b where e_pair: "e = (a, b)" and a_mod: "a \<in> all_vertices ?mod t"
      and b_mod: "b \<in> all_vertices ?mod t" and b_neigh: "b \<in> set (neighbors ?mod t a)"
      by (auto simp: all_edges_def)
    show "e \<in> insert (v1, v2) (insert (v2, v1) (all_edges ?base t))"
    proof (cases "a = v1")
      case True
      then have "b = v2 \<or> b \<in> set (neighbors ?base t v1)"
        using b_neigh neighbors_mod[of a] by auto
      then show ?thesis
      proof
        assume "b = v2"
        then show ?thesis
          using True e_pair by simp
      next
        assume b_base: "b \<in> set (neighbors ?base t v1)"
        then have "(v1, b) \<in> all_edges ?base t"
          using invD[OF b_base] by (auto simp: all_edges_def)
        then show ?thesis
          using True e_pair by simp
      qed
    next
      case a_not_v1: False
      show ?thesis
      proof (cases "a = v2")
        case True
        then have "b = v1 \<or> b \<in> set (neighbors ?base t v2)"
          using a_not_v1 b_neigh neighbors_mod[of a] by auto
        then show ?thesis
        proof
          assume "b = v1"
          then show ?thesis
            using True e_pair by simp
        next
          assume b_base: "b \<in> set (neighbors ?base t v2)"
          then have "(v2, b) \<in> all_edges ?base t"
            using invD[OF b_base] by (auto simp: all_edges_def)
          then show ?thesis
            using True e_pair by simp
        qed
      next
        case a_not_v2: False
        then have b_base: "b \<in> set (neighbors ?base t a)"
          using a_not_v1 b_neigh neighbors_mod[of a] by auto
        then have "(a, b) \<in> all_edges ?base t"
          using invD[OF b_base] by (auto simp: all_edges_def)
        then show ?thesis
          using e_pair by simp
      qed
    qed
  next
    fix e
    assume e: "e \<in> insert (v1, v2) (insert (v2, v1) (all_edges ?base t))"
    then show "e \<in> all_edges ?mod t"
    proof (elim insertE)
      assume "e = (v1, v2)"
      then show ?thesis
        using vertices_mod neighbors_mod[of v1] by (auto simp: all_edges_def)
    next
      assume "e = (v2, v1)"
      then show ?thesis
        using vertices_mod neighbors_mod[of v2] by (auto simp: all_edges_def)
    next
      assume e_base: "e \<in> all_edges ?base t"
      then obtain a b where e_pair: "e = (a, b)" and a_base: "a \<in> all_vertices ?base t"
        and b_base: "b \<in> all_vertices ?base t" and b_neigh: "b \<in> set (neighbors ?base t a)"
        by (auto simp: all_edges_def)
      have "b \<in> set (neighbors ?mod t a)"
        using b_neigh neighbors_mod[of a] by auto
      then show ?thesis
        using e_pair a_base b_base vertices_mod by (auto simp: all_edges_def)
    qed
  qed
  have base_eq_tail': "all_edges (?base_tail\<lparr>timestamps := t # T\<rparr>) t = all_edges ?base_tail t"
    using all_edges_Cons_timestamp_eq[OF sync, of t] by simp

  have base_eq_tail: "all_edges ?base t = all_edges ?base_tail t"
    using base_eq_tail' by (simp add: all_edges_def all_vertices_def neighbors_def)



  show ?thesis
    using mod_eq_base base_eq_tail by simp
qed



section \<open>Edge Enumeration under Label Updates\<close>

text \<open>all_edges is stable under label updates on either side of the
  order.\<close>

lemma all_edges_eq_le:
  fixes t :: "'t::order"
  assumes V'_def: "V' = map_entry t ((Cons v1) o (Cons v2)) V"
    and sync: "label_prop_upd_inv
    \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
     input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
     initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
     en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
     timestamps = T, graph = G, vertices = V, label = label_sync\<rparr>"

and time_le: "t \<le> t'"

shows "all_edges
   \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = t # T, graph = G(t := (map_entry v1 (Cons v2) (G t))(v2 := v1 # (G t v2))),
    vertices = V', label = label_state\<rparr> t' =
   insert (v1, v2) (insert (v2, v1) (all_edges
   \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = T, graph = G, vertices = V, label = label_sync\<rparr> t'))"
proof -
  let ?mod = "\<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = t # T, graph = G(t := (map_entry v1 (Cons v2) (G t))(v2 := v1 # (G t v2))),
    vertices = V', label = label_state\<rparr>"
  let ?base = "\<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = t # T, graph = G, vertices = V, label = label_state\<rparr>"
  let ?base_tail = "\<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = T, graph = G, vertices = V, label = label_sync\<rparr>"

  have vertices_mod:
    "all_vertices ?mod t' = insert v1 (insert v2 (all_vertices ?base t'))"
    using V'_def time_le by (auto simp: all_vertices_def split: if_splits)
  have neighbors_mod:
    "\<And>v. set (neighbors ?mod t' v) =
      (if v = v1 then insert v2 (set (neighbors ?base t' v))
       else if v = v2 then insert v1 (set (neighbors ?base t' v))
       else set (neighbors ?base t' v))"
    using time_le by (auto simp: neighbors_def split: if_splits)

  have invD: "\<And>v w. w \<in> set (neighbors ?base t' v) \<Longrightarrow>
    v \<in> all_vertices ?base t' \<and> w \<in> all_vertices ?base t'"
  proof -
    fix v w
    assume neigh: "w \<in> set (neighbors ?base t' v)"
    have sync': "label_prop_upd_inv (?base_tail\<lparr>timestamps := T\<rparr>)"
      using sync by simp
    have neigh': "w \<in> set (neighbors (?base_tail\<lparr>timestamps := t # T\<rparr>) t' v)"
      using neigh by (simp add: neighbors_def)
    have "v \<in> all_vertices (?base_tail\<lparr>timestamps := t # T\<rparr>) t' \<and>
      w \<in> all_vertices (?base_tail\<lparr>timestamps := t # T\<rparr>) t'"
      using label_prop_upd_inv_neighbors_ConsD[OF sync' neigh'] .
    then show "v \<in> all_vertices ?base t' \<and> w \<in> all_vertices ?base t'"
      by (simp add: all_vertices_def)
  qed

  have mod_eq_base:
    "all_edges ?mod t' = insert (v1, v2) (insert (v2, v1) (all_edges ?base t'))"
  proof (intro equalityI subsetI)
    fix e
    assume e: "e \<in> all_edges ?mod t'"
    then obtain a b where e_pair: "e = (a, b)" and a_mod: "a \<in> all_vertices ?mod t'"
      and b_mod: "b \<in> all_vertices ?mod t'" and b_neigh: "b \<in> set (neighbors ?mod t' a)"
      by (auto simp: all_edges_def)
    show "e \<in> insert (v1, v2) (insert (v2, v1) (all_edges ?base t'))"
    proof (cases "a = v1")
      case True
      then have "b = v2 \<or> b \<in> set (neighbors ?base t' v1)"
        using b_neigh neighbors_mod[of a] by auto
      then show ?thesis
      proof
        assume "b = v2"
        then show ?thesis
          using True e_pair by simp
      next
        assume b_base: "b \<in> set (neighbors ?base t' v1)"
        then have "(v1, b) \<in> all_edges ?base t'"
          using invD[OF b_base] by (auto simp: all_edges_def)
        then show ?thesis
          using True e_pair by simp
      qed
    next
      case a_not_v1: False
      show ?thesis
      proof (cases "a = v2")
        case True
        then have "b = v1 \<or> b \<in> set (neighbors ?base t' v2)"
          using a_not_v1 b_neigh neighbors_mod[of a] by auto
        then show ?thesis
        proof
          assume "b = v1"
          then show ?thesis
            using True e_pair by simp
        next
          assume b_base: "b \<in> set (neighbors ?base t' v2)"
          then have "(v2, b) \<in> all_edges ?base t'"
            using invD[OF b_base] by (auto simp: all_edges_def)
          then show ?thesis
            using True e_pair by simp
        qed
      next
        case a_not_v2: False
        then have b_base: "b \<in> set (neighbors ?base t' a)"
          using a_not_v1 b_neigh neighbors_mod[of a] by auto
        then have "(a, b) \<in> all_edges ?base t'"
          using invD[OF b_base] by (auto simp: all_edges_def)
        then show ?thesis
          using e_pair by simp
      qed
    qed
  next
    fix e
    assume e: "e \<in> insert (v1, v2) (insert (v2, v1) (all_edges ?base t'))"
    then show "e \<in> all_edges ?mod t'"
    proof (elim insertE)
      assume "e = (v1, v2)"
      then show ?thesis
        using vertices_mod neighbors_mod[of v1] by (auto simp: all_edges_def)
    next
      assume "e = (v2, v1)"
      then show ?thesis
        using vertices_mod neighbors_mod[of v2] by (auto simp: all_edges_def)
    next
      assume e_base: "e \<in> all_edges ?base t'"
      then obtain a b where e_pair: "e = (a, b)" and a_base: "a \<in> all_vertices ?base t'"
        and b_base: "b \<in> all_vertices ?base t'" and b_neigh: "b \<in> set (neighbors ?base t' a)"
        by (auto simp: all_edges_def)
      have "b \<in> set (neighbors ?mod t' a)"
        using b_neigh neighbors_mod[of a] by auto
      then show ?thesis
        using e_pair a_base b_base vertices_mod by (auto simp: all_edges_def)
    qed
  qed
  have base_eq_tail: "all_edges ?base t' = all_edges ?base_tail t'"
    using all_edges_Cons_timestamp_eq[OF sync, of t t']
    by (simp add: all_edges_def all_vertices_def neighbors_def)


  show ?thesis
    using mod_eq_base base_eq_tail by simp
qed


lemma all_edges_eq_not_le:
  fixes t :: "'t::order"
  assumes V'_def: "V' = map_entry t ((Cons v1) o (Cons v2)) V"
    and time_not_le: "\<not> t \<le> t'"

shows "all_edges
   \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = t # T, graph = G(t := (map_entry v1 (Cons v2) (G t))(v2 := v1 # (G t v2))),
    vertices = V', label = label_state\<rparr> t' =
   (all_edges
   \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = T, graph = G, vertices = V, label = label_sync\<rparr> t')"
proof -
  let ?mod = "\<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = t # T, graph = G(t := (map_entry v1 (Cons v2) (G t))(v2 := v1 # (G t v2))),
    vertices = V', label = label_state\<rparr>"
  let ?base_tail = "\<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = T, graph = G, vertices = V, label = label_sync\<rparr>"
  have vertices_eq: "all_vertices ?mod t' = all_vertices ?base_tail t'"
    using V'_def time_not_le by (auto simp: all_vertices_def split: if_splits)
  have neighbors_eq: "\<And>v. set (neighbors ?mod t' v) = set (neighbors ?base_tail t' v)"
    using time_not_le by (auto simp: neighbors_def split: if_splits)
  show ?thesis
    using vertices_eq neighbors_eq by (auto simp: all_edges_def)
qed









section \<open>Batching and the Operator Definition\<close>

text \<open>Record-update batches and the label_propagation_op operator itself.\<close>

definition label_prop_edge_record_update where
  \<open>label_prop_edge_record_update old_os event_t src_v dst_v updated_v updated_label =
    old_os\<lparr>
      timestamps := event_t # timestamps old_os,
      graph := (graph old_os)(event_t :=
        (graph old_os event_t)(src_v := dst_v # graph old_os event_t src_v,
                              dst_v := src_v # graph old_os event_t dst_v)),
      vertices := (vertices old_os)(event_t := [src_v, dst_v] @ vertices old_os event_t),
      label := (label old_os)(event_t := (label old_os event_t)(updated_v := updated_label))\<rparr>\<close>

definition label_prop_label_record_update where
  \<open>label_prop_label_record_update old_os event_t vertex assigned_label =
    old_os\<lparr>label := (label old_os)(event_t := (label old_os event_t)(vertex := assigned_label))\<rparr>\<close>

definition label_prop_neighbor_batch where
  \<open>label_prop_neighbor_batch old_os neighbor_os label_os relevant_times vertex new_label event_time =
    concat (map (\<lambda>cur_t.
      let vs = neighbors neighbor_os cur_t vertex in
      if min_label old_os cur_t vertex > new_label
      then map (\<lambda>v'. (en1 old_os (v', new_label), Cap (MyPair cur_t (mysnd event_time)) 1))
        (filter (\<lambda>v'. min_label label_os cur_t v' > new_label) vs)
      else []) relevant_times)\<close>

definition label_prop_edge_batch where
  \<open>label_prop_edge_batch old_os updated_os event_t vertex new_label event_time =
    concat (map (\<lambda>cur_t.
      let vs = neighbors updated_os cur_t vertex;
          m = fold min (map (min_label old_os cur_t) vs)
                (min (min_label old_os cur_t vertex) new_label) in
      map (\<lambda>v'. (en1 old_os (v', m), Cap (MyPair cur_t (mysnd event_time)) 1))
        (filter (\<lambda>v'. m < min_label old_os cur_t v') (vertex # vs)))
      (filter ((\<le>) event_t) (timestamps updated_os)))\<close>

definition label_prop_label_batch where
  \<open>label_prop_label_batch old_os updated_os event_t vertex new_label event_time =
    label_prop_neighbor_batch old_os old_os updated_os
      (filter ((\<le>) event_t) (timestamps old_os)) vertex new_label event_time\<close>

definition label_prop_output_batch where
  \<open>label_prop_output_batch old_os below_times =
    map
      (\<lambda>t. let cap = Cap (MyPair t (0 :: nat)) (0 :: 2) in
        (en2 old_os (components_from_labels (all_edges old_os t) (min_label old_os t)), cap))
      (remdups (map myfst below_times))\<close>

definition "label_prob_ty2_check os bufs \<equiv>
   (\<forall> p. (\<forall> x \<in> fst ` set (input os p) \<union> fst ` set (bufs p). is_en1 os x)) \<and>
   (\<forall> x \<in> fst ` set (outpu os 0). is_en2 os x) \<and> (\<forall> x \<in> fst ` set (outpu os 1). is_en1 os x)"

definition label_propagation_op_logic where
  \<open>label_propagation_op_logic os = cUn (cUn
    (case input os 0 of
      [] \<Rightarrow> {||}
    | (d, t) # _ \<Rightarrow>
      let
        (v1, v2) = de1 os d;
        t1 = myfst t;
        (l1, l2) = pairself (min_label os t1) (v1, v2);
        (v, l) = if l1 > l2 then (v1, l2) else (v2, l1);
        os' = input_tl os 0;
        os'' = label_prop_edge_record_update os' t1 v1 v2 v l;
        batch = label_prop_edge_batch os os'' t1 v l t
      in {|release_caps (drop_caps (produces ((add_caps os'' (map snd batch))) batch)  (map snd batch)) 1|})
    (case input os 1 of
      [] \<Rightarrow> {||}
    | (d, t) # _ \<Rightarrow>
      let
        (v, l) = de1 os d;
        t1 = myfst t;
        os' = input_tl os 1;
        l' = min (min_label os t1 v) l;
        os'' = label_prop_label_record_update os' t1 v l';
        batch = label_prop_label_batch os os'' t1 v l' t
      in
        {|release_caps (drop_caps (produces (add_caps os'' (map snd batch)) batch) (map snd batch)) 1|}))
  (cUn (let
      below_times = filter
        (\<lambda> t. \<not> frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t) \<and> myfst t \<in> set (timestamps os))
        (ocaps os 0);
      batch = label_prop_output_batch os below_times
    in
      if batch = [] then {||}
      else {|drop_caps (produces os batch) (map (\<lambda>t. Cap t 0) below_times)|})
    (case ocaps os 1 of [] \<Rightarrow> {||} | _ \<Rightarrow> {| release_caps os 1 |}))\<close>

term components_from_labels


(* @ map (\<lambda>t. Cap t 1) (filter P (ocaps os 1)) *)
definition label_propagation_op where
  \<open>label_propagation_op os = builder_op True cUNIV cUNIV os label_propagation_op_logic\<close>



(* FIXME: move me closer to dependencies *)

section \<open>Frame Facts for the Operator State\<close>

text \<open>Vertices, timestamps, and min_label are unchanged by capability and
  buffer updates.\<close>

lemma vertices_drop_caps[simp]:
  "vertices (drop_caps os caps) = vertices os"
  unfolding drop_caps_def
  by auto

lemma timestamps_drop_caps[simp]:
  "timestamps (drop_caps os caps) = timestamps os"
  unfolding drop_caps_def
  by auto

lemma vertices_release_caps[simp]:
  "vertices (release_caps os p) = vertices os"
  unfolding release_caps_def
  by auto

lemma timestamps_release_caps[simp]:
  "timestamps (release_caps os p) = timestamps os"
  unfolding release_caps_def trace_simp Let_def
  by auto

lemma timestamps_produces[simp]:
  "timestamps (produces os batch) = timestamps os"
  unfolding produces_def trace_simp Let_def
  by auto

lemma all_vertices_release_caps[simp]:
  "all_vertices (release_caps os p) = all_vertices os"
  unfolding all_vertices_def
  by (auto split: list.splits cong: if_cong)

lemma min_label_drop_caps[simp]:
  "min_label (drop_caps os p) = min_label os"
  unfolding drop_caps_def  Let_def trace_simp min_label_def
  by (auto cong: if_cong)

lemma min_label_release_caps[simp]:
  "min_label (release_caps os p) = min_label os"
  unfolding release_caps_def Let_def trace_simp
  by (auto split: list.splits)





lemma neighbors_drop_caps[simp]:
  "neighbors (drop_caps os caps) = neighbors os"
  unfolding drop_caps_def neighbors_def
  by auto

lemma neighbors_produces[simp]:
  "neighbors (produces os batch) = neighbors os"
  unfolding produces_def neighbors_def
  by auto

lemma graph_drop_caps[simp]:
  "label_propagation_state.graph (drop_caps os caps) = label_propagation_state.graph os"
  unfolding drop_caps_def 
  by auto

lemma graph_release_caps[simp]:
  "label_propagation_state.graph (release_caps os p) = label_propagation_state.graph os"
  unfolding release_caps_def
  by auto

lemma neighbors_release_caps[simp]:
  "neighbors (release_caps os p) = neighbors os"
  unfolding release_caps_def neighbors_def
  by auto

lemma all_vertices_drop_caps[simp]:
  "all_vertices (drop_caps os caps) = all_vertices os"
  unfolding all_vertices_def drop_caps_def
  apply clarsimp
  done

lemma all_vertices_add_caps[simp]:
  "all_vertices (add_caps os caps) = all_vertices os"
  unfolding all_vertices_def add_caps_def by simp

lemma all_vertices_produces[simp]:
  "all_vertices (produces os batch) = all_vertices os"
  unfolding all_vertices_def produces_def
  apply clarsimp
  done

lemma all_edges_drop_caps[simp]:
  "all_edges (drop_caps os caps) = all_edges os"
  unfolding all_edges_def
  by auto

lemma vertices_produces[simp]:
  "vertices (produces os batch) = vertices os"
  unfolding produces_def
  by auto

lemma all_edges_produces[simp]:
  "all_edges (produces os batch) = all_edges os"
  unfolding all_edges_def
  by (auto cong: if_cong)

lemma all_edges_release_caps[simp]:
  "all_edges (release_caps os p) = all_edges os"
  unfolding release_caps_def all_edges_def
  by auto

lemma all_edges_input_update[simp]:
  "all_edges (os\<lparr>input := input'\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_outpu_update[simp]:
  "all_edges (os\<lparr>outpu := outp\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_input_tl[simp]:
  "all_edges (input_tl os p) = all_edges os"
  unfolding input_tl_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_input_tl_label_state_update[simp]:
  "all_edges ((input_tl os p)\<lparr>timestamps := ts, graph := G, vertices := V, label := L\<rparr>) =
   all_edges (os\<lparr>timestamps := ts, graph := G, vertices := V, label := L\<rparr>)"
  unfolding input_tl_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_label_update[simp]:
  "all_edges (os\<lparr>label := L\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_intsum_update[simp]:
  "all_edges (os\<lparr>intsum := xs\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_consu_update[simp]:
  "all_edges (os\<lparr>consu := xs\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_inter_update[simp]:
  "all_edges (os\<lparr>inter := xs\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_produ_update[simp]:
  "all_edges (os\<lparr>produ := xs\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_front_update[simp]:
  "all_edges (os\<lparr>front := xs\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_ocaps_update[simp]:
  "all_edges (os\<lparr>ocaps := xs\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_initia_update[simp]:
  "all_edges (os\<lparr>initia := b\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_en1_update[simp]:
  "all_edges (os\<lparr>en1 := f\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_de1_update[simp]:
  "all_edges (os\<lparr>de1 := f\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_is_en1_update[simp]:
  "all_edges (os\<lparr>is_en1 := f\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_en2_update[simp]:
  "all_edges (os\<lparr>en2 := f\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_de2_update[simp]:
  "all_edges (os\<lparr>de2 := f\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma all_edges_is_en2_update[simp]:
  "all_edges (os\<lparr>is_en2 := f\<rparr>) = all_edges os"
  unfolding all_edges_def all_vertices_def neighbors_def by auto

lemma min_label_intsum_update[simp]:
  "min_label (os\<lparr>intsum := xs\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_consu_update[simp]:
  "min_label (os\<lparr>consu := xs\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_inter_update[simp]:
  "min_label (os\<lparr>inter := xs\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_produ_update[simp]:
  "min_label (os\<lparr>produ := xs\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_front_update[simp]:
  "min_label (os\<lparr>front := xs\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_ocaps_update[simp]:
  "min_label (os\<lparr>ocaps := xs\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_initia_update[simp]:
  "min_label (os\<lparr>initia := b\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_en1_update[simp]:
  "min_label (os\<lparr>en1 := f\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_de1_update[simp]:
  "min_label (os\<lparr>de1 := f\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_is_en1_update[simp]:
  "min_label (os\<lparr>is_en1 := f\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_en2_update[simp]:
  "min_label (os\<lparr>en2 := f\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_de2_update[simp]:
  "min_label (os\<lparr>de2 := f\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma min_label_is_en2_update[simp]:
  "min_label (os\<lparr>is_en2 := f\<rparr>) = min_label os"
  unfolding min_label_def by auto

lemma all_edges_add_cap[simp]:
  "all_edges (add_cap os p t') = all_edges os"
  unfolding add_cap_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_add_caps[simp]:
  "all_edges (add_caps os caps) = all_edges os"
  unfolding add_caps_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_delay_cap[simp]:
  "all_edges (delay_cap os cap incr) = all_edges os"
  unfolding delay_cap_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_consume[simp]:
  "all_edges (consume os p t' len) = all_edges os"
  unfolding consume_def all_edges_def all_vertices_def neighbors_def
  by (auto split: if_splits)

lemma all_edges_consumes[simp]:
  "all_edges (consumes os p t' d) = all_edges os"
  unfolding consumes_def add_caps_def BENQ_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_obtain_progress[simp]:
  "all_edges (fst (obtain_progress os)) = all_edges os"
  unfolding obtain_progress_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma all_edges_label_prop_label_record_update[simp]:
  "all_edges (label_prop_label_record_update os event_t vertex assigned_label) = all_edges os"
  unfolding label_prop_label_record_update_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma label_prob_ty2_check_timestamps_update[simp]:
  "label_prob_ty2_check (os\<lparr>timestamps := T\<rparr>) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def by auto

lemma label_prob_ty2_check_graph_update[simp]:
  "label_prob_ty2_check (os\<lparr>graph := G\<rparr>) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def by auto

lemma label_prob_ty2_check_vertices_update[simp]:
  "label_prob_ty2_check (os\<lparr>vertices := V\<rparr>) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def by auto

lemma label_prob_ty2_check_label_update[simp]:
  "label_prob_ty2_check (os\<lparr>label := L\<rparr>) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def by auto

lemma label_prob_ty2_check_drop_cap[simp]:
  "label_prob_ty2_check (drop_cap os cap) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def drop_cap_def by auto

lemma label_prob_ty2_check_drop_caps[simp]:
  "label_prob_ty2_check (drop_caps os caps) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def drop_caps_def by auto

lemma label_prob_ty2_check_release_caps[simp]:
  "label_prob_ty2_check (release_caps os p) bufs = label_prob_ty2_check os bufs"
  unfolding release_caps_def label_prob_ty2_check_def drop_caps_def trace_simp Let_def
  by auto

lemma label_prob_ty2_check_add_cap[simp]:
  "label_prob_ty2_check (add_cap os p t') bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def add_cap_def by auto

lemma label_prob_ty2_check_add_caps[simp]:
  "label_prob_ty2_check (add_caps os caps) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def add_caps_def by auto

lemma label_prob_ty2_check_delay_cap[simp]:
  "label_prob_ty2_check (delay_cap os cap incr) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def delay_cap_def by auto

lemma label_prob_ty2_check_consume[simp]:
  "label_prob_ty2_check (consume os p t' len) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def consume_def
  by (auto split: if_splits)

lemma label_prob_ty2_check_obtain_progress[simp]:
  "label_prob_ty2_check (fst (obtain_progress os)) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def obtain_progress_def by auto

lemma label_prob_ty2_check_label_prop_edge_record_update[simp]:
  "label_prob_ty2_check (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def label_prop_edge_record_update_def by auto

lemma label_prob_ty2_check_label_prop_label_record_update[simp]:
  "label_prob_ty2_check (label_prop_label_record_update os event_t vertex assigned_label) bufs = label_prob_ty2_check os bufs"
  unfolding label_prob_ty2_check_def label_prop_label_record_update_def by auto

lemma label_prob_ty2_check_producesI[intro]:
  assumes check: "label_prob_ty2_check os bufs"
    and out0: "\<And>x cap. (x, cap) \<in> set batch \<Longrightarrow> out cap = 0 \<Longrightarrow> is_en2 os x"
    and out1: "\<And>x cap. (x, cap) \<in> set batch \<Longrightarrow> out cap = 1 \<Longrightarrow> is_en1 os x"
  shows "label_prob_ty2_check (produces os batch) bufs"
  using check out0 out1
  unfolding label_prob_ty2_check_def produces_def
  by auto

lemma label_prob_ty2_check_input_tlI[intro]:
  assumes check: "label_prob_ty2_check os bufs"
  shows "label_prob_ty2_check (input_tl os p) bufs"
proof -
  have input_subset: "fst ` set (input (input_tl os p) q) \<subseteq> fst ` set (input os q)" for q
  proof (cases "q = p")
    case True
    then show ?thesis
      unfolding input_tl_def by (auto dest: in_set_tlD)
  next
    case False
    then show ?thesis
      unfolding input_tl_def by auto
  qed
  show ?thesis
    using check input_subset
    unfolding label_prob_ty2_check_def input_tl_def
    apply (intro conjI allI ballI)
    apply safe
    subgoal premises aux for pa x a b
      using aux(1)[of pa] aux(2) aux(5)
      by auto
    subgoal premises aux for pa x a b
      using aux(2) aux(5)
      by auto
    subgoal
      by auto
    subgoal
      by auto
    done
qed



lemma min_label_produces[simp]:
  "min_label (produces os batch) = min_label os"
  unfolding produces_def min_label_def
  by (auto cong: if_cong)

lemma min_label_drop_cap[simp]:
  "min_label (drop_cap os cap) = min_label os"
  unfolding drop_cap_def min_label_def
  by (auto cong: if_cong)

lemma min_label_add_cap[simp]:
  "min_label (add_cap os p t') = min_label os"
  unfolding add_cap_def min_label_def
  by (auto cong: if_cong)

lemma min_label_add_caps[simp]:
  "min_label (add_caps os caps) = min_label os"
  unfolding add_caps_def min_label_def
  by (auto cong: if_cong)

lemma min_label_delay_cap[simp]:
  "min_label (delay_cap os cap incr) = min_label os"
  unfolding delay_cap_def min_label_def
  by (auto cong: if_cong)

lemma min_label_consume[simp]:
  "min_label (consume os p t' len) = min_label os"
  unfolding consume_def min_label_def
  by (auto split: if_splits cong: if_cong)

lemma min_label_consumes[simp]:
  "min_label (consumes os p t' d) = min_label os"
  unfolding consumes_def add_caps_def BENQ_def min_label_def
  by (auto cong: if_cong)

lemma min_label_obtain_progress[simp]:
  "min_label (fst (obtain_progress os)) = min_label os"
  unfolding obtain_progress_def min_label_def
  by (auto cong: if_cong)

lemma min_label_input_tl[simp]:
  "min_label (input_tl os p) = min_label os"
  unfolding input_tl_def min_label_def
  by (auto cong: if_cong)

lemma min_label_input_update[simp]:
  "min_label (os\<lparr>input := input'\<rparr>) = min_label os"
  unfolding min_label_def
  by auto

lemma min_label_input_tl_label_state_update[simp]:
  "min_label ((input_tl os p)\<lparr>timestamps := ts, graph := G, vertices := V, label := L\<rparr>) =
   min_label (os\<lparr>timestamps := ts, graph := G, vertices := V, label := L\<rparr>)"
  unfolding input_tl_def min_label_def
  by auto

lemma labels_inv_drop_cap[simp]:
  "labels_inv (all_edges (drop_cap os cap) t) (min_label (drop_cap os cap) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def drop_cap_def
  by auto

lemma labels_inv_drop_caps[simp]:
  "labels_inv (all_edges (drop_caps os caps) t) (min_label (drop_caps os caps) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def drop_caps_def
  by auto

lemma labels_inv_release_caps[simp]:
  "labels_inv (all_edges (release_caps os p) t) (min_label (release_caps os p) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding release_caps_def Let_def trace_simp
  by simp

lemma labels_inv_produces[simp]:
  "labels_inv (all_edges (produces os batch) t) (min_label (produces os batch) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def produces_def
  by auto

lemma labels_inv_delay_cap[simp]:
  "labels_inv (all_edges (delay_cap os cap incr) t) (min_label (delay_cap os cap incr) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def delay_cap_def
  by auto

lemma labels_inv_consume[simp]:
  "labels_inv (all_edges (consume os p t' len) t) (min_label (consume os p t' len) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def consume_def
  by auto

lemma labels_inv_add_cap[simp]:
  "labels_inv (all_edges (add_cap os p t') t) (min_label (add_cap os p t') t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def add_cap_def
  by auto

lemma labels_inv_add_caps[simp]:
  "labels_inv (all_edges (add_caps os caps) t) (min_label (add_caps os caps) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def add_caps_def
  by auto

lemma labels_inv_consumes[simp]:
  "labels_inv (all_edges (consumes os p t' d) t) (min_label (consumes os p t' d) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def consumes_def add_caps_def BENQ_def
  by auto

lemma labels_inv_fold_consumes[simp]:
  "labels_inv (all_edges (fold (\<lambda>(d, t') os'. consumes os' p t' d) xs os) t)
     (min_label (fold (\<lambda>(d, t') os'. consumes os' p t' d) xs os) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def fold_consumes
  by auto

lemma labels_inv_obtain_progress[simp]:
  "labels_inv (all_edges (fst (obtain_progress os)) t) (min_label (fst (obtain_progress os)) t) =
   labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def all_edges_def all_vertices_def neighbors_def min_label_def obtain_progress_def
  by auto

lemma label_prop_upd_inv_produces[simp]:
  "label_prop_upd_inv (produces os batch) \<longleftrightarrow> label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def produces_def
  by (simp add: set_neighbors)


lemma label_prop_upd_inv_drop_caps[simp]:
  "label_prop_upd_inv (drop_caps os caps) \<longleftrightarrow> label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def drop_caps_def
  by (simp add: set_neighbors)

lemma label_prop_upd_inv_consume[simp]:
  "label_prop_upd_inv (consume os p t len) \<longleftrightarrow> label_prop_upd_inv os"
  by (cases "len = 0")
    (simp_all add: consume_def label_prop_upd_inv_def all_vertices_def all_edges_def set_neighbors)

lemma label_prop_upd_inv_delay_cap[simp]:
  "label_prop_upd_inv (delay_cap os cap incr) \<longleftrightarrow> label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def delay_cap_def
  by (simp add: set_neighbors)

lemma label_prop_upd_inv_add_cap[simp]:
  "label_prop_upd_inv (add_cap os p t) \<longleftrightarrow> label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def add_cap_def
  by (simp add: set_neighbors)

lemma label_prop_upd_inv_add_caps[simp]:
  "label_prop_upd_inv (add_caps os caps) \<longleftrightarrow> label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def add_caps_def
  by (simp add: set_neighbors)

lemma label_prop_upd_inv_drop_cap[simp]:
  "label_prop_upd_inv (drop_cap os cap) \<longleftrightarrow> label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def drop_cap_def
  by (simp add: set_neighbors)

lemma label_prop_upd_inv_obtain_progress[simp]:
  "label_prop_upd_inv (fst (obtain_progress os)) \<longleftrightarrow> label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def obtain_progress_def
  by (simp add: set_neighbors)

lemma label_prop_upd_inv_upd_outpu[simp]:
  "label_prop_upd_inv (os\<lparr>outpu := xs\<rparr>) = label_prop_upd_inv os"
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def obtain_progress_def
  by (simp add: set_neighbors)

lemma label_prop_upd_inv_release_caps[simp]:
  "label_prop_upd_inv (release_caps os p) \<longleftrightarrow> label_prop_upd_inv os"
  unfolding release_caps_def
  using label_prop_upd_inv_drop_caps
  by simp



lemma timestamps_add_caps[simp]:
  "timestamps (add_caps os caps) = timestamps os"
  unfolding add_caps_def by auto

lemma graph_add_caps[simp]:
  "label_propagation_state.graph (add_caps os caps) = label_propagation_state.graph os"
  unfolding add_caps_def by auto

lemma vertices_add_caps[simp]:
  "vertices (add_caps os caps) = vertices os"
  unfolding add_caps_def by auto

lemma label_add_caps[simp]:
  "label (add_caps os caps) = label os"
  unfolding add_caps_def by auto



lemma timestamps_input_tl[simp]:
  "timestamps (input_tl os p) = timestamps os"
  unfolding input_tl_def by auto

lemma graph_input_tl[simp]:
  "label_propagation_state.graph (input_tl os p) = label_propagation_state.graph os"
  unfolding input_tl_def by auto

lemma vertices_input_tl[simp]:
  "vertices (input_tl os p) = vertices os"
  unfolding input_tl_def by auto

lemma label_input_tl[simp]:
  "label (input_tl os p) = label os"
  unfolding input_tl_def by auto

lemma intsum_label_prop_edge_record_update[simp]:
  "intsum (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = intsum os"
  unfolding label_prop_edge_record_update_def by auto

lemma consu_label_prop_edge_record_update[simp]:
  "consu (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = consu os"
  unfolding label_prop_edge_record_update_def by auto

lemma inter_label_prop_edge_record_update[simp]:
  "inter (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = inter os"
  unfolding label_prop_edge_record_update_def by auto

lemma produ_label_prop_edge_record_update[simp]:
  "produ (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = produ os"
  unfolding label_prop_edge_record_update_def by auto

lemma input_label_prop_edge_record_update[simp]:
  "input (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = input os"
  unfolding label_prop_edge_record_update_def by auto

lemma outpu_label_prop_edge_record_update[simp]:
  "outpu (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = outpu os"
  unfolding label_prop_edge_record_update_def by auto

lemma front_label_prop_edge_record_update[simp]:
  "front (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = front os"
  unfolding label_prop_edge_record_update_def by auto

lemma ocaps_label_prop_edge_record_update[simp]:
  "ocaps (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = ocaps os"
  unfolding label_prop_edge_record_update_def by auto

lemma initia_label_prop_edge_record_update[simp]:
  "initia (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = initia os"
  unfolding label_prop_edge_record_update_def by auto

lemma en1_label_prop_edge_record_update[simp]:
  "en1 (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = en1 os"
  unfolding label_prop_edge_record_update_def by auto

lemma de1_label_prop_edge_record_update[simp]:
  "de1 (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = de1 os"
  unfolding label_prop_edge_record_update_def by auto

lemma is_en1_label_prop_edge_record_update[simp]:
  "is_en1 (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = is_en1 os"
  unfolding label_prop_edge_record_update_def by auto

lemma en2_label_prop_edge_record_update[simp]:
  "en2 (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = en2 os"
  unfolding label_prop_edge_record_update_def by auto

lemma de2_label_prop_edge_record_update[simp]:
  "de2 (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = de2 os"
  unfolding label_prop_edge_record_update_def by auto

lemma is_en2_label_prop_edge_record_update[simp]:
  "is_en2 (label_prop_edge_record_update os event_t src_v dst_v updated_v updated_label) = is_en2 os"
  unfolding label_prop_edge_record_update_def by auto

lemma intsum_label_prop_label_record_update[simp]:
  "intsum (label_prop_label_record_update os event_t vertex assigned_label) = intsum os"
  unfolding label_prop_label_record_update_def by auto

lemma consu_label_prop_label_record_update[simp]:
  "consu (label_prop_label_record_update os event_t vertex assigned_label) = consu os"
  unfolding label_prop_label_record_update_def by auto

lemma inter_label_prop_label_record_update[simp]:
  "inter (label_prop_label_record_update os event_t vertex assigned_label) = inter os"
  unfolding label_prop_label_record_update_def by auto

lemma produ_label_prop_label_record_update[simp]:
  "produ (label_prop_label_record_update os event_t vertex assigned_label) = produ os"
  unfolding label_prop_label_record_update_def by auto

lemma input_label_prop_label_record_update[simp]:
  "input (label_prop_label_record_update os event_t vertex assigned_label) = input os"
  unfolding label_prop_label_record_update_def by auto

lemma outpu_label_prop_label_record_update[simp]:
  "outpu (label_prop_label_record_update os event_t vertex assigned_label) = outpu os"
  unfolding label_prop_label_record_update_def by auto

lemma front_label_prop_label_record_update[simp]:
  "front (label_prop_label_record_update os event_t vertex assigned_label) = front os"
  unfolding label_prop_label_record_update_def by auto

lemma ocaps_label_prop_label_record_update[simp]:
  "ocaps (label_prop_label_record_update os event_t vertex assigned_label) = ocaps os"
  unfolding label_prop_label_record_update_def by auto

lemma initia_label_prop_label_record_update[simp]:
  "initia (label_prop_label_record_update os event_t vertex assigned_label) = initia os"
  unfolding label_prop_label_record_update_def by auto

lemma en1_label_prop_label_record_update[simp]:
  "en1 (label_prop_label_record_update os event_t vertex assigned_label) = en1 os"
  unfolding label_prop_label_record_update_def by auto

lemma de1_label_prop_label_record_update[simp]:
  "de1 (label_prop_label_record_update os event_t vertex assigned_label) = de1 os"
  unfolding label_prop_label_record_update_def by auto

lemma is_en1_label_prop_label_record_update[simp]:
  "is_en1 (label_prop_label_record_update os event_t vertex assigned_label) = is_en1 os"
  unfolding label_prop_label_record_update_def by auto

lemma en2_label_prop_label_record_update[simp]:
  "en2 (label_prop_label_record_update os event_t vertex assigned_label) = en2 os"
  unfolding label_prop_label_record_update_def by auto

lemma de2_label_prop_label_record_update[simp]:
  "de2 (label_prop_label_record_update os event_t vertex assigned_label) = de2 os"
  unfolding label_prop_label_record_update_def by auto

lemma is_en2_label_prop_label_record_update[simp]:
  "is_en2 (label_prop_label_record_update os event_t vertex assigned_label) = is_en2 os"
  unfolding label_prop_label_record_update_def by auto

lemma timestamps_label_prop_label_record_update[simp]:
  "timestamps (label_prop_label_record_update os event_t vertex assigned_label) = timestamps os"
  unfolding label_prop_label_record_update_def by auto

lemma graph_label_prop_label_record_update[simp]:
  "label_propagation_state.graph (label_prop_label_record_update os event_t vertex assigned_label) = label_propagation_state.graph os"
  unfolding label_prop_label_record_update_def by auto

lemma vertices_label_prop_label_record_update[simp]:
  "vertices (label_prop_label_record_update os event_t vertex assigned_label) = vertices os"
  unfolding label_prop_label_record_update_def by auto




lemma timestamps_consumes[simp]:
  "timestamps (consumes os p t d) = timestamps os"
  unfolding consumes_def add_caps_def BENQ_def by auto

lemma graph_consumes[simp]:
  "label_propagation_state.graph (consumes os p t d) = label_propagation_state.graph os"
  unfolding consumes_def add_caps_def BENQ_def by auto

lemma vertices_consumes[simp]:
  "vertices (consumes os p t d) = vertices os"
  unfolding consumes_def add_caps_def BENQ_def by auto

lemma label_consumes[simp]:
  "label (consumes os p t d) = label os"
  unfolding consumes_def add_caps_def BENQ_def by auto

lemma all_vertices_consumes[simp]:
  "all_vertices (consumes os p t d) = all_vertices os"
  unfolding all_vertices_def by simp

lemma neighbors_consumes[simp]:
  "neighbors (consumes os p t d) = neighbors os"
  unfolding neighbors_def by simp

lemma all_edges_consumes_label_state[simp]:
  "all_edges (consumes os p t d) = all_edges os"
  unfolding all_edges_def by simp

lemma min_label_consumes_label_state[simp]:
  "min_label (consumes os p t d) = min_label os"
  unfolding min_label_def by simp

lemma timestamps_fold_consumes[simp]:
  "timestamps (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = timestamps os"
  by (induct xs arbitrary: os) auto

lemma graph_fold_consumes[simp]:
  "label_propagation_state.graph (fold (\<lambda>(d, t) os. consumes os p t d) xs os) =
    label_propagation_state.graph os"
  by (induct xs arbitrary: os) auto

lemma vertices_fold_consumes[simp]:
  "vertices (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = vertices os"
  by (induct xs arbitrary: os) auto

lemma label_fold_consumes[simp]:
  "label (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = label os"
  by (induct xs arbitrary: os) auto

lemma all_vertices_fold_consumes[simp]:
  "all_vertices (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = all_vertices os"
  unfolding all_vertices_def by simp

lemma neighbors_fold_consumes[simp]:
  "neighbors (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = neighbors os"
  unfolding neighbors_def by simp

lemma all_edges_fold_consumes[simp]:
  "all_edges (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = all_edges os"
  unfolding all_edges_def by simp

lemma min_label_fold_consumes[simp]:
  "min_label (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = min_label os"
  unfolding min_label_def by simp

lemma all_vertices_outpu_upd[simp]:
  "all_vertices (os_label_prop\<lparr>outpu := A\<rparr>) = all_vertices os_label_prop"
  unfolding all_vertices_def
  by auto

lemma all_vertices_input_upd[simp]:
  \<open>all_vertices (os_label_prop\<lparr>input := xs\<rparr>) = all_vertices os_label_prop\<close>
  unfolding all_vertices_def
  by auto

lemma label_prop_upd_inv_input0_preserved:
  fixes t1 :: "'t::order"
  assumes inv: "label_prop_upd_inv os"
    and timestamps_eq: "timestamps os' = t1 # timestamps os"
    and graph_eq: "graph os' = (graph os)(t1 := (graph os t1)(v1 := v2 # graph os t1 v1,
          v2 := v1 # graph os t1 v2))"
    and vertices_eq: "vertices os' = (vertices os)(t1 := [v1, v2] @ vertices os t1)"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(v := l))"
    and input1_eq: "input os' 1 = input os 1"
    and de1_eq: "de1 os' = de1 os"
    and label_update:
    "(v, l) = (if min_label os t1 v1 > min_label os t1 v2
        then (v1, min_label os t1 v2)
        else (v2, min_label os t1 v1))"
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows "label_prop_upd_inv os'"
proof -
  have ts_old: "\<And>q. q \<in> set (timestamps os) \<longleftrightarrow>
      edge_vertices {(a, b). b \<in> set (graph os q a)} \<noteq> {}"
    and vertices_old: "\<And>q. set (vertices os q) = edge_vertices {(a, b). b \<in> set (graph os q a)}"
    and sym_old: "\<And>q. sym {(a, b). b \<in> set (graph os q a)}"
    and label_old: "\<And>q x. x \<notin> all_vertices os q \<Longrightarrow> label os q x = x"
    and label5_old: "\<And>q x. q \<notin> set (timestamps os) \<Longrightarrow> label os q x = x"
    and label6_old: "\<And>q x. label os q x \<le> x"
    using inv unfolding label_prop_upd_inv_def by metis+
  have old_edges_subset: "\<And>q. all_edges os q \<subseteq> all_edges os' q"
    using timestamps_eq graph_eq vertices_eq
    unfolding all_edges_def all_vertices_def set_neighbors
    by auto

  have v_new: "v = v1 \<or> v = v2"
    using label_update by (auto split: if_splits)
  have edge_vertices_new:
    "\<And>q. edge_vertices {(a, b). b \<in> set (graph os' q a)} =
      (if q = t1
       then insert v1 (insert v2 (edge_vertices {(a, b). b \<in> set (graph os q a)}))
       else edge_vertices {(a, b). b \<in> set (graph os q a)})"
    using graph_eq unfolding edge_vertices_def Field_def by (auto split: if_splits)
  have vertices_new:
    "\<And>q. set (vertices os' q) =
      (if q = t1 then insert v1 (insert v2 (set (vertices os q))) else set (vertices os q))"
    using vertices_eq by (auto split: if_splits)
  have all_vertices_mono: "\<And>q x. x \<in> all_vertices os q \<Longrightarrow> x \<in> all_vertices os' q"
    using timestamps_eq vertices_eq unfolding all_vertices_def by (auto split: if_splits)

  have ts_new: "\<And>q. q \<in> set (timestamps os') \<longleftrightarrow>
      edge_vertices {(a, b). b \<in> set (graph os' q a)} \<noteq> {}"
    using ts_old edge_vertices_new timestamps_eq by auto
  have vertices_eq_new: "\<And>q. set (vertices os' q) =
      edge_vertices {(a, b). b \<in> set (graph os' q a)}"
    using vertices_old vertices_new edge_vertices_new by auto
  have sym_new: "\<And>q. sym {(a, b). b \<in> set (graph os' q a)}"
    using sym_old graph_eq unfolding sym_def by (auto split: if_splits)
  have label_new: "\<And>q x. x \<notin> all_vertices os' q \<Longrightarrow> label os' q x = x"
  proof -
    fix q x
    assume not_new: "x \<notin> all_vertices os' q"
    show "label os' q x = x"
    proof (cases "q = t1 \<and> x = v")
      case True
      then have "x \<in> all_vertices os' q"
        using timestamps_eq vertices_eq v_new unfolding all_vertices_def by auto
      then show ?thesis
        using not_new by contradiction
    next
      case False
      have not_old: "x \<notin> all_vertices os q"
        using all_vertices_mono not_new by blast
      then show ?thesis
        using label_old[OF not_old] label_eq False by auto
    qed
  qed
  have wf_upd_new: \<open>wf_label_prop_updates os' (set (input os' 1))\<close>
    using input1_eq timestamps_eq all_vertices_mono de1_eq old_edges_subset cc_of_mono wf_upd
    unfolding wf_label_prop_updates_def by (smt (verit, best) list.set_intros(2) split_beta')
  have label5_new: "\<And>q x. q \<notin> set (timestamps os') \<Longrightarrow> label os' q x = x"
    using label5_old timestamps_eq by (auto simp add: label_eq)
  have l_le_v: "l \<le> v"
  proof -
    have "l \<le> min_label os t1 v"
      using label_update by (auto split: if_splits simp add: less_imp_le)
    also have "min_label os t1 v \<le> label os t1 v"
      by (rule min_label_le_current_labelI)
    also have "label os t1 v \<le> v"
      by (rule label6_old)
    finally show ?thesis .
  qed
  have label6_new: "\<And>q x. label os' q x \<le> x"
    using label6_old l_le_v by (auto simp add: label_eq)
  show ?thesis
    unfolding label_prop_upd_inv_def
    using ts_new vertices_eq_new sym_new label_new label5_new label6_new wf_upd_new by blast
qed

lemma label_prop_upd_inv_cong:
  \<open>input os' 1 = input os 1 \<Longrightarrow> de1 os' = de1 os \<Longrightarrow> timestamps os' = timestamps os \<Longrightarrow>
  graph os' = graph os \<Longrightarrow> vertices os' = vertices os \<Longrightarrow> label os' = label os \<Longrightarrow>
  label_prop_upd_inv os \<longleftrightarrow> label_prop_upd_inv os'\<close>
  unfolding label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def by simp

lemma label_prop_upd_inv_input1_preserved:
  fixes t1 :: "'t::order"
  assumes inv: "label_prop_upd_inv os"
    and input1: "input os 1 = (d, t) # xs"
    and input1_eq: "input os' 1 = xs"
    and msg: "de1 os d = (v, l)"
    and t1_def: "t1 = myfst t"
    and timestamps_eq: "timestamps os' = timestamps os"
    and graph_eq: "graph os' = graph os"
    and vertices_eq: "vertices os' = vertices os"
    and de1_eq: "de1 os' = de1 os"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(v := min (min_label os t1 v) l))"
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows "label_prop_upd_inv os'"
proof -
  have ts_old: "\<And>q. q \<in> set (timestamps os) \<longleftrightarrow>
      edge_vertices {(a, b). b \<in> set (graph os q a)} \<noteq> {}"
    and vertices_old: "\<And>q. set (vertices os q) = edge_vertices {(a, b). b \<in> set (graph os q a)}"
    and sym_old: "\<And>q. sym {(a, b). b \<in> set (graph os q a)}"
    and label_old: "\<And>q x. x \<notin> all_vertices os q \<Longrightarrow> label os q x = x"
    and label5_old: "\<And>q x. q \<notin> set (timestamps os) \<Longrightarrow> label os q x = x"
    and label6_old: "\<And>q x. label os q x \<le> x"
    using inv unfolding label_prop_upd_inv_def by metis+

  have all_edges_eq: "\<And>q. all_edges os' q = all_edges os q"
    unfolding all_edges_def all_vertices_def set_neighbors
    using timestamps_eq graph_eq vertices_eq by simp

  have v_in: "v \<in> all_vertices os t1"
  proof -
    have in_set: "(d, t) \<in> set (input os 1)" using input1 by simp
    then have "fst (de1 os d) \<in> all_vertices os (myfst t)"
      using wf_upd unfolding wf_label_prop_updates_def by fast
    then show ?thesis using msg t1_def by auto
  qed

  have t1_ts: "t1 \<in> set (timestamps os)"
    using wf_upd input1 t1_def unfolding wf_label_prop_updates_def by fastforce

  have ts_new: "\<And>q. q \<in> set (timestamps os') \<longleftrightarrow>
      edge_vertices {(a, b). b \<in> set (graph os' q a)} \<noteq> {}"
    using ts_old timestamps_eq graph_eq by simp
  have vertices_new: "\<And>q. set (vertices os' q) =
      edge_vertices {(a, b). b \<in> set (graph os' q a)}"
    using vertices_old vertices_eq graph_eq by simp
  have sym_new: "\<And>q. sym {(a, b). b \<in> set (graph os' q a)}"
    using sym_old graph_eq by simp

  have label_new: "\<And>q x. x \<notin> all_vertices os' q \<Longrightarrow> label os' q x = x"
  proof -
    fix q x
    assume not_in: "x \<notin> all_vertices os' q"
    have all_vertices_eq: "all_vertices os' q = all_vertices os q"
      using timestamps_eq vertices_eq unfolding all_vertices_def by auto
    have not_in_old: "x \<notin> all_vertices os q"
      using not_in all_vertices_eq by simp
    show "label os' q x = x"
    proof (cases "q = t1 \<and> x = v")
      case True
      then have "x \<in> all_vertices os q"
        using v_in by simp
      then show ?thesis
        using not_in_old by contradiction
    next
      case False
      then show ?thesis
        using label_old[OF not_in_old] label_eq by auto
    qed
  qed
  have wf_upd_new: \<open>wf_label_prop_updates os' (set (input os' 1))\<close>
    using input1_eq input1 timestamps_eq vertices_eq de1_eq all_edges_eq wf_upd
    unfolding wf_label_prop_updates_def all_vertices_def by simp
  have label5_new: "\<And>q x. q \<notin> set (timestamps os') \<Longrightarrow> label os' q x = x"
    using label5_old timestamps_eq t1_ts by (auto simp add: label_eq)
  have upd_le: "min (min_label os t1 v) l \<le> v"
    using min_label_le_current_labelI[of os t1 v] label6_old[of t1 v]
    by (meson min.coboundedI1 order_trans)
  have label6_new: "\<And>q x. label os' q x \<le> x"
    using label6_old upd_le by (auto simp add: label_eq)
  show ?thesis
    unfolding label_prop_upd_inv_def
    using ts_new vertices_new sym_new label_new label5_new label6_new wf_upd_new by blast
qed



lemma label_prop_upd_inv_output_preserved:
  assumes inv: "label_prop_upd_inv os"
  shows "label_prop_upd_inv (drop_caps (produces os batch) caps)"
  oops

lemma labels_inv_input0_preserved:
  fixes q t1 :: "'t::order"
  assumes labels: "\<And>q. labels_inv (all_edges os q) (min_label os q)"
    and inv: "label_prop_upd_inv os"
    and input_eq: "input os' = (input os)(0 := xs)"
    and timestamps_eq: "timestamps os' = t1 # timestamps os"
    and graph_eq: "graph os' = (graph os)(t1 := (graph os t1)(v1 := v2 # graph os t1 v1,
          v2 := v1 # graph os t1 v2))"
    and vertices_eq: "vertices os' = (vertices os)(t1 := [v1, v2] @ vertices os t1)"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(v := l))"
    and label_update:
    "(v, l) = (if min_label os t1 v1 > min_label os t1 v2
        then (v1, min_label os t1 v2)
        else (v2, min_label os t1 v1))"
  shows "labels_inv (all_edges os' q) (min_label os' q)"

proof -
  have old_edges_subset: "all_edges os q \<subseteq> all_edges os' q"
    using timestamps_eq graph_eq vertices_eq
    unfolding all_edges_def all_vertices_def set_neighbors
    by auto

  have v2_cc_v1: "t1 \<le> q \<Longrightarrow> v2 \<in> cc_of (all_edges os' q) v1"
    using timestamps_eq graph_eq vertices_eq
    unfolding cc_of_def reachable_def all_edges_def all_vertices_def set_neighbors edge_vertices_def Field_def
    by auto
  have v1_cc_v2: "t1 \<le> q \<Longrightarrow> v1 \<in> cc_of (all_edges os' q) v2"
    using timestamps_eq graph_eq vertices_eq
    unfolding cc_of_def reachable_def all_edges_def all_vertices_def set_neighbors edge_vertices_def Field_def
    by auto
  have updated_label_valid: "t1 \<le> q \<Longrightarrow> l \<in> cc_of (all_edges os' q) v"
  proof -
    assume t1_le_q: "t1 \<le> q"
    show "l \<in> cc_of (all_edges os' q) v"
    proof (cases "min_label os t1 v1 > min_label os t1 v2")
      case True
      then have v_def: "v = v1" and l_def: "l = min_label os t1 v2"
        using label_update by auto
      show ?thesis
      proof (cases "v2 \<in> all_vertices os q")
        case True
        have old_valid: "min_label os t1 v2 \<in> cc_of (all_edges os q) v2"
          using labels_inv_min_label_le[OF labels inv t1_le_q True] .

        then have new_valid: "min_label os t1 v2 \<in> cc_of (all_edges os' q) v2"
          using old_edges_subset cc_of_mono by blast

        have "cc_of (all_edges os' q) v2 = cc_of (all_edges os' q) v1"
          using v2_cc_v1[OF t1_le_q] by (rule cc_of_eq_if_member)
        then show ?thesis
          using new_valid v_def l_def by simp
      next
        case False
        then have "v2 \<notin> all_vertices os t1"
          using t1_le_q unfolding all_vertices_def by auto
        then have "min_label os t1 v2 = v2"
          using min_label_eq_self_if_not_all_vertices'[OF inv] by simp
        then show ?thesis
          using v2_cc_v1[OF t1_le_q] v_def l_def by simp
      qed
    next
      case False
      then have v_def: "v = v2" and l_def: "l = min_label os t1 v1"
        using label_update by auto
      show ?thesis
      proof (cases "v1 \<in> all_vertices os q")
        case True
        have old_valid: "min_label os t1 v1 \<in> cc_of (all_edges os q) v1"
          using labels_inv_min_label_le[OF labels inv t1_le_q True] .

        then have new_valid: "min_label os t1 v1 \<in> cc_of (all_edges os' q) v1"
          using old_edges_subset cc_of_mono by blast

        have "cc_of (all_edges os' q) v1 = cc_of (all_edges os' q) v2"
          using v1_cc_v2[OF t1_le_q] by (rule cc_of_eq_if_member)
        then show ?thesis
          using new_valid v_def l_def by simp
      next
        case False
        then have "v1 \<notin> all_vertices os t1"
          using t1_le_q unfolding all_vertices_def by auto
        then have "min_label os t1 v1 = v1"
          using min_label_eq_self_if_not_all_vertices'[OF inv] by simp
        then show ?thesis
          using v1_cc_v2[OF t1_le_q] v_def l_def by simp
      qed
    qed
  qed

  show ?thesis
    unfolding labels_inv_def
  proof safe
    fix x
    assume x_new: "x \<in> edge_vertices (all_edges os' q)"
    then have x_new_vertices: "x \<in> all_vertices os' q"
      using edge_vertices_all_edges_subset_all_vertices[of os' q] by blast

    show "min_label os' q x \<in> cc_of (all_edges os' q) x"
    proof (cases "t1 \<le> q")
      case False
      have times_eq: "{r \<in> set (timestamps os'). r \<le> q} = {r \<in> set (timestamps os). r \<le> q}"
        using False timestamps_eq by auto
      have vertices_eq_q: "\<And>r. r \<le> q \<Longrightarrow> vertices os' r = vertices os r"
        using False vertices_eq by auto
      have x_old: "x \<in> all_vertices os q"
        using x_new_vertices times_eq vertices_eq_q unfolding all_vertices_def by auto
      then have x_edge_old: "x \<in> edge_vertices (all_edges os q)"
        using edge_vertices_all_edges[OF inv, of q] by simp
      have label_eq_q: "\<And>r. r \<le> q \<Longrightarrow> label os' r x = label os r x"
        using False label_eq by auto
      have min_eq: "min_label os' q x = min_label os q x"
        using times_eq label_eq_q unfolding min_label_def by auto

      have edges_eq: "all_edges os' q = all_edges os q"
        using False timestamps_eq graph_eq vertices_eq
        unfolding all_edges_def all_vertices_def set_neighbors by auto
      show ?thesis
        using labels[of q] x_edge_old min_eq edges_eq unfolding labels_inv_def by simp

    next
      case True
      have updated_label_le: "l \<le> min_label os t1 v"
        using label_update by (auto split: if_splits)
      have new_self_valid:
        "\<And>y. y \<in> all_vertices os' q \<Longrightarrow> y \<notin> all_vertices os q \<Longrightarrow> y \<in> cc_of (all_edges os' q) y"
      proof -
        fix y
        assume y_new: "y \<in> all_vertices os' q"
          and y_not_old: "y \<notin> all_vertices os q"
        have vertices_t1_old: "set (vertices os t1) \<subseteq> all_vertices os q"
        proof (cases "t1 \<in> set (timestamps os)")
          case True
          then show ?thesis
            using \<open>t1 \<le> q\<close> unfolding all_vertices_def by auto
        next
          case False
          then show ?thesis
            using label_prop_upd_inv_vertices_timestamps_iff[OF inv, of t1] by auto
        qed
        have vertices_subset:
          "all_vertices os' q \<subseteq> insert v1 (insert v2 (all_vertices os q))"
        proof
          fix z
          assume "z \<in> all_vertices os' q"
          then obtain r where r_ts: "r \<in> set (timestamps os')" and r_le: "r \<le> q"
            and z_in: "z \<in> set (vertices os' r)"
            unfolding all_vertices_def by auto
          show "z \<in> insert v1 (insert v2 (all_vertices os q))"
          proof (cases "r = t1")
            case True
            then have "z = v1 \<or> z = v2 \<or> z \<in> set (vertices os t1)"
              using z_in vertices_eq by auto
            then show ?thesis
              using vertices_t1_old by auto
          next
            case False
            then have "r \<in> set (timestamps os)"
              using r_ts timestamps_eq by auto
            moreover have "z \<in> set (vertices os r)"
              using False z_in vertices_eq by auto
            ultimately show ?thesis
              using r_le unfolding all_vertices_def by auto
          qed
        qed


        have "y \<in> insert v1 (insert v2 (all_vertices os q))"
          using vertices_subset y_new by blast
        then have "y = v1 \<or> y = v2"
          using y_not_old by auto


        then show "y \<in> cc_of (all_edges os' q) y"
        proof
          assume "y = v1"
          then show ?thesis
            using v1_cc_v2[OF True] unfolding cc_of_def reachable_def by auto
        next
          assume "y = v2"
          then show ?thesis
            using v2_cc_v1[OF True] unfolding cc_of_def reachable_def by auto
        qed
      qed
      have old_q_valid: "min_label os q x \<in> cc_of (all_edges os' q) x"
      proof (cases "x \<in> all_vertices os q")
        case True
        then have x_edge: "x \<in> edge_vertices (all_edges os q)"
          using edge_vertices_all_edges[OF inv, of q] by simp
        have "min_label os q x \<in> cc_of (all_edges os q) x"
          using labels[of q] x_edge unfolding labels_inv_def by blast
        then show ?thesis

          using old_edges_subset cc_of_mono by blast
      next
        case False
        then have "min_label os q x = x"
          using min_label_eq_self_if_not_all_vertices'[OF inv] by simp
        then show ?thesis
          using new_self_valid[OF x_new_vertices False] by simp

      qed
      have old_t1_valid: "min_label os t1 x \<in> cc_of (all_edges os' q) x"
      proof (cases "x \<in> all_vertices os q")
        case True
        have "min_label os t1 x \<in> cc_of (all_edges os q) x"
          using labels_inv_min_label_le[OF labels inv \<open>t1 \<le> q\<close> True] .
        then show ?thesis
          using old_edges_subset cc_of_mono by blast

      next
        case False
        then have "x \<notin> all_vertices os t1"
          using \<open>t1 \<le> q\<close> unfolding all_vertices_def by auto
        then have "min_label os t1 x = x"
          using min_label_eq_self_if_not_all_vertices'[OF inv] by simp
        then show ?thesis
          using new_self_valid[OF x_new_vertices False] by simp

      qed
      have min_cases:
        "min_label os' q x = min_label os q x \<or>
         min_label os' q x = min_label os t1 x \<or>
         (x = v \<and> min_label os' q x = l)"
        using min_label_input0_update_cases[OF \<open>t1 \<le> q\<close> timestamps_eq label_eq updated_label_le, of x] .
      then show ?thesis
      proof (elim disjE conjE)
        assume "min_label os' q x = min_label os q x"
        then show ?thesis
          using old_q_valid by simp
      next
        assume "min_label os' q x = min_label os t1 x"
        then show ?thesis
          using old_t1_valid by simp
      next
        assume "x = v" and "min_label os' q x = l"
        then show ?thesis
          using updated_label_valid[OF \<open>t1 \<le> q\<close>] by simp
      qed




    qed
  qed



qed











section \<open>Label Invariants under Input Steps\<close>

text \<open>Preservation of labels_inv and labels_stable across input steps and
  record updates.\<close>

lemma min_label_label_update_v_cases:
  fixes q t1 :: "'t::order"
  assumes timestamps_eq: "timestamps os' = timestamps os"
    and label_eq: "label os' = (label os)(t1 := (label os t1)(v := l_new))"
    and new_le: "l_new \<le> min_label os t1 v"
  shows "min_label os' q x = min_label os q x \<or> (x = v \<and> min_label os' q x = l_new)"
proof (cases "x = v")
  case False
  have label_x_eq: "\<And>t'. label os' t' x = label os t' x"
    using label_eq False by (auto simp: fun_upd_def)
  show ?thesis
    unfolding min_label_def using label_x_eq timestamps_eq by simp
next
  case True
  let ?ts = "{t' \<in> set (timestamps os). t' \<le> q}"
  let ?img = "(\<lambda>t'. label os t' v) ` ?ts"
  let ?img' = "(\<lambda>t'. label os' t' v) ` ?ts"
  let ?S = "insert (label os q v) ?img"
  let ?S' = "insert (label os' q v) ?img'"
  have ts_eq': "{t' \<in> set (timestamps os'). t' \<le> q} = ?ts"
    using timestamps_eq by simp
  have min_S': "min_label os' q v = Min ?S'"
    unfolding min_label_def using ts_eq' by simp
  have min_S: "min_label os q v = Min ?S"
    unfolding min_label_def by simp

  have S'_sub_ins_S: "?S' \<subseteq> insert l_new ?S"
  proof
    fix y assume "y \<in> ?S'"
    then consider "y = label os' q v" | t' where "t' \<in> ?ts" "y = label os' t' v" by blast
    then show "y \<in> insert l_new ?S"
    proof cases
      case 1
      then show ?thesis
        by (cases "q = t1") (auto simp: label_eq)
    next
      case (2 t')
      then show ?thesis
        by (cases "t' = t1") (auto simp: label_eq)
    qed
  qed

  have lnew_le_label_t1: "l_new \<le> label os t1 v"
  proof -
    have "min_label os t1 v \<le> label os t1 v"
      unfolding min_label_def by (intro Min_le) auto
    then show ?thesis using new_le by simp
  qed

  have fin_S': "finite ?S'" by auto
  have fin_S: "finite ?S" by auto
  have ne_S: "?S \<noteq> {}" by auto
  have ne_S': "?S' \<noteq> {}" by auto

  show ?thesis
  proof (cases "Min ?S' = l_new")
    case True
    then show ?thesis using \<open>x = v\<close> min_S' by simp
  next
    case False
    have min_in_S': "Min ?S' \<in> ?S'"
      using fin_S' ne_S' by (intro Min_in) auto
    then have min_in_S: "Min ?S' \<in> ?S"
      using S'_sub_ins_S False by auto
    then have lower: "Min ?S \<le> Min ?S'"
      using Min_le[OF fin_S min_in_S] by simp

    have upper: "Min ?S' \<le> Min ?S"
    proof (rule Min.boundedI[OF fin_S ne_S])
      fix y assume y_in: "y \<in> ?S"
      then consider "y = label os q v" | t' where "t' \<in> ?ts" "y = label os t' v" by blast
      then show "Min ?S' \<le> y"
      proof cases
        case 1
        show ?thesis
        proof (cases "q = t1")
          case True
          then have y_eq: "y = label os t1 v" using 1 by simp
          have "label os' q v = l_new"
            using True label_eq by simp
          then have "l_new \<in> ?S'" by auto
          then have "Min ?S' \<le> l_new"
            using fin_S' Min_le by auto
          also have "l_new \<le> y" using lnew_le_label_t1 y_eq by simp
          finally show ?thesis .
        next
          case False
          then have "label os' q v = label os q v"
            using label_eq by simp
          then have "y \<in> ?S'" using 1 by auto
          then show ?thesis
            using fin_S' Min_le by auto
        qed
      next
        case (2 t')
        show ?thesis
        proof (cases "t' = t1")
          case True
          then have y_eq: "y = label os t1 v" using 2 by simp
          have "label os' t1 v = l_new"
            using label_eq by simp
          moreover have "t1 \<in> ?ts"
            using True 2 by simp
          ultimately have "l_new \<in> ?img'"
            by (metis (mono_tags, lifting) image_eqI)
          then have "l_new \<in> ?S'" by simp
          then have "Min ?S' \<le> l_new"
            using fin_S' Min_le by auto
          also have "l_new \<le> y" using lnew_le_label_t1 y_eq by simp
          finally show ?thesis .
        next
          case False
          then have "label os' t' v = label os t' v"
            using label_eq by simp
          then have "y \<in> ?img'" using 2 by force
          then have "y \<in> ?S'" by simp
          then show ?thesis
            using fin_S' Min_le by auto
        qed
      qed
    qed

    from upper lower have "Min ?S' = Min ?S" by (rule antisym)
    then show ?thesis using \<open>x = v\<close> min_S' min_S by simp
  qed
qed

lemma labels_inv_input1_preserved:
  fixes q t1 :: "'t::order"
  assumes labels: "\<And>q. labels_inv (all_edges os q) (min_label os q)"
    and inv: "label_prop_upd_inv os"
    and pending: "(d, t) \<in> set (input os 1)"
    and msg: "de1 os d = (v, l)"
    and t1_def: "t1 = myfst t"
    and timestamps_eq: "timestamps os' = timestamps os"
    and graph_eq: "graph os' = graph os"
    and vertices_eq: "vertices os' = vertices os"
    and label_eq:
      "label os' = (label os)(t1 := (label os t1)(v := min (min_label os t1 v) l))"
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows "labels_inv (all_edges os' q) (min_label os' q)"
proof -
  have msg_valid: "\<And>q. t1 \<le> q \<Longrightarrow> l \<in> cc_of (all_edges os q) v"
  proof -
    fix q assume "t1 \<le> q"
    then have "myfst t \<le> q" using t1_def by simp
    then have "snd (de1 os d) \<in> cc_of (all_edges os q) (fst (de1 os d))"
      using wf_upd pending unfolding wf_label_prop_updates_def by blast
    then show "l \<in> cc_of (all_edges os q) v"
      using msg by simp
  qed
  define l_new where "l_new = min (min_label os t1 v) l"
  have label_eq': "label os' = (label os)(t1 := (label os t1)(v := l_new))"
    using label_eq unfolding l_new_def by simp
  have new_le: "l_new \<le> min_label os t1 v"
    unfolding l_new_def by simp

  have all_vertices_eq: "all_vertices os' = all_vertices os"
    unfolding all_vertices_def using timestamps_eq vertices_eq by simp
  have all_edges_eq: "\<And>r. all_edges os' r = all_edges os r"
    unfolding all_edges_def all_vertices_def set_neighbors
    using timestamps_eq vertices_eq graph_eq by auto

  show ?thesis
    unfolding labels_inv_def
  proof safe
    fix x
    assume x_new: "x \<in> edge_vertices (all_edges os' q)"
    then have x_new_vertices: "x \<in> all_vertices os' q"
      using edge_vertices_all_edges_subset_all_vertices[of os' q] by blast
    then have x_old: "x \<in> all_vertices os q"
      using all_vertices_eq by simp
    then have x_edge_old: "x \<in> edge_vertices (all_edges os q)"
      using edge_vertices_all_edges[OF inv, of q] by simp
    have min_cases:
      "min_label os' q x = min_label os q x \<or> (x = v \<and> min_label os' q x = l_new)"
      using min_label_label_update_v_cases[OF timestamps_eq label_eq' new_le] .
    show "min_label os' q x \<in> cc_of (all_edges os' q) x"
    proof (cases "min_label os' q x = min_label os q x")
      case True
      have "min_label os q x \<in> cc_of (all_edges os q) x"
        using labels[of q] x_edge_old unfolding labels_inv_def by blast
      then show ?thesis using True all_edges_eq by simp
    next
      case False
      with min_cases have x_v: "x = v" and min_eq: "min_label os' q x = l_new" by auto
      show ?thesis
      proof (cases "t1 \<le> q")
        case True
        have v_in: "v \<in> all_vertices os q"
          using x_old x_v by simp
        have a: "min_label os t1 v \<in> cc_of (all_edges os q) v"
          using labels_inv_min_label_le[OF labels inv True v_in] .
        have b: "l \<in> cc_of (all_edges os q) v"
          using msg_valid[OF True] .
        have "l_new \<in> {min_label os t1 v, l}"
          unfolding l_new_def by (simp add: min_def)
        then have "l_new \<in> cc_of (all_edges os q) v"
          using a b by auto
        then show ?thesis using min_eq x_v all_edges_eq by simp
      next
        case False
        have label_eq_q: "\<And>t'. t' \<le> q \<Longrightarrow> label os' t' = label os t'"
          using label_eq' False by auto
        have label_at_q: "label os' q v = label os q v"
          using label_eq_q[of q] by simp
        have img_eq:
          "(\<lambda>t'. label os' t' v) ` {t' \<in> set (timestamps os'). t' \<le> q} =
           (\<lambda>t'. label os t' v) ` {t' \<in> set (timestamps os). t' \<le> q}"
          using timestamps_eq label_eq_q by auto
        have "min_label os' q v = min_label os q v"
          unfolding min_label_def using img_eq label_at_q by simp
        then show ?thesis using False min_eq x_v \<open>min_label os' q x \<noteq> min_label os q x\<close> by simp
      qed
    qed
  qed
qed



lemma labels_inv_input1_preserved_record_update_tl:
  fixes q t1 :: "'t::order"
  assumes labels: "\<And>q. labels_inv (all_edges os q) (min_label os q)"
    and inv: "label_prop_upd_inv os"
    and pending: "(d, t) \<in> set (input os 1)"
    and msg: "de1 os d = (v, l)"
    and t1_def: "t1 = myfst t"
    and update:
      "os' = label_prop_label_record_update (input_tl os 1) t1 v (min (min_label os t1 v) l)"
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows "labels_inv (all_edges os' q) (min_label os' q)"
proof (rule labels_inv_input1_preserved[OF labels inv pending msg t1_def _ _ _ _ wf_upd])
  show "timestamps os' = timestamps os"
    using update by simp
  show "graph os' = graph os"
    using update by simp
  show "vertices os' = vertices os"
    using update by simp
  show "label os' = (label os)(t1 := (label os t1)(v := min (min_label os t1 v) l))"
    using update unfolding label_prop_label_record_update_def by simp
qed

lemma min_label_outpu_upd[simp]:
  "min_label (os\<lparr>outpu := xs\<rparr>) = min_label os"
  unfolding min_label_def
  by auto


(* Preservation of labels_stable across the first branch of label_propagation_op_logic
   (input0: insertion of edge (v1, v2) at timestamp t1).

   The update can break labels_stable when t1 \<le> t': the new edge would force
   min_label os' t' v1 and min_label os' t' v2 to coincide, but min_label is the min
   over labels at all timestamps t'' \<le> t', so a t'' with t1 < t'' \<le> t' carrying a
   strictly smaller label at one endpoint can leave the other endpoint above it.

   We therefore restrict the query timestamp t' so that the inserted edge is not yet
   visible, i.e. \<not> t1 \<le> t'. Under this assumption all_edges and min_label at t'
   are unchanged, and stability transfers from os to os'. *)
lemma labels_stable_input0_preserved:
  fixes q t1 t' :: "'t::order"
  assumes stable: "labels_stable (all_edges os t') (min_label os t')"
    and time_not_le: "\<not> t1 \<le> t'"
    and ts_eq: "timestamps os' = t1 # timestamps os"
    and graph_eq:
      "graph os' = (graph os)(t1 := (graph os t1)(v1 := v2 # graph os t1 v1,
        v2 := v1 # graph os t1 v2))"
    and vertices_eq:
      "vertices os' = (vertices os)(t1 := [v1, v2] @ vertices os t1)"
    and label_eq:
      "label os' = (label os)(t1 := (label os t1)(v := l))"
    and label_update:
      "(v, l) = (if min_label os t1 v1 > min_label os t1 v2
        then (v1, min_label os t1 v2)
        else (v2, min_label os t1 v1))"
  shows "labels_stable (all_edges os' t') (min_label os' t')"
proof -
  have t'_ne_t1: "t' \<noteq> t1"
    using time_not_le by auto
  have filter_ts_eq:
    "{t'' \<in> set (timestamps os'). t'' \<le> t'} = {t'' \<in> set (timestamps os). t'' \<le> t'}"
    using ts_eq time_not_le by auto
  have label_on_filter:
    "\<And>v t''. t'' \<le> t' \<Longrightarrow> label os' t'' v = label os t'' v"
    using label_eq time_not_le by auto
  have vertices_on_filter:
    "\<And>t''. t'' \<le> t' \<Longrightarrow> vertices os' t'' = vertices os t''"
    using vertices_eq time_not_le by auto
  have graph_on_filter:
    "\<And>v t''. t'' \<le> t' \<Longrightarrow> graph os' t'' v = graph os t'' v"
    using graph_eq time_not_le by auto
  have all_vertices_eq: "all_vertices os' t' = all_vertices os t'"
    using filter_ts_eq vertices_on_filter
    unfolding all_vertices_def by auto
  have neighbors_eq: "\<And>v. set (neighbors os' t' v) = set (neighbors os t' v)"
    using filter_ts_eq graph_on_filter
    unfolding set_neighbors by auto
  have all_edges_eq: "all_edges os' t' = all_edges os t'"
    using all_vertices_eq neighbors_eq unfolding all_edges_def by auto
  have min_label_eq: "min_label os' t' = min_label os t'"
  proof (rule ext)
    fix v
    have lab_t': "label os' t' v = label os t' v"
      using label_eq t'_ne_t1 by auto
    have img_eq:
      "(\<lambda>t''. label os' t'' v) ` {t'' \<in> set (timestamps os'). t'' \<le> t'} =
       (\<lambda>t''. label os t'' v) ` {t'' \<in> set (timestamps os). t'' \<le> t'}"
      using filter_ts_eq label_on_filter by (auto intro!: image_cong)
    show "min_label os' t' v = min_label os t' v"
      unfolding min_label_def using lab_t' img_eq by simp
  qed
  show ?thesis
    using stable all_edges_eq min_label_eq by simp
qed

(* Preservation of labels_stable across the second branch of label_propagation_op_logic
   (input1: in-place label update at (t1, v) via label_prop_label_record_update).

   The update only rewrites label os t1 v to min (min_label os t1 v) l;
   timestamps, graph, and vertices are unchanged. Hence all_edges os' t' = all_edges os t'
   unconditionally.

   For min_label os' t' = min_label os t' to hold we still need t1 to be invisible at t'
   (otherwise the rewritten label at (t1, v) would enter the min). The condition
   \<not> t1 \<le> t' is exactly what guarantees this, so it is required here too.

   No invariant assumption (label_prop_upd_inv) is needed: the proof never inspects
   the structural part of os; only the field-equality assumptions matter. *)
lemma labels_stable_input1_preserved:
  fixes t1 t' :: "'t::order"
  assumes stable: "labels_stable (all_edges os t') (min_label os t')"
    and time_not_le: "\<not> t1 \<le> t'"
    and ts_eq: "timestamps os' = timestamps os"
    and graph_eq: "graph os' = graph os"
    and vertices_eq: "vertices os' = vertices os"
    and label_eq:
      "label os' = (label os)(t1 := (label os t1)(v := min (min_label os t1 v) l))"
  shows "labels_stable (all_edges os' t') (min_label os' t')"
proof -
  have t'_ne_t1: "t' \<noteq> t1"
    using time_not_le by auto
  have filter_ts_eq:
    "{t'' \<in> set (timestamps os'). t'' \<le> t'} = {t'' \<in> set (timestamps os). t'' \<le> t'}"
    using ts_eq by simp
  have label_on_filter:
    "\<And>x t''. t'' \<le> t' \<Longrightarrow> label os' t'' x = label os t'' x"
    using label_eq time_not_le by auto
  have all_vertices_eq: "all_vertices os' t' = all_vertices os t'"
    unfolding all_vertices_def using ts_eq vertices_eq by simp
  have neighbors_eq: "\<And>v. set (neighbors os' t' v) = set (neighbors os t' v)"
    unfolding set_neighbors using ts_eq graph_eq by simp
  have all_edges_eq: "all_edges os' t' = all_edges os t'"
    using all_vertices_eq neighbors_eq unfolding all_edges_def by auto
  have min_label_eq: "min_label os' t' = min_label os t'"
  proof (rule ext)
    fix x
    have lab_t': "label os' t' x = label os t' x"
      using label_eq t'_ne_t1 by auto
    have img_eq:
      "(\<lambda>t''. label os' t'' x) ` {t'' \<in> set (timestamps os'). t'' \<le> t'} =
       (\<lambda>t''. label os t'' x) ` {t'' \<in> set (timestamps os). t'' \<le> t'}"
      using filter_ts_eq label_on_filter by (auto intro!: image_cong)
    show "min_label os' t' x = min_label os t' x"
      unfolding min_label_def using lab_t' img_eq by simp
  qed
  show ?thesis
    using stable all_edges_eq min_label_eq by simp
qed

lemma labels_stable_input1_preserved_record_update_tl:
  fixes t' :: "'t::order"
  assumes stable: "labels_stable (all_edges os_label_prop t') (min_label os_label_prop t')"
    and time_not_le: "\<not> myfst t \<le> t'"
  shows "labels_stable (all_edges os_label_prop t')
          (min_label (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v
              (min (min_label os_label_prop (myfst t) v) l)) t')"
proof -
  let ?os' = "label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v
                (min (min_label os_label_prop (myfst t) v) l)"
  have stable':
    "labels_stable (all_edges ?os' t') (min_label ?os' t')"
  proof (rule labels_stable_input1_preserved[OF stable time_not_le])
    show "timestamps ?os' = timestamps os_label_prop" by simp
    show "graph ?os' = graph os_label_prop" by simp
    show "vertices ?os' = vertices os_label_prop" by simp
    show "label ?os' =
            (label os_label_prop)
              (myfst t :=
                 (label os_label_prop (myfst t))
                   (v := min (min_label os_label_prop (myfst t) v) l))"
      unfolding label_prop_label_record_update_def by simp
  qed
  have all_edges_eq: "all_edges ?os' t' = all_edges os_label_prop t'" by simp
  from stable' show ?thesis
    using all_edges_eq by simp
qed




section \<open>Inputs of label_propagation_op\<close>

lemma inputs_label_propagation_op:
  assumes \<open>sub_op (Read p f) (label_propagation_op os) n\<close>
  shows \<open>p = None \<or> p = Some 0 \<or> p = Some 1\<close>
proof -
  have \<open>p = None \<or> (\<exists>ip. p = Some ip \<and> ip |\<in>| (cUNIV :: 2 cset))\<close>
    using assms unfolding label_propagation_op_def by (rule inputs_builder_op)
  then show ?thesis
    by (metis num2_cases)
qed

lemma inputs_label_propagation_op_le:
  \<open>inputs (label_propagation_op os) \<subseteq> {None, Some 0, Some 1}\<close>
  by (auto dest!: inputs_sub_op_Read inputs_label_propagation_op)

lemma inputs_label_propagation_op_le_alt[dest!]:
  \<open>p \<in> inputs (label_propagation_op os) \<Longrightarrow> p = None \<or> p = Some 0 \<or> p = Some 1\<close>
  using set_mp[OF inputs_label_propagation_op_le] by blast

section \<open>Introduction rules for label_propagation_op steps\<close>

lemma step_label_propagation_op_Read_None[intro]:
  assumes \<open>io = Inp None (Inl (Inr f))\<close>
    and \<open>op = label_propagation_op (os\<lparr>front := f, initia := True\<rparr>)\<close>
  shows \<open>step io (label_propagation_op os) op\<close>
  using assms unfolding label_propagation_op_def by auto

lemma step_label_propagation_op_Read_Some[intro]:
  assumes \<open>io = Inp (Some p) (Inr (d, t))\<close>
    and \<open>op = label_propagation_op (consumes os p t d)\<close>
  shows \<open>step io (label_propagation_op os) op\<close>
  using assms unfolding label_propagation_op_def by (auto simp add: filter_True filter_False BULK_BENQ_right_empty BULK_BENQ_left_empty list_emb_Nil2 in_filter_zmset_in_zmset pos_filter_zmset_pos_zmset neg_filter_zmset_neg_zmset set_antichain1 set_antichain2 mset_set.infinite cin.rep_eq simp del: cin.rep_eq[symmetric] cong del: if_cong)

lemma step_label_propagation_op_Write_None[intro]:
  assumes \<open>io = Out None (Inl (Inl st))\<close>
    and \<open>(os', st) = obtain_progress os\<close>
    and \<open>op = label_propagation_op os'\<close>
  shows \<open>step io (label_propagation_op os) op\<close>
  using assms unfolding label_propagation_op_def by auto

lemma step_label_propagation_op_Write_None_alt[intro]:
  assumes \<open>io = Out None (Inl (Inl (snd (obtain_progress os))))\<close>
    and \<open>op = label_propagation_op (fst (obtain_progress os))\<close>
  shows \<open>step io (label_propagation_op os) op\<close>
  by (rule step_label_propagation_op_Write_None[OF assms(1) _ assms(2)]) (rule prod.collapse)

lemma step_label_propagation_op_Write_Some[intro]:
  assumes \<open>io = Out (Some p) (Inr x)\<close>
    and \<open>outpu os p = x # xs\<close>
    and \<open>op = label_propagation_op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>)\<close>
  shows \<open>step io (label_propagation_op os) op\<close>
  using assms unfolding label_propagation_op_def by (auto simp add: filter_True filter_False BULK_BENQ_right_empty BULK_BENQ_left_empty list_emb_Nil2 in_filter_zmset_in_zmset pos_filter_zmset_pos_zmset neg_filter_zmset_neg_zmset set_antichain1 set_antichain2 mset_set.infinite cin.rep_eq simp del: cin.rep_eq[symmetric] cong del: if_cong)

lemma steps_label_propagation_op_Write_Some[intro]:
  assumes \<open>outpu os p = xs @ ys\<close>
    and \<open>op = label_propagation_op (os\<lparr>outpu := (outpu os)(p := ys)\<rparr>)\<close>
    and \<open>zs = map (\<lambda>x. Out (Some p) (Inr x)) xs\<close>
  shows \<open>steps zs (label_propagation_op os) op\<close>
  using assms unfolding label_propagation_op_def by (auto simp add: filter_True filter_False BULK_BENQ_right_empty BULK_BENQ_left_empty list_emb_Nil2 in_filter_zmset_in_zmset pos_filter_zmset_pos_zmset neg_filter_zmset_neg_zmset set_antichain1 set_antichain2 mset_set.infinite cin.rep_eq simp del: cin.rep_eq[symmetric] cong del: if_cong)

lemma steps_label_propagation_op_Read_Some[intro]:
  assumes \<open>op = label_propagation_op (fold (\<lambda>(d, t) os. consumes os p t d) xs os)\<close>
  and \<open>ys = (map (\<lambda>x. Inp (Some p) (Inr x)) xs)\<close>
  shows \<open>steps ys (label_propagation_op os) op\<close>
  using assms unfolding label_propagation_op_def by (auto simp add: filter_True filter_False BULK_BENQ_right_empty BULK_BENQ_left_empty list_emb_Nil2 in_filter_zmset_in_zmset pos_filter_zmset_pos_zmset neg_filter_zmset_neg_zmset set_antichain1 set_antichain2 mset_set.infinite cin.rep_eq simp del: cin.rep_eq[symmetric] cong del: if_cong)

lemma step_label_propagation_op_Silent[intro]:
  assumes \<open>io = Tau\<close>
    and \<open>initia os\<close>
    and \<open>os' |\<in>| label_propagation_op_logic os\<close>
    and \<open>op = label_propagation_op os'\<close>
  shows \<open>step io (label_propagation_op os) op\<close>
  using assms unfolding label_propagation_op_def by auto

lemma step_label_propagation_op_n_Silents[intro]:
  assumes \<open>os' |\<in>| ((\<lambda>oss. cUnion (cimage label_propagation_op_logic
      (cfilter (\<lambda>os. initia os \<and> (\<exists>p. ocaps os p \<noteq> [])) oss))) ^^ n) {|os|}\<close>
    and \<open>op = label_propagation_op os'\<close>
  shows \<open>(step Tau ^^ n) (label_propagation_op os) op\<close>
  using assms unfolding label_propagation_op_def by auto

lemma steps_label_propagation_op_n_Silents[intro]:
  assumes \<open>os' |\<in>| ((\<lambda>oss. cUnion (cimage label_propagation_op_logic
      (cfilter (\<lambda>os. initia os \<and> (\<exists>p. ocaps os p \<noteq> [])) oss))) ^^ n) {|os|}\<close>
    and \<open>op = label_propagation_op os'\<close>
  shows \<open>(step Tau ^^ n) (label_propagation_op os) op\<close>
  using assms by (rule step_label_propagation_op_n_Silents)



lemma label_propagation_op_logic_input0I[intro]:
  assumes \<open>input os 0 = (d, t) # xs\<close>
    and \<open>de1 os d = (v1, v2)\<close>
    and \<open>t1 = myfst t\<close>
    and \<open>l1 = min_label os t1 v1\<close>
    and \<open>l2 = min_label os t1 v2\<close>
    and \<open>(v, l) = (if l1 > l2 then (v1, l2) else (v2, l1))\<close>
    and \<open>os' = input_tl os 0\<close>
    and \<open>os'' = label_prop_edge_record_update os' t1 v1 v2 v l\<close>
    and \<open>batch = label_prop_edge_batch os os'' t1 v l t\<close>
    and \<open>os_next = release_caps (drop_caps (produces (add_caps os'' (map snd batch)) batch) (map snd batch)) 1\<close>
  shows \<open>os_next |\<in>| label_propagation_op_logic os\<close>
  using assms unfolding label_propagation_op_logic_def by auto

lemma step_label_propagation_op_input0[intro]:
  assumes \<open>input os 0 = (d, t) # xs\<close>
    and \<open>de1 os d = (v1, v2)\<close>
    and \<open>t1 = myfst t\<close>
    and \<open>l1 = min_label os t1 v1\<close>
    and \<open>l2 = min_label os t1 v2\<close>
    and \<open>(v, l) = (if l1 > l2 then (v1, l2) else (v2, l1))\<close>
    and \<open>os' = input_tl os 0\<close>
    and \<open>os'' = label_prop_edge_record_update os' t1 v1 v2 v l\<close>
    and \<open>batch = label_prop_edge_batch os os'' t1 v l t\<close>
    and \<open>os_next = release_caps (drop_caps (produces (add_caps os'' (map snd batch)) batch) (map snd batch)) 1\<close>
    and \<open>initia os\<close>
    and \<open>op = label_propagation_op os_next\<close>
  shows \<open>step Tau (label_propagation_op os) op\<close>
  using assms by auto

lemma step_compower_label_propagation_op_input0[intro]:
  assumes \<open>input os 0 = msgs @ ys\<close>
    and \<open>n = length msgs\<close>
    and \<open>os_next |\<in>| ((\<lambda>oss. cUnion (cimage label_propagation_op_logic
      (cfilter (\<lambda>os. initia os \<and> (\<exists>p. ocaps os p \<noteq> [])) oss))) ^^ n) {|os|}\<close>
    and \<open>op = label_propagation_op os_next\<close>
  shows \<open>(step Tau ^^ n) (label_propagation_op os) op\<close>
  using assms by auto




section \<open>Batched Input Step Functions\<close>

text \<open>Executable step-state and batched forms of the input handlers.\<close>

definition label_prop_input0_step_state where
  \<open>label_prop_input0_step_state os d t = (
     let v1 = fst (de1 os d);
         v2 = snd (de1 os d);
         t1 = myfst t;
         l1 = min_label os t1 v1;
         l2 = min_label os t1 v2;
         v  = (if l1 > l2 then v1 else v2);
         l  = (if l1 > l2 then l2 else l1);
         os' = input_tl os 0;
         os'' = label_prop_edge_record_update os' t1 v1 v2 v l;
         batch = label_prop_edge_batch os os'' t1 v l t
     in release_caps (drop_caps (produces (add_caps os'' (map snd batch)) batch) (map snd batch)) 1)\<close>

definition label_prop_input0_step_batch ::
    "('d, nat, nat, nat) label_propagation_state \<Rightarrow> 'd \<Rightarrow> (nat, nat) myprod \<Rightarrow> ('d \<times> (2, (nat, nat) myprod) capability) buf" where
  \<open>label_prop_input0_step_batch os d t = (
     let v1 = fst (de1 os d);
         v2 = snd (de1 os d);
         t1 = myfst t;
         l1 = min_label os t1 v1;
         l2 = min_label os t1 v2;
         v  = (if l1 > l2 then v1 else v2);
         l  = (if l1 > l2 then l2 else l1);
         os' = input_tl os 0;
         os'' = label_prop_edge_record_update os' t1 v1 v2 v l
     in label_prop_edge_batch os os'' t1 v l t)\<close>

fun label_prop_input0_batched where
  \<open>label_prop_input0_batched os [] = (os, [])\<close>
| \<open>label_prop_input0_batched os ((d, t) # ms) =
     (case label_prop_input0_batched (label_prop_input0_step_state os d t) ms of
        (os_final, batches) \<Rightarrow> (os_final, label_prop_input0_step_batch os d t @ batches))\<close>




definition label_prop_input1_step_state where
  \<open>label_prop_input1_step_state os d t = (
     let v = fst (de1 os d);
         l = snd (de1 os d);
         t1 = myfst t;
         os' = input_tl os 1;
         l' = min (min_label os t1 v) l;
         os'' = label_prop_label_record_update os' t1 v l';
         batch = label_prop_label_batch os os'' t1 v l' t
     in release_caps (drop_caps (produces (add_caps os'' (map snd batch)) batch) (map snd batch)) 1)\<close>

definition label_prop_input1_step_batch ::
    "('d, nat, nat, nat) label_propagation_state \<Rightarrow> 'd \<Rightarrow> (nat, nat) myprod \<Rightarrow> ('d \<times> (2, (nat, nat) myprod) capability) buf" where
  \<open>label_prop_input1_step_batch os d t = (
     let v = fst (de1 os d);
         l = snd (de1 os d);
         t1 = myfst t;
         os' = input_tl os 1;
         l' = min (min_label os t1 v) l;
         os'' = label_prop_label_record_update os' t1 v l'
     in label_prop_label_batch os os'' t1 v l' t)\<close>

fun label_prop_input1_batched where
  \<open>label_prop_input1_batched os [] = (os, [])\<close>
| \<open>label_prop_input1_batched os ((d, t) # ms) =
     (case label_prop_input1_batched (label_prop_input1_step_state os d t) ms of
        (os_final, batches) \<Rightarrow> (os_final, label_prop_input1_step_batch os d t @ batches))\<close>


lemma label_propagation_op_logic_outputI[intro]:
  assumes \<open>below_times = filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t) \<and> myfst t \<in> set (timestamps os)) (ocaps os 0)\<close>
    and \<open>batch = label_prop_output_batch os below_times\<close>
    and \<open>batch \<noteq> []\<close>
    and \<open>os_next = drop_caps (produces os batch) (map (\<lambda>t. Cap t 0) below_times)\<close>
  shows \<open>os_next |\<in>| label_propagation_op_logic os\<close>
  using assms unfolding label_propagation_op_logic_def by auto

lemma step_label_propagation_op_output[intro]:
  assumes \<open>below_times = filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t) \<and> myfst t \<in> set (timestamps os)) (ocaps os 0)\<close>
    and \<open>batch = label_prop_output_batch os below_times\<close>
    and \<open>batch \<noteq> []\<close>
    and \<open>os_next = drop_caps (produces os batch) (map (\<lambda>t. Cap t 0) below_times)\<close>
    and \<open>initia os\<close>
    and \<open>op = label_propagation_op os_next\<close>
  shows \<open>step Tau (label_propagation_op os) op\<close>
  using assms by auto

lemma label_propagation_op_logic_release_caps1I[intro]:
  assumes \<open>ocaps os 1 = cap # caps\<close>
    and \<open>os_next = release_caps os 1\<close>
  shows \<open>os_next |\<in>| label_propagation_op_logic os\<close>
  using assms unfolding label_propagation_op_logic_def by auto

lemma step_label_propagation_op_release_caps1[intro]:
  assumes \<open>ocaps os 1 = cap # caps\<close>
    and \<open>os_next = release_caps os 1\<close>
    and \<open>initia os\<close>
    and \<open>op = label_propagation_op os_next\<close>
  shows \<open>step Tau (label_propagation_op os) op\<close>
  using assms by auto


lemma step_label_propagation_op_drop_caps[intro]:
  assumes \<open>input os 0 = []\<close>
    and \<open>input os 1 = []\<close>
    and \<open>os_next = drop_caps os (map (\<lambda> t. Cap t 1) (ocaps os 1))\<close>
    and \<open>initia os\<close>
    and \<open>op = label_propagation_op os_next\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>* (label_propagation_op os) op\<close>
proof (cases "ocaps os 1")
  case Nil
  then have "os_next = os"
    using assms(3) unfolding drop_caps_def by simp
  then show ?thesis
    using assms by simp
next
  case (Cons cap caps)
  have inputs_empty: "input os p = []" for p :: 2
    using assms(1,2) by (cases p rule: num2_cases) simp_all
  have empty_deps:
    "concat (map (\<lambda>(p', s). map (((+) s) \<circ> snd) (input os p')) xs) = []" for xs
    using inputs_empty by (induct xs) (auto split: prod.splits)
  have concat_empty: "concat (map (\<lambda>_. []) xs) = []" for xs
    by (induct xs) simp_all
  have release_eq: "release_caps os 1 = drop_caps os (map (\<lambda>t. Cap t 1) (ocaps os 1))"
    unfolding release_caps_def trace_simp Let_def
    by (simp add: empty_deps inputs_empty concat_empty case_prod_beta comp_def)
  have step1: "step Tau (label_propagation_op os) (label_propagation_op os_next)"
    using assms(3,4) Cons release_eq
    by (intro step_label_propagation_op_release_caps1[OF Cons]) simp_all
  then show ?thesis
    using assms(5) by auto
qed


lemma vertices_CONSUMES[simp]:
  \<open>vertices (CONSUMES p xs os) = vertices os\<close>
  unfolding fold_consumes by simp

lemma label_CONSUMES[simp]:
  \<open>label (CONSUMES p xs os) = label os\<close>
  unfolding fold_consumes by simp

lemma all_vertices_CONSUMES[simp]:
  \<open>all_vertices (CONSUMES p xs os) = all_vertices os\<close>
  unfolding all_vertices_def by simp

lemma all_edges_CONSUMES[simp]:
  \<open>all_edges (CONSUMES p xs os) = all_edges os\<close>
  unfolding all_edges_def all_vertices_def neighbors_def by simp

lemma min_label_CONSUMES[simp]:
  \<open>min_label (CONSUMES p xs os) = min_label os\<close>
  unfolding min_label_def by simp

lemma timestamps_CONSUMES[simp]:
  \<open>timestamps (CONSUMES p xs os) = timestamps os\<close>
  unfolding fold_consumes by simp

lemma graph_CONSUMES[simp]:
  \<open>label_propagation_state.graph (CONSUMES p xs os) = label_propagation_state.graph os\<close>
  unfolding fold_consumes by simp

lemma label_prop_upd_inv_CONSUMES_port1I:
  assumes inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set xs)\<close>
  shows \<open>label_prop_upd_inv (CONSUMES (1 :: 2) xs os)\<close>
proof -
  let ?os' = \<open>CONSUMES (1 :: 2) xs os\<close>
  have input_eq: \<open>set (input ?os' 1) = set (input os 1) \<union> set xs\<close>
    by (simp add: input_CONSUMES)
  show ?thesis
    using inv wf_upd
    unfolding label_prop_upd_inv_def wf_label_prop_updates_def
    apply (auto simp add: input_eq)
    done
qed

lemma min_label_mono_time:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>t \<in> set (timestamps os)\<close>
    and \<open>t \<le> q\<close>
  shows \<open>min_label os q v \<le> min_label os t v\<close>
  using assms
  unfolding min_label_def
  by (intro Min.boundedI) auto


lemma finite_all_vertices:
  shows \<open>finite (all_vertices os t)\<close>
  unfolding all_vertices_def by simp

lemma finite_edge_vertices_all_edges:
  shows \<open>finite (edge_vertices (all_edges os t))\<close>
proof -
  have \<open>edge_vertices (all_edges os t) \<subseteq> all_vertices os t\<close>
    by (rule edge_vertices_all_edges_subset_all_vertices)
  then show ?thesis
    using finite_all_vertices[of os t] by (rule finite_subset)
qed

lemma wf_label_prop_updates_consumes[simp]:
  \<open>wf_label_prop_updates (consumes os p t d) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  by (simp add: wf_label_prop_updates_def consumes_def all_vertices_def all_edges_def neighbors_def)

lemma wf_label_prop_updates_CONSUMES[simp]:
  \<open>wf_label_prop_updates (CONSUMES p ys os) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  by (induct ys arbitrary: os) clarsimp+

lemma wf_label_prop_updates_intsum_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>intsum := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_consu_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>consu := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_inter_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>inter := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_produ_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>produ := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_input_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>input := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_outpu_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>outpu := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_front_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>front := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_ocaps_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>ocaps := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_initia_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>initia := b\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_en1_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>en1 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_is_en1_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>is_en1 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_en2_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>en2 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_de2_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>de2 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_is_en2_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>is_en2 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_label_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>label := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_cong:
  \<open>de1 os = de1 os' \<Longrightarrow> timestamps os = timestamps os' \<Longrightarrow> graph os = graph os' \<Longrightarrow>
  vertices os = vertices os' \<Longrightarrow> S = S' \<Longrightarrow>
  wf_label_prop_updates os S \<longleftrightarrow> wf_label_prop_updates os' S'\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_subset:
  \<open>wf_label_prop_updates os S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> wf_label_prop_updates os S'\<close>
  unfolding wf_label_prop_updates_def by fast

lemma wf_label_prop_updates_Un:
  \<open>S'' = S \<union> S' \<Longrightarrow> wf_label_prop_updates os S'' \<longleftrightarrow> wf_label_prop_updates os S \<and> wf_label_prop_updates os S'\<close>
  unfolding wf_label_prop_updates_def by force

lemma wf_label_prop_updates_os_mono:
  assumes \<open>wf_label_prop_updates os S\<close> \<open>de1 os = de1 os'\<close> \<open>set (timestamps os) \<subseteq> set (timestamps os')\<close>
    \<open>\<forall>t. set (vertices os t) \<subseteq> set (vertices os' t) \<and> (\<forall>v. set (graph os t v) \<subseteq> set (graph os' t v))\<close>
    \<open>S = S'\<close>
  shows \<open>wf_label_prop_updates os' S'\<close>
proof -
  { fix d t
    assume d_t: \<open>(d, t) \<in> S\<close>
    let ?t0 = \<open>myfst t\<close>
    have t0: \<open>?t0 \<in> set (timestamps os')\<close> (is ?A)
      using assms(1,3) d_t unfolding wf_label_prop_updates_def by fast
    have all_vertices_subset: \<open>\<forall>t'. all_vertices os t' \<subseteq> all_vertices os' t'\<close>
      using assms(3,4) d_t unfolding wf_label_prop_updates_def all_vertices_def by blast
    hence fst_de1: \<open>fst (de1 os d) \<in> all_vertices os' ?t0\<close> (is ?B)
      using assms(1) d_t unfolding wf_label_prop_updates_def by fast
    have \<open>\<forall>t' \<ge> ?t0. \<forall>v. set (neighbors os t' v) \<subseteq> set (neighbors os' t' v)\<close>
      unfolding neighbors_def using assms(3,4) by force
    hence \<open>\<forall>t' \<ge> ?t0. all_edges os t' \<subseteq> all_edges os' t'\<close>
      unfolding all_edges_def using all_vertices_subset by fast
    hence \<open>\<forall>t' \<ge> ?t0. snd (de1 os d) \<in> cc_of (all_edges os' t') (fst (de1 os d))\<close> (is ?C)
      using assms(1) d_t cc_of_mono prod.simps(2) unfolding wf_label_prop_updates_def
      by (metis (mono_tags, lifting))
    hence \<open>?A \<and> ?B \<and> ?C\<close> using t0 fst_de1 by blast
  }
  thus ?thesis unfolding wf_label_prop_updates_def assms(5) using assms(2) by force
qed

lemma label_prop_edge_batch_in_timestamps:
  \<open>(d, cap) \<in> set (label_prop_edge_batch old_os updated_os event_t vertex new_label event_time)
  \<Longrightarrow> myfst (capability.time cap) \<in> set (timestamps updated_os)\<close>
  unfolding label_prop_edge_batch_def label_prop_neighbor_batch_def by force

lemma label_prop_label_batch_in_timestamps:
  \<open>(d, cap) \<in> set (label_prop_label_batch old_os updated_os event_t vertex new_label event_time)
  \<Longrightarrow> myfst (capability.time cap) \<in> set (timestamps old_os)\<close>
  unfolding label_prop_label_batch_def label_prop_neighbor_batch_def by force

lemma neighbors_reachable:
  \<open>label_prop_upd_inv os \<Longrightarrow> w \<in> set (neighbors os t v) \<Longrightarrow> reachable (all_edges os t) v w\<close>
  unfolding all_edges_def reachable_def using label_prop_upd_inv_neighborsD by blast

lemma min_label_le_label: "min_label os t v \<le> label os t v"
  unfolding min_label_def by (intro Min_le) auto
end
