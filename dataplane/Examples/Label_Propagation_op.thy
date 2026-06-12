theory Label_Propagation_op

imports
  Dataplane.Timely_Builder_Op
  Dataplane.MyProduct_Instances
  Wcc
begin

definition union_with where
  \<open>union_with f g h x = f (g x) (h x)\<close>

fun unions_with where
  \<open>unions_with f [] = undefined\<close>
| \<open>unions_with f (g # gs) = foldl (union_with f) g gs\<close>

primrec list_span where
  \<open>list_span _ [] = ([], [])\<close>
| \<open>list_span P (x # xs) =
    (if P x then let (ys, zs) = list_span P xs in (x # ys, zs) else ([], x # xs))\<close>

lemma list_span_length_le:
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length ys \<le> length xs\<close>
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length zs \<le> length xs\<close>
  by (induction xs arbitrary: ys zs) (auto split: if_splits prod.splits)

function group_by where
  \<open>group_by _ [] = []\<close>
| \<open>group_by f (x # xs) = (let (ys, zs) = list_span (f x) xs in (x # ys) # group_by f zs)\<close>
  by pat_completeness auto
termination by (lexicographic_order simp add: list_span_length_le)

definition insort_union where
  \<open>insort_union = fold insort_insert\<close>

lemma set_insort_union[simp]:
  \<open>set (insort_union xs ys) = set xs \<union> set ys\<close>
  by (induction xs arbitrary: ys) (simp_all add: insort_union_def set_insort_insert)

lemma distinct_insort_union[simp]:
  \<open>distinct (insort_union xs ys) \<longleftrightarrow> distinct ys\<close>
  by (induction xs arbitrary: ys)
    (simp_all add: insort_union_def distinct_insort insort_insert_key_def)

lemma sorted_insort_union:
  \<open>sorted ys \<Longrightarrow> sorted (insort_union xs ys)\<close>
  by (induction xs) (simp_all add: insort_union_def fold_invariant sorted_insort_insert)

record ('d, 'v :: linorder, 't1, 't2) label_propagation_state =
  \<open>(2, 'd, 'v \<times> 'v, 'v set set, ('t1, 't2) myprod) operator_state_ty2\<close> +
  timestamps :: \<open>'t1 list\<close> graph :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v list\<close> vertices :: \<open>'t1 \<Rightarrow> 'v list\<close>
  label :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v\<close>

definition neighbors where
  \<open>neighbors os t v = (let ts = filter ((\<ge>) t) (timestamps os) in
  rmdups {} (concat ((map (\<lambda> t. graph os t v) ts))))\<close>

definition all_vertices where
  \<open>all_vertices os t = ((\<Union>t'\<in>{t' \<in> set (timestamps os). t' \<le> t}. set (vertices os t')))\<close>

definition all_edges where
  \<open>all_edges os t = {(v, w) \<in> (all_vertices os t) \<times> (all_vertices os t). w \<in> set (neighbors os t v)}\<close>

definition min_label where
  \<open>min_label os t v =
    Min (insert (label os t v)
      ((\<lambda>t'. label os t' v) ` {t' \<in> set (timestamps os). t' \<le> t}))\<close>


lemma set_foldl_union_with:
  "set (foldl (union_with List.union) g gs y) = (\<Union>f\<in>set (g # gs). set (f y))"
proof (induction gs arbitrary: g)
  case Nil
  then show ?case by simp
next
  case (Cons h hs)
  then show ?case
    by (auto simp: union_with_def)
qed

lemma set_unions_with_List_union:
  assumes "fs \<noteq> []"
  shows "set (unions_with List.union fs y) = (\<Union>f\<in>set fs. set (f y))"
proof (cases fs)
  case Nil
  then show ?thesis
    using assms by simp
next
  case (Cons g gs)
  then show ?thesis
    using set_foldl_union_with[of g gs y] by simp
qed

lemma set_neighbors:
  "set (neighbors os t v) = (\<Union>t'\<in>{t' \<in> set (timestamps os). t' \<le> t}. set (graph os t' v))"
  unfolding neighbors_def
  by simp



(* lemma all_edges_set:
  "all_edges os t =
    (if \<exists>t'\<in>set (timestamps os). t' \<le> t
     then {(v, w) \<in> all_vertices os t \<times> all_vertices os t.
       \<exists>t'\<in>set (timestamps os). t' \<le> t \<and> w \<in> set (graph os t' v)}
     else {(v, w) \<in> all_vertices os t \<times> all_vertices os t.
       w \<in> set (graph os t v)})"
  by (auto simp: all_edges_def set_neighbors)
 *)
(* 
lemma all_edges_set':
  "all_edges os t =
    (if \<exists>t'\<in>set (timestamps os). t' \<le> t
     then {(v, w). (\<exists>t'\<in>set (timestamps os). t' \<le> t \<and> v \<in> set (vertices os t')) \<and>
       (\<exists>t'\<in>set (timestamps os). t' \<le> t \<and> w \<in> set (vertices os t')) \<and>
       (\<exists>t'\<in>set (timestamps os). t' \<le> t \<and> w \<in> set (graph os t' v))}
     else {(v, w). v \<in> set (vertices os t) \<and> w \<in> set (vertices os t) \<and>
       w \<in> set (graph os t v)})"
  by (auto simp: all_edges_set all_vertices_set)
 *)


definition all_vertices_inv where
  "all_vertices_inv os t \<longleftrightarrow> (\<forall>v w. w \<in> set (neighbors os t v) \<longrightarrow>
    v \<in> all_vertices os t \<and> w \<in> all_vertices os t)"

definition all_vertices_incident_inv where
  "all_vertices_incident_inv os t \<longleftrightarrow>
    (\<forall>v \<in> all_vertices os t.
      (\<exists>w \<in> all_vertices os t. w \<in> set (neighbors os t v)) \<or>
      (\<exists>w \<in> all_vertices os t. v \<in> set (neighbors os t w)))"



lemma edge_vertices_all_edges:
  assumes "all_vertices_incident_inv os t"
  shows "edge_vertices (all_edges os t) = all_vertices os t"
  using assms
  unfolding all_vertices_incident_inv_def edge_vertices_def all_edges_def Field_def
  by auto

lemma labels_inv_insert_updateI:
  assumes inv: "labels_inv A l"
    and v1_label: "l' \<in> cc_of (insert (v1, v2) A) v1"
    and v2_label: "v2 \<notin> edge_vertices A \<Longrightarrow> l v2 \<in> cc_of (insert (v1, v2) A) v2"
  shows "labels_inv (insert (v1, v2) A) (l(v1 := l'))"
proof -
  have cc_of_mono: "\<And>v x. x \<in> cc_of A v \<Longrightarrow> x \<in> cc_of (insert (v1, v2) A) v"
  proof -
    fix v x
    assume x: "x \<in> cc_of A v"
    have rel_mono: "A \<union> A\<inverse> \<subseteq> insert (v1, v2) A \<union> (insert (v1, v2) A)\<inverse>"
      by auto
    have "reachable (insert (v1, v2) A) v x"
      using x rtrancl_mono[OF rel_mono] unfolding cc_of_def reachable_def by blast
    then show "x \<in> cc_of (insert (v1, v2) A) v"
      using x unfolding cc_of_def edge_vertices_def Field_def by auto
  qed
  show ?thesis
    unfolding labels_inv_def
  proof safe
    fix v
    assume v_edge: "v \<in> edge_vertices (insert (v1, v2) A)"
    show "(l(v1 := l')) v \<in> cc_of (insert (v1, v2) A) v"
    proof (cases "v = v1")
      case True
      then show ?thesis
        using v1_label by simp
    next
      case v_not_v1: False
      show ?thesis
      proof (cases "v = v2")
        case True
        then show ?thesis
        using inv v2_label v_not_v1 by (cases "v2 \<in> edge_vertices A")
          (auto simp: labels_inv_def intro: cc_of_mono)

      next
        case False
        then have v_old: "v \<in> edge_vertices A"
          using v_edge v_not_v1 by simp
        have "l v \<in> cc_of A v"
          using inv v_old by (auto simp: labels_inv_def)
        then show ?thesis
          using v_not_v1 by (auto intro: cc_of_mono)
      qed
    qed
  qed
qed

lemma labels_inv_insert_update_neighborI:
  assumes inv: "labels_inv A l"
    and v2_label: "v2 \<in> edge_vertices A \<or> l v2 = v2"
  shows "labels_inv (insert (v1, v2) A) (l(v1 := l v2))"
proof (rule labels_inv_insert_updateI)
  show "labels_inv A l"
    by (rule inv)
  show "l v2 \<in> cc_of (insert (v1, v2) A) v1"
    using inv v2_label
    by (auto simp: labels_inv_def)
  show "v2 \<notin> edge_vertices A \<Longrightarrow> l v2 \<in> cc_of (insert (v1, v2) A) v2"
    using v2_label by (auto simp: cc_of_def reachable_def edge_vertices_def Field_def)
qed

lemma labels_inv_insert_symmetric_update_neighborI:
  assumes inv: "labels_inv A l"
    and v2_label: "v2 \<in> edge_vertices A \<or> l v2 = v2"
  shows "labels_inv (insert (l1, v2) (insert (v2, l1) A)) (l(l1 := l v2))"
proof -
  let ?B = "insert (l1, v2) (insert (v2, l1) A)"
  have cc_of_mono: "\<And>v x. x \<in> cc_of A v \<Longrightarrow> x \<in> cc_of ?B v"
  proof -
    fix v x
    assume x: "x \<in> cc_of A v"
    have rel_mono: "A \<union> A\<inverse> \<subseteq> ?B \<union> ?B\<inverse>"
      by auto
    have "reachable ?B v x"
      using x rtrancl_mono[OF rel_mono] unfolding cc_of_def reachable_def by blast
    then show "x \<in> cc_of ?B v"
      using x unfolding cc_of_def edge_vertices_def Field_def by auto
  qed
  have lv2_in_v2: "l v2 \<in> cc_of ?B v2"
  proof (cases "v2 \<in> edge_vertices A")
    case True
    then have "l v2 \<in> cc_of A v2"
      using inv unfolding labels_inv_def by simp
    then show ?thesis
      by (rule cc_of_mono)
  next
    case False
    then have "l v2 = v2"
      using v2_label by simp
    then show ?thesis
      unfolding cc_of_def edge_vertices_def reachable_def Field_def by auto
  qed

  have lv2_in_l1: "l v2 \<in> cc_of ?B l1"
  proof -
    have "reachable ?B l1 v2"
      by simp
    moreover have "reachable ?B v2 (l v2)"
      using lv2_in_v2 unfolding cc_of_def by simp
    ultimately have "reachable ?B l1 (l v2)"
      by (rule reachable_trans)
    then show ?thesis
      using lv2_in_v2 unfolding cc_of_def by simp
  qed
  show ?thesis
    unfolding labels_inv_def
  proof safe
    fix v
    assume v_edge: "v \<in> edge_vertices ?B"
    show "(l(l1 := l v2)) v \<in> cc_of ?B v"
    proof (cases "v = l1")
      case True
      then show ?thesis
        using lv2_in_l1 by simp
    next
      case v_not_l1: False
      show ?thesis
      proof (cases "v = v2")
        case True
        then show ?thesis
          using v_not_l1 lv2_in_v2 by simp
      next
        case False
        then have v_old: "v \<in> edge_vertices A"
          using v_edge v_not_l1 by simp
        have "l v \<in> cc_of A v"
          using inv v_old unfolding labels_inv_def by simp
        then show ?thesis
          using v_not_l1 by (auto intro: cc_of_mono)
      qed
    qed
  qed
qed

lemma labels_inv_insert_symmetric_min_label_updateI:
  assumes inv: "labels_inv (all_edges os t) (min_label os t)"
    and v2_label: "v2 \<in> edge_vertices (all_edges os t) \<or> min_label os t v2 = v2"
    and update_eq: "min_label os' t = (min_label os t)(l1 := min_label os t v2)"
  shows "labels_inv (insert (l1, v2) (insert (v2, l1) (all_edges os t))) (min_label os' t)"
  using labels_inv_insert_symmetric_update_neighborI[OF inv v2_label] update_eq by simp

lemma min_label_Cons_timestamp_label_update_eq:
  fixes t :: "'t::order"
  assumes new_le: "l \<le> min_label (os\<lparr>timestamps := T\<rparr>) t v"
  shows "min_label (os\<lparr>timestamps := t # T, label := (label os)(t := (label os t)(v := l))\<rparr>) t =
    (min_label (os\<lparr>timestamps := T\<rparr>) t)(v := l)"
proof (rule ext)
  fix v'
  let ?old = "os\<lparr>timestamps := T\<rparr>"
  let ?new = "os\<lparr>timestamps := t # T, label := (label os)(t := (label os t)(v := l))\<rparr>"
  show "min_label ?new t v' = ((min_label ?old t)(v := l)) v'"
  proof (cases "v' = v")
    case True
    let ?old_set = "insert (label os t v) ((\<lambda>t'. label os t' v) ` {t' \<in> set T. t' \<le> t})"
    let ?new_set = "insert l ((\<lambda>t'. label ?new t' v) ` {t' \<in> set (t # T). t' \<le> t})"
    have le_Min: "l \<le> Min ?old_set"
      using new_le unfolding min_label_def by simp
    have le_old: "\<And>x. x \<in> ?old_set \<Longrightarrow> l \<le> x"
      using le_Min by (auto intro: order_trans[OF le_Min Min_le])
    have le_new: "\<And>x. x \<in> ?new_set \<Longrightarrow> l \<le> x"
      using le_old by auto
    show ?thesis
      using True le_new unfolding min_label_def
      by (auto intro!: Min_insert2)
  next
    case False
    have set_eq:
      "insert (label ?new t v') ((\<lambda>t'. label ?new t' v') ` {t' \<in> set (t # T). t' \<le> t}) =
       insert (label os t v') ((\<lambda>t'. label os t' v') ` {t' \<in> set T. t' \<le> t})"
      using False by auto
    show ?thesis
      using False set_eq unfolding min_label_def by simp
  qed
qed

lemma min_label_Cons_timestamp_label_update_eq_no_t_in:
  fixes t :: "'t::order"
  assumes new_le: "l \<le> min_label (os\<lparr>timestamps := T\<rparr>) t v"
  shows "min_label (os\<lparr>timestamps := t # T, label := (label os)(t := (label os t)(v := l))\<rparr>) t =
    (min_label (os\<lparr>timestamps := T\<rparr>) t)(v := l)"
  using new_le by (rule min_label_Cons_timestamp_label_update_eq)

lemma min_label_le_current_labelI:
  fixes t :: "'t::order"
  shows "min_label os t v \<le> label os t v"
  unfolding min_label_def by (auto intro: Min_le)

lemma min_label_eq_self_if_not_all_vertices:
  fixes t :: "'t::order"
  assumes absent_label_self:
    "\<And>t' v. t' \<in> set (timestamps os) \<Longrightarrow> t' \<le> t \<Longrightarrow>
      v \<notin> set (vertices os t') \<Longrightarrow> label os t' v = v"
    and current_default: "t \<notin> set (timestamps os) \<Longrightarrow> label os t v = v"
    and not_vertex: "v \<notin> all_vertices os t"
  shows "min_label os t v = v"
proof -
  have current_self: "label os t v = v"
  proof (cases "t \<in> set (timestamps os)")
    case True
    then show ?thesis
      using absent_label_self[of t v] not_vertex unfolding all_vertices_def by auto
  next
    case False
    then show ?thesis
      by (rule current_default)
  qed
  have stored_self:
    "\<And>t'. t' \<in> set (timestamps os) \<Longrightarrow> t' \<le> t \<Longrightarrow> label os t' v = v"
    using absent_label_self not_vertex unfolding all_vertices_def by auto
  have set_eq:
    "insert (label os t v) ((\<lambda>t'. label os t' v) ` {t' \<in> set (timestamps os). t' \<le> t}) = {v}"
    using current_self stored_self by force

  show ?thesis
    unfolding min_label_def
    by (simp only: set_eq Min_singleton)

qed

lemma min_label_eq_self_if_not_edge_vertices:
  fixes t :: "'t::order"
  assumes incident: "all_vertices_incident_inv os t"
    and absent_label_self:
      "\<And>t' v. t' \<in> set (timestamps os) \<Longrightarrow> t' \<le> t \<Longrightarrow>
        v \<notin> set (vertices os t') \<Longrightarrow> label os t' v = v"
    and current_default: "t \<notin> set (timestamps os) \<Longrightarrow> label os t v = v"
    and not_edge: "v \<notin> edge_vertices (all_edges os t)"
  shows "min_label os t v = v"
proof (rule min_label_eq_self_if_not_all_vertices)
  show "\<And>t' v. t' \<in> set (timestamps os) \<Longrightarrow> t' \<le> t \<Longrightarrow>
    v \<notin> set (vertices os t') \<Longrightarrow> label os t' v = v"
    by (rule absent_label_self)
  show "t \<notin> set (timestamps os) \<Longrightarrow> label os t v = v"
    by (rule current_default)
  show "v \<notin> all_vertices os t"
    using not_edge edge_vertices_all_edges[OF incident] by simp
qed

lemma edge_vertices_all_edges_subset_all_vertices:
  "edge_vertices (all_edges os t) \<subseteq> all_vertices os t"
  unfolding edge_vertices_def all_edges_def Field_def by auto

lemma labels_inv_min_label_any_queryI:
  fixes q :: "'t::order"
  assumes stored_valid:
    "\<And>t' v. t' \<in> set (timestamps os) \<Longrightarrow> t' \<le> q \<Longrightarrow>
      v \<in> edge_vertices (all_edges os q) \<Longrightarrow>
      label os t' v \<in> cc_of (all_edges os q) v"
    and current_valid:
      "\<And>v. v \<in> edge_vertices (all_edges os q) \<Longrightarrow>
        label os q v \<in> cc_of (all_edges os q) v"
  shows "labels_inv (all_edges os q) (min_label os q)"
  unfolding labels_inv_def
proof safe
  fix v
  assume v_edge: "v \<in> edge_vertices (all_edges os q)"
  let ?S = "insert (label os q v) ((\<lambda>t'. label os t' v) ` {t' \<in> set (timestamps os). t' \<le> q})"
  have "Min ?S \<in> ?S"
    by (intro Min_in) auto
  then show "min_label os q v \<in> cc_of (all_edges os q) v"
    using stored_valid[OF _ _ v_edge] current_valid[OF v_edge]
    unfolding min_label_def by auto
qed

definition labels_cc_inv where
  "labels_cc_inv os t =
    (\<forall>v\<in>all_vertices os t.
        min_label os t v \<in> cc_of (all_edges os t) v)"

lemma labels_cc_inv_imp_labels_inv:
  assumes  current_valid: "labels_cc_inv os t"
  shows "labels_inv (all_edges os t) (min_label os t)"
  unfolding labels_inv_def
proof safe
  fix v
  assume "v \<in> edge_vertices (all_edges os t)"
  then have "v \<in> all_vertices os t"
    using edge_vertices_all_edges_subset_all_vertices by auto
  then show "min_label os t v \<in> cc_of (all_edges os t) v"
    using current_valid unfolding labels_cc_inv_def by auto
qed

lemma labels_cc_inv_iff_labels_inv:
  assumes "all_vertices_incident_inv os t"
  shows "labels_cc_inv os t \<longleftrightarrow> labels_inv (all_edges os t) (min_label os t)"
proof
  assume "labels_cc_inv os t"
  then show "labels_inv (all_edges os t) (min_label os t)"
    by (rule labels_cc_inv_imp_labels_inv)
next
  assume inv: "labels_inv (all_edges os t) (min_label os t)"
  show "labels_cc_inv os t"
    unfolding labels_cc_inv_def
  proof safe
    fix v
    assume "v \<in> all_vertices os t"
    then have "v \<in> edge_vertices (all_edges os t)"
      using edge_vertices_all_edges[OF assms, symmetric] by simp
    then show "min_label os t v \<in> cc_of (all_edges os t) v"
      using inv unfolding labels_inv_def by simp
  qed
qed


lemma all_vertices_insert:
  assumes "vertices os' = (vertices os)(t := [v1, v2] @ vertices os t)"
  and "timestamps os' = (t :: _ :: order) # timestamps os"
  and "\<forall> t. t \<notin> set (timestamps os) \<longleftrightarrow> vertices os t = []"
shows "all_vertices os' t = insert v1 (insert v2 (all_vertices os t))"
  using assms apply -
  unfolding all_vertices_def
  by (force split: if_splits)



lemma
  assumes "all_vertices_incident_inv os t"
    and "label os' = (label os)(t := (label os t)(l1 := min_label os t v2))"
    and "graph os' = (graph os)((t :: _ :: order) := (map_entry l1 ((#) v2) ((graph os) t))(v2 := l1 # (graph os)( t) v2))"
    and "vertices os' = (vertices os)(t := [v1, v2] @ vertices os t)"
    and "\<forall> t. t \<notin> set (timestamps os) \<longleftrightarrow> vertices os t = []"
  and "timestamps os' = t # timestamps os"
  shows "all_vertices_incident_inv os' t"
  unfolding all_vertices_incident_inv_def
  apply (subst all_vertices_insert)
  using assms(4) apply assumption 
  using assms(6) apply assumption 
  using assms(5) apply assumption 

end

lemma labels_cc_inv_updateI:
  assumes  "Ball (set (timestamps os)) (labels_cc_inv os)"
    and "label os' = (label os)(t := (label os t)(l1 := min_label os t v2))"
    and "graph os' = (graph os)(t := (map_entry l1 ((#) v2) ((graph os) t))(v2 := l1 # (graph os)( t) v2))"
    and "vertices os' = (vertices os)(t := [v1, v2] @ vertices os t)"
    and "all_vertices_incident_inv os t"
  shows "labels_cc_inv os' t"
  using assms(2-) apply -
  unfolding labels_cc_inv_def
  apply clarsimp
  subgoal for v
    unfolding all_vertices_def
    apply (clarsimp split: if_splits)
    subgoal for t'
    apply (elim conjE disjE)
    subgoal
      apply (clarsimp split: if_splits)
      apply hypsubst_thin
    apply (elim conjE disjE)
      subgoal
        apply hypsubst_thin
        apply (rule cc_ofI)
         apply (subst edge_vertices_all_edges)


        find_theorems edge_vertices all_edges

    oops





definition timestamps_data_sync where
  "timestamps_data_sync os \<longleftrightarrow>
    (\<forall>t. t \<notin> set (timestamps os) \<longrightarrow> vertices os t = [] \<and> (\<forall>v. graph os t v = []))"


lemma all_edges_eq:
  fixes t :: "'t::order"
  assumes inv: "all_vertices_inv
    \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
     input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
     initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
     en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
     timestamps = t # T, graph = G, vertices = V, label = label_state\<rparr> t"
    and V'_def: "V' = map_entry t ((Cons v1) o (Cons v2)) V"
    and sync: "timestamps_data_sync
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
    using inv by (auto simp: all_vertices_inv_def)
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
  have base_eq_tail: "all_edges ?base t = all_edges ?base_tail t"
    using sync by (auto simp: all_edges_def all_vertices_def neighbors_def timestamps_data_sync_def)

  show ?thesis
    using mod_eq_base base_eq_tail by simp
qed



lemma all_edges_eq_le:
  fixes t :: "'t::order"
  assumes inv: "all_vertices_inv
    \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
     input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
     initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
     en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
     timestamps = t # T, graph = G, vertices = V, label = label_state\<rparr> t'"
    and V'_def: "V' = map_entry t ((Cons v1) o (Cons v2)) V"
    and sync: "timestamps_data_sync
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
    using inv by (auto simp: all_vertices_inv_def)
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
    using sync by (auto simp: all_edges_def all_vertices_def neighbors_def timestamps_data_sync_def)

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


lemma all_edges_eq_if:
  fixes t :: "'t::order"
  assumes inv: "all_vertices_inv
    \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
     input = input_state, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
     initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
     en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
     timestamps = t # T, graph = G, vertices = V, label = label_state\<rparr> t'"
    and V'_def: "V' = map_entry t ((Cons v1) o (Cons v2)) V"
    and sync: "timestamps_data_sync
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
    vertices = V', label = label_state\<rparr> t' =
   (if t \<le> t'
    then insert (v1, v2) (insert (v2, v1) (all_edges
   \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = T, graph = G, vertices = V, label = label_sync\<rparr> t'))
    else all_edges
   \<lparr>intsum = intsum_state, consu = consu_state, inter = inter_state, produ = produ_state,
    input = input_sync, outpu = outpu_state, front = front_state, ocaps = ocaps_state,
    initia = initia_state, en1 = en1_state, de1 = de1_state, is_en1 = is_en1_state,
    en2 = en2_state, de2 = de2_state, is_en2 = is_en2_state,
    timestamps = T, graph = G, vertices = V, label = label_sync\<rparr> t')"
  by (simp add: all_edges_eq_le all_edges_eq_not_le assms(1,2,3))


definition exit_scope where
  "exit_scope f A = frontier ((zmset_of o mset_set) (f ` set_antichain A))"

lemma frontier_less_equal_exit_scope:
  "\<not> frontier_less_equal (exit_scope myfst A) (myfst t) \<Longrightarrow>
   \<not> frontier_less_equal A t"
proof
  assume not_projected: "\<not> frontier_less_equal (exit_scope myfst A) (myfst t)"
  assume "frontier_less_equal A t"
  then obtain t' where t'_in: "t' \<in>\<^sub>A A" and t'_le: "t' \<le> t"
    unfolding frontier_less_equal_iff2 by blast
  have zcount_pos: "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) (myfst t')"
    using t'_in by (simp add: member_antichain.rep_eq)
  have "frontier_less_equal (exit_scope myfst A) (myfst t')"
    unfolding exit_scope_def o_def using zcount_pos by (rule frontier_less_equal_zcount_pos)
  then have "frontier_less_equal (exit_scope myfst A) (myfst t)"
    using myfst_mono[OF t'_le] by (rule frontier_less_equal_trans)
  then show False
    using not_projected by contradiction
qed


lemma frontier_less_equal_antichain_plusI1:
  assumes "frontier_less_equal A t"
  shows "frontier_less_equal (A + B) t"
proof -
  obtain a where a_in: "a \<in>\<^sub>A A" and a_le: "a \<le> t"
    using assms unfolding frontier_less_equal_iff2 by blast
  have fin: "finite (set_antichain A \<union> set_antichain B)"
    by simp
  have "a \<in> set_antichain A \<union> set_antichain B"
    using a_in unfolding member_antichain.rep_eq by simp
  then obtain a' where a'_in: "a' \<in> minimal_antichain (set_antichain A \<union> set_antichain B)" and a'_le: "a' \<le> a"
    using minimal_antichain_member[OF fin] by blast
  then have "a' \<in>\<^sub>A A + B"
    unfolding member_antichain.rep_eq plus_antichain.rep_eq by simp
  moreover have "a' \<le> t"
    using a'_le a_le by order
  ultimately show ?thesis
    unfolding frontier_less_equal_iff2 by blast
qed

lemma frontier_less_equal_antichain_plusI2:
  assumes "frontier_less_equal B t"
  shows "frontier_less_equal (A + B) t"
  using frontier_less_equal_antichain_plusI1[OF assms, of A]
  by (simp add: antichain_add_commute)

lemma exit_scope_memberE:
  assumes "y \<in>\<^sub>A exit_scope myfst A"
  obtains x where "x \<in>\<^sub>A A" and "myfst x = y"
proof -
  have y_front: "y \<in>\<^sub>A frontier (zmset_of (mset_set (myfst ` set_antichain A)))"
    using assms unfolding exit_scope_def o_def by simp
  have "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) y"
    using y_front by (simp add: in_frontier_iff)
  then obtain x where "x \<in> set_antichain A" and "myfst x = y"
    by auto
  then show ?thesis
    using that unfolding member_antichain.rep_eq by blast
qed

lemma frontier_less_equal_exit_scopeI:
  assumes "x \<in>\<^sub>A A"
  shows "frontier_less_equal (exit_scope myfst A) (myfst x)"
proof -
  have "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) (myfst x)"
    using assms by (simp add: member_antichain.rep_eq)
  then show ?thesis
    unfolding exit_scope_def o_def by (rule frontier_less_equal_zcount_pos)
qed

lemma frontier_less_equal_exit_scope_plusI1:
  assumes "x \<in>\<^sub>A A"
  shows "frontier_less_equal (exit_scope myfst (A + B)) (myfst x)"
proof -
  have fin: "finite (set_antichain A \<union> set_antichain B)"
    by simp
  have "x \<in> set_antichain A \<union> set_antichain B"
    using assms unfolding member_antichain.rep_eq by simp
  then obtain x' where x'_in: "x' \<in> minimal_antichain (set_antichain A \<union> set_antichain B)" and x'_le: "x' \<le> x"
    using minimal_antichain_member[OF fin] by blast
  then have "x' \<in>\<^sub>A A + B"
    unfolding member_antichain.rep_eq plus_antichain.rep_eq by simp
  then have "frontier_less_equal (exit_scope myfst (A + B)) (myfst x')"
    by (rule frontier_less_equal_exit_scopeI)
  then show ?thesis
    using myfst_mono[OF x'_le] by (rule frontier_less_equal_trans)
qed

lemma frontier_less_equal_exit_scope_plusI2:
  assumes "x \<in>\<^sub>A B"
  shows "frontier_less_equal (exit_scope myfst (A + B)) (myfst x)"
  using frontier_less_equal_exit_scope_plusI1[OF assms, of A]
  by (simp add: antichain_add_commute)

lemma exit_scope_plus_distrib:
  "exit_scope myfst (A + B) = exit_scope myfst A + exit_scope myfst B"
proof (rule antisym)
  show "exit_scope myfst (A + B) \<le> exit_scope myfst A + exit_scope myfst B"
    unfolding less_eq_antichain_def
  proof safe
    fix y
    assume y_in: "y \<in>\<^sub>A exit_scope myfst A + exit_scope myfst B"
    have "y \<in> set_antichain (exit_scope myfst A) \<union> set_antichain (exit_scope myfst B)"
      using y_in minimal_antichain_subset
      unfolding member_antichain.rep_eq plus_antichain.rep_eq by blast
    then show "\<exists>x. x \<in>\<^sub>A exit_scope myfst (A + B) \<and> x \<le> y"
    proof
      assume "y \<in> set_antichain (exit_scope myfst A)"
      then obtain x where x_in: "x \<in>\<^sub>A A" and y_eq: "myfst x = y"
        using exit_scope_memberE unfolding member_antichain.rep_eq by blast
      show ?thesis
        using frontier_less_equal_exit_scope_plusI1[OF x_in, of B]
        unfolding frontier_less_equal_iff2 y_eq by blast
    next
      assume "y \<in> set_antichain (exit_scope myfst B)"
      then obtain x where x_in: "x \<in>\<^sub>A B" and y_eq: "myfst x = y"
        using exit_scope_memberE unfolding member_antichain.rep_eq by blast
      show ?thesis
        using frontier_less_equal_exit_scope_plusI2[OF x_in, of A]
        unfolding frontier_less_equal_iff2 y_eq by blast
    qed
  qed
next
  show "exit_scope myfst A + exit_scope myfst B \<le> exit_scope myfst (A + B)"
    unfolding less_eq_antichain_def
  proof safe
    fix y
    assume y_in: "y \<in>\<^sub>A exit_scope myfst (A + B)"
    then obtain x where x_in: "x \<in>\<^sub>A A + B" and y_eq: "myfst x = y"
      using exit_scope_memberE by blast
    have "x \<in> set_antichain A \<union> set_antichain B"
      using x_in minimal_antichain_subset
      unfolding member_antichain.rep_eq plus_antichain.rep_eq by blast
    then show "\<exists>x. x \<in>\<^sub>A exit_scope myfst A + exit_scope myfst B \<and> x \<le> y"
    proof
      assume "x \<in> set_antichain A"
      then have "x \<in>\<^sub>A A"
        unfolding member_antichain.rep_eq by simp
      then have "frontier_less_equal (exit_scope myfst A) y"
        using frontier_less_equal_exit_scopeI[of x A] y_eq by simp
      then show ?thesis
        using frontier_less_equal_antichain_plusI1[of "exit_scope myfst A" y "exit_scope myfst B"]
        unfolding frontier_less_equal_iff2 by blast
    next
      assume "x \<in> set_antichain B"
      then have "x \<in>\<^sub>A B"
        unfolding member_antichain.rep_eq by simp
      then have "frontier_less_equal (exit_scope myfst B) y"
        using frontier_less_equal_exit_scopeI[of x B] y_eq by simp
      then show ?thesis
        using frontier_less_equal_antichain_plusI2[of "exit_scope myfst B" y "exit_scope myfst A"]
        unfolding frontier_less_equal_iff2 by blast
    qed
  qed
qed



value "exit_scope myfst (frontier {#MyPair (1 :: nat) (0 :: nat), MyPair (0 :: nat) (1 :: nat)#}\<^sub>z)"

definition label_propagation_op_logic where
  \<open>label_propagation_op_logic os = cUn (cUn
  (case (input os 0) of
    [] \<Rightarrow> {||}
  | (d, t) # xs \<Rightarrow>
    let (v1, v2) = trace (STR ''input0-------'') (de1 os d);
        t1 = trace (STR ''input0 edge: ('' +  show_nat v1 + STR '', '' + show_nat v2 + STR '')'') (myfst t);
        (l1, l2) = pairself (min_label os t1) (v1, v2);
        (v, l) = if l1 > l2 then (v1, l2) else (v2, l1);
        os' = os\<lparr>input := (input os)(0 := xs), timestamps := t1 # (timestamps os),
  graph := (graph os)(t1 := (graph os t1)(v1 := v2 # (graph os t1 v1),
    v2 := v1 # (graph os t1 v2))),
  vertices := (vertices os)(t1 := [v1, v2] @ (vertices os t1)),
  label := (label os)(t1 := (label os t1)(v := l))\<rparr>;
        ts = trace (STR ''input0 label upd: '' +  show_nat v + STR '': '' + show_nat l + STR '' @ '' + show_nat t1) (filter ((\<le>) t1) (timestamps os')) ;
        batch = concat (map (\<lambda> t1. let vs = neighbors os' t1 v in
          if min_label os t1 v > trace (STR ''neighbors: '' +  show_list show_nat vs) l
          then map (\<lambda>v'. (en1 os (v', l), Cap (MyPair t1 (mysnd t)) 1)) (filter (\<lambda>v'. min_label os t1 v' > l) vs)
          else []) ts)
     in trace (STR ''input0: looping back batch: '' + show_list (show_prod (show_prod show_nat show_nat) (show_myprod show_nat show_nat)) (map (\<lambda> (x, p). (de1 os x, time p)) batch)) {|release_caps (produces os' batch) 1|})
  (case input os 1 of
    [] \<Rightarrow> {||}
  | (d, t) # xs \<Rightarrow>
    let (v, l) = trace (STR ''input1-------'') (de1 os d);
        t1 = myfst t;
        os' = os\<lparr>input := (input os)(1 := xs),
          label := (label os)(t1 := (label os t1)(v := min (min_label os t1 v) l))\<rparr>;
        ts = trace (STR ''input1 label upd: '' +  show_nat v + STR '': '' + show_nat l + STR '' @ '' + show_nat t1) (filter ((\<le>) t1) (timestamps os)) ;
        batch = concat (map (\<lambda> t1. 
          let vs = neighbors os t1 v in 
          if min_label os t1 v > l
          then map (\<lambda>v'. (en1 os (v', l), Cap (MyPair t1 (mysnd t)) 1)) (filter (\<lambda>v'. min_label os' t1 v' > l) vs)
          else []) ts)
    in {|release_caps (produces os' batch) 1|}))
  (let below_times = filter (\<lambda> t. \<not> frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t)) (ocaps os 0);
       output_times = rmdups {} (map myfst below_times);
       batch = map (\<lambda>t. let cap = Cap (MyPair t 0) 0 in (en2 os ((components_from_labels (all_edges os t) (min_label os t))), cap)) output_times
   in if batch = []
        then {||}
        else {|(drop_caps ((produces os batch)) (map (\<lambda>t. Cap t 0) below_times ))|})\<close>

term components_from_labels
term "all_vertices os t "

term "components_from_labels (all_edges os t) (\<lambda> v. min_label os t v)"

(* @ map (\<lambda>t. Cap t 1) (filter P (ocaps os 1)) *)
definition label_propagation_op where
  \<open>label_propagation_op os = builder_op True cUNIV cUNIV os label_propagation_op_logic\<close>



(* FIXME: move me closer to dependencies *)

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


lemma outpu_release_caps[simp]:
  "outpu (release_caps os p) = outpu os"
  unfolding release_caps_def Let_def trace_simp
  by (auto split: list.splits)

lemma front_release_caps[simp]:
  "front (release_caps os p) = front os"
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

lemma input_release_caps[simp]:
  "input (release_caps os p) = input os"
  unfolding release_caps_def
  by auto

lemma min_label_produces[simp]:
  "min_label (produces os batch) = min_label os"
  unfolding produces_def min_label_def
  by (auto cong: if_cong)

lemma labels_cc_inv_drop_cap[simp]:
  "labels_cc_inv (drop_cap os cap) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def drop_cap_def
  by auto

lemma labels_cc_inv_drop_caps[simp]:
  "labels_cc_inv (drop_caps os caps) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def
  by simp

lemma labels_cc_inv_release_caps[simp]:
  "labels_cc_inv (release_caps os p) t = labels_cc_inv os t"
  unfolding release_caps_def Let_def trace_simp
  by simp

lemma labels_cc_inv_produces[simp]:
  "labels_cc_inv (produces os batch) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def
  by simp

lemma labels_cc_inv_delay_cap[simp]:
  "labels_cc_inv (delay_cap os cap incr) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def delay_cap_def
  by auto

lemma labels_cc_inv_produce[simp]:
  "labels_cc_inv (produce os cap batch) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def produce_def
  by auto

lemma labels_cc_inv_consume[simp]:
  "labels_cc_inv (consume os p t' len) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def consume_def
  by auto

lemma labels_cc_inv_mint_cap[simp]:
  "labels_cc_inv (mint_cap os p t') t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def mint_cap_def
  by auto

lemma labels_cc_inv_add_cap[simp]:
  "labels_cc_inv (add_cap os p t') t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def add_cap_def
  by auto

lemma labels_cc_inv_add_caps[simp]:
  "labels_cc_inv (add_caps os caps) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def add_caps_def
  by auto

lemma labels_cc_inv_consumes[simp]:
  "labels_cc_inv (consumes os p t' d) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def consumes_def add_caps_def BENQ_def
  by auto

lemma labels_cc_inv_fold_consumes[simp]:
  "labels_cc_inv (fold (\<lambda>(d, t') os'. consumes os' p t' d) xs os) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def fold_consumes
  by auto


lemma labels_cc_inv_obtain_progress[simp]:
  "labels_cc_inv (fst (obtain_progress os)) t = labels_cc_inv os t"
  unfolding labels_cc_inv_def all_vertices_def all_edges_def neighbors_def min_label_def obtain_progress_def
  by auto

lemma labels_cc_inv_mint[simp]:
  "labels_cc_inv (snd (mint os caps p t')) t = labels_cc_inv os t"
  unfolding mint_def
  by auto



end
