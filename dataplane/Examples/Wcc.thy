theory Wcc
  imports Main
begin

section \<open>Weakly Connected Components\<close>

context
  fixes edges :: \<open>('a::order \<times> 'a) set\<close> (\<open>E\<close>)
begin

subsection \<open>Undirected Reachability and Components\<close>

definition reachable where
  \<open>reachable x y \<equiv> (x, y) \<in> (E \<union> E\<inverse>)\<^sup>*\<close>

definition edge_vertices where
  \<open>edge_vertices = Field E\<close>

definition is_subcc :: \<open>'a set \<Rightarrow> bool\<close>  where
  \<open>is_subcc S \<equiv> S \<subseteq> edge_vertices \<and> (\<forall>x \<in> S. \<forall>y \<in> S. reachable x y)\<close>

definition is_cc :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>is_cc S \<equiv> S \<noteq> {} \<and> is_subcc S \<and> (\<forall>S'. S \<subseteq> S' \<and> is_subcc S' \<longrightarrow> S' = S)\<close>

abbreviation ccs :: \<open>'a set set\<close> where
  \<open>ccs \<equiv> {S. is_cc S}\<close>

definition is_ccs :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>is_ccs \<equiv> (=) ccs\<close>

lemma Ex1_is_ccs:
  \<open>Ex1 is_ccs\<close>
  unfolding is_ccs_def by blast

definition cc_of where
  \<open>cc_of v = {u \<in> edge_vertices. reachable v u}\<close>

definition labels_inv  where
  "labels_inv l \<longleftrightarrow> (\<forall>v \<in> edge_vertices. l v \<in> cc_of v)"

definition labels_stable where
  "labels_stable l \<longleftrightarrow> (\<forall>v u. (v, u) \<in> E \<union> E\<inverse> \<longrightarrow> l v \<le> l u)"

definition components_from_labels where
  "components_from_labels l = ((\<lambda>a. {v \<in> edge_vertices. l v = a}) ` (l ` edge_vertices))"

subsection \<open>Basic Reachability Facts\<close>

lemma reachable_refl:
  "reachable v v"
  unfolding reachable_def by simp

lemma reachable_trans:
  assumes "reachable u v" and "reachable v w"
  shows "reachable u w"
  using assms unfolding reachable_def by (rule rtrancl_trans)

lemma reachable_sym:
  assumes "reachable u v"
  shows "reachable v u"
  using assms unfolding reachable_def
proof (induction rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have "(z, y) \<in> E \<union> E\<inverse>"
    using step.hyps(2) by auto
  then have "(z, y) \<in> (E \<union> E\<inverse>)\<^sup>*"
    by (rule r_into_rtrancl)
  also have "(y, u) \<in> (E \<union> E\<inverse>)\<^sup>*"
    by (rule step.IH)
  finally show ?case .
qed

subsection \<open>Connected Components\<close>

lemma cc_ofI:
  assumes "u \<in> edge_vertices" and "reachable v u"
  shows "u \<in> cc_of v"
  using assms unfolding cc_of_def by simp

lemma cc_ofD:
  assumes "u \<in> cc_of v"
  shows "reachable v u"
  using assms unfolding cc_of_def by simp

lemma cc_of_self:
  assumes "v \<in> edge_vertices"
  shows "v \<in> cc_of v"
  using assms reachable_refl by (rule cc_ofI)

lemma cc_of_nonempty:
  assumes "v \<in> edge_vertices"
  shows "cc_of v \<noteq> {}"
  using assms cc_of_self by blast

lemma cc_of_eq_if_reachable:
  assumes "reachable u v"
  shows "cc_of u = cc_of v"
proof (intro set_eqI iffI)
  fix w
  assume "w \<in> cc_of u"
  then have "reachable u w"
    by (rule cc_ofD)
  moreover have "reachable v u"
    using assms by (rule reachable_sym)
  ultimately have "reachable v w"
    by (meson reachable_trans)
  then show "w \<in> cc_of v"
    using \<open>w \<in> cc_of u\<close> unfolding cc_of_def by simp
next
  fix w
  assume "w \<in> cc_of v"
  then have "reachable v w"
    by (rule cc_ofD)
  then have "reachable u w"
    using assms by (meson reachable_trans)
  then show "w \<in> cc_of u"
    using \<open>w \<in> cc_of v\<close> unfolding cc_of_def by simp
qed

lemma cc_of_eq_if_member:
  assumes "u \<in> cc_of v"
  shows "cc_of u = cc_of v"
  using assms cc_ofD cc_of_eq_if_reachable reachable_sym by blast

lemma cc_of_is_subcc:
  "is_subcc (cc_of v)"
  unfolding is_subcc_def cc_of_def by (auto intro: reachable_sym reachable_trans)

lemma cc_of_is_cc:
  assumes "v \<in> edge_vertices"
  shows "is_cc (cc_of v)"
  unfolding is_cc_def
proof (intro conjI allI impI)
  show "cc_of v \<noteq> {}"
    using assms by (rule cc_of_nonempty)
  show "is_subcc (cc_of v)"
    by (rule cc_of_is_subcc)
next
  fix S'
  assume "cc_of v \<subseteq> S' \<and> is_subcc S'"
  then have subset: "cc_of v \<subseteq> S'" and subcc: "is_subcc S'"
    by simp_all
  show "S' = cc_of v"
  proof (intro set_eqI iffI)
    fix x
    assume "x \<in> S'"
    have "v \<in> S'"
      using assms subset cc_of_self by blast
    then have "reachable v x"
      using subcc \<open>x \<in> S'\<close> unfolding is_subcc_def by blast
    then show "x \<in> cc_of v"
      using subcc \<open>x \<in> S'\<close> unfolding cc_of_def is_subcc_def by blast
  next
    fix x
    assume "x \<in> cc_of v"
    then show "x \<in> S'"
      using subset by blast
  qed
qed

lemma cc_of_in_ccs:
  assumes "v \<in> edge_vertices"
  shows "cc_of v \<in> ccs"
  using assms cc_of_is_cc by simp

lemma cc_of_disjoint_or_eq:
  "cc_of u \<inter> cc_of v = {} \<or> cc_of u = cc_of v"
proof (cases "cc_of u \<inter> cc_of v = {}")
  case False
  then obtain w where "w \<in> cc_of u" and "w \<in> cc_of v"
    by blast
  then have "cc_of w = cc_of u" and "cc_of w = cc_of v"
    using cc_of_eq_if_member by blast+
  then show ?thesis
    by blast
qed simp

lemma Union_ccs:
  "\<Union>ccs = edge_vertices"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> \<Union>ccs"
  then obtain C where "C \<in> ccs" and "x \<in> C"
    by auto
  then show "x \<in> edge_vertices"
    unfolding is_cc_def is_subcc_def by auto
next
  fix x
  assume "x \<in> edge_vertices"
  then have "cc_of x \<in> ccs" and "x \<in> cc_of x"
    using cc_of_in_ccs cc_of_self by auto
  then show "x \<in> \<Union>ccs"
    by auto
qed


lemma is_cc_eq_cc_of:
  assumes "is_cc S" and "x \<in> S"
  shows "S = cc_of x"
proof -
  have subcc: "is_subcc S"
    using assms(1) unfolding is_cc_def by simp
  have "S \<subseteq> cc_of x"
  proof
    fix y
    assume "y \<in> S"
    then have "reachable x y"
      using subcc assms(2) unfolding is_subcc_def by blast
    show "y \<in> cc_of x"
      using subcc assms(2) \<open>y \<in> S\<close> unfolding cc_of_def is_subcc_def by blast
  qed
  moreover have "is_subcc (cc_of x)"
    by (rule cc_of_is_subcc)
  ultimately have "cc_of x = S"
    using assms(1) unfolding is_cc_def by blast
  then show ?thesis
    by simp
qed

subsection \<open>Label Invariants\<close>

lemma labels_invI:
  assumes "\<And>v. v \<in> edge_vertices \<Longrightarrow> l v \<in> cc_of v"
  shows "labels_inv l"
  using assms unfolding labels_inv_def by simp

lemma labels_invD:
  assumes "labels_inv l" and "v \<in> edge_vertices"
  shows "l v \<in> cc_of v"
  using assms unfolding labels_inv_def by simp

lemma labels_inv_reachable:
  assumes "labels_inv l" and "v \<in> edge_vertices"
  shows "reachable v (l v)"
  using labels_invD[OF assms] by (rule cc_ofD)

lemma labels_inv_same_label_reachable:
  assumes "labels_inv l" and "x \<in> edge_vertices" and "y \<in> edge_vertices" and "l x = l y"
  shows "reachable x y"
proof -
  have "reachable x (l x)"
    using assms(1,2) by (rule labels_inv_reachable)
  then have "reachable x (l y)"
    using assms(4) by simp
  moreover have "reachable (l y) y"
    using labels_inv_reachable[OF assms(1,3)] by (rule reachable_sym)
  ultimately show ?thesis
    by (rule reachable_trans)
qed

lemma labels_inv_label_class_is_subcc:
  assumes "labels_inv l"
  shows "is_subcc {v \<in> edge_vertices. l v = a}"
  unfolding is_subcc_def by (auto intro: labels_inv_same_label_reachable[OF assms])

subsection \<open>Stable Labels\<close>

lemma labels_stableD:
  assumes "labels_stable l" and "(v, u) \<in> E \<union> E\<inverse>"
  shows "l v \<le> l u"
  using assms unfolding labels_stable_def by auto

lemma labels_stable_edge_eq:
  assumes "labels_stable (l :: 'a \<Rightarrow> 'b::order)" and "(v, u) \<in> E \<union> E\<inverse>"
  shows "l v = l u"
proof -
  have uv: "(u, v) \<in> E \<union> E\<inverse>"
    using assms(2) by auto
  have "l v \<le> l u"
    using assms by (rule labels_stableD)
  moreover have "l u \<le> l v"
    using assms(1) uv by (rule labels_stableD)
  ultimately show ?thesis
    by (metis order_antisym)
qed

lemma labels_stable_edge_eq_E:
  assumes "labels_stable (l :: 'a \<Rightarrow> 'b::order)" and "(v, u) \<in> E"
  shows "l v = l u"
  using assms by (auto intro: labels_stable_edge_eq)

lemma labels_stable_reachable_eq:
  assumes "labels_stable (l :: 'a \<Rightarrow> 'b::order)" and "reachable u v"
  shows "l u = l v"
  using assms(2) unfolding reachable_def
proof (induction rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have "l y = l z"
    using assms(1) step.hyps(2) by (rule labels_stable_edge_eq)
  then show ?case
    using step.IH by simp
qed

subsection \<open>Components Induced by Stable Labels\<close>

lemma label_class_eq_cc_of:
  assumes "labels_inv l" and "labels_stable (l :: 'a \<Rightarrow> 'a)" and "x \<in> edge_vertices"
  shows "{v \<in> edge_vertices. l v = l x} = cc_of x"
proof (intro set_eqI iffI)
  fix v
  assume v_class: "v \<in> {v \<in> edge_vertices. l v = l x}"
  then have v_edge: "v \<in> edge_vertices"
    by simp
  from v_class have eq: "l v = l x"
    by simp
  have lv_v: "l v \<in> cc_of v"
    using labels_invD[OF assms(1) v_edge] .
  have lx_x: "l x \<in> cc_of x"
    using assms(1,3) by (rule labels_invD)
  have "cc_of v = cc_of (l v)"
    using cc_of_eq_if_member[OF lv_v] by simp
  also have "... = cc_of (l x)"
    using eq by simp
  also have "... = cc_of x"
    using cc_of_eq_if_member[OF lx_x] by simp
  finally have "cc_of v = cc_of x" .
  moreover have "v \<in> cc_of v"
    using v_class by (auto intro: cc_of_self)
  ultimately show "v \<in> cc_of x"
    by simp
next
  fix v
  assume "v \<in> cc_of x"
  then have "reachable x v"
    by (rule cc_ofD)
  have "l x = l v"
    using assms(2) \<open>reachable x v\<close> by (rule labels_stable_reachable_eq)
  then show "v \<in> {v \<in> edge_vertices. l v = l x}"
    using \<open>v \<in> cc_of x\<close> unfolding cc_of_def by simp
qed

lemma components_from_labels_correct:
  assumes "labels_inv l" and "labels_stable (l :: 'a \<Rightarrow> 'a)"
  shows "components_from_labels l = ccs"
proof (intro set_eqI iffI)
  fix C
  assume "C \<in> components_from_labels l"
  then obtain x where "x \<in> edge_vertices" and C: "C = {v \<in> edge_vertices. l v = l x}"
    unfolding components_from_labels_def by auto
  then have "C = cc_of x"
    using label_class_eq_cc_of[OF assms, of x] by simp
  then show "C \<in> ccs"
    using \<open>x \<in> edge_vertices\<close> cc_of_in_ccs by simp
next
  fix C
  assume "C \<in> ccs"
  then have is_cc_C: "is_cc C"
    by simp
  then have "C \<noteq> {}"
    unfolding is_cc_def by simp
  then obtain x where "x \<in> C"
    by blast
  then have "x \<in> edge_vertices"
    using is_cc_C unfolding is_cc_def is_subcc_def by blast
  have C_eq: "C = cc_of x"
    using is_cc_eq_cc_of[OF is_cc_C \<open>x \<in> C\<close>] .
  have "C = {v \<in> edge_vertices. l v = l x}"
    using C_eq label_class_eq_cc_of[OF assms \<open>x \<in> edge_vertices\<close>] by simp
  then show "C \<in> components_from_labels l"
    unfolding components_from_labels_def using \<open>x \<in> edge_vertices\<close> by auto
qed

end


term components_from_labels

value "components_from_labels {(0 :: nat, 1), (1, 2)} (\<lambda> _. 0 :: nat)"

end
