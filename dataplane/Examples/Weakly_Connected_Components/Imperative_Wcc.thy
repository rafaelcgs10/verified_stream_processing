theory Imperative_Wcc
  imports
    "Refine_Monadic.Refine_Monadic"
    Wcc
begin

section \<open>Imperative Weakly Connected Components\<close>

text \<open>
  The label propagation algorithm in the refinement framework, verified
  against the weakly connected components specification of theory Wcc.
  Reachability symmetrizes the edge relation, so no symmetry assumption
  on the edges is needed, and the vertices are the ones occurring in
  some edge.
\<close>

type_synonym 'v labels = "'v \<Rightarrow> 'v"

subsection \<open>Labels and Local Updates\<close>

text \<open>
  A label @{term "l v"} is the current representative candidate for vertex
  @{term v}.  A local update replaces @{term "l v"} by the minimum of its
  current label and the labels currently seen on its adjacent vertices.
\<close>

definition adjacent :: "('v \<times> 'v) set \<Rightarrow> 'v \<Rightarrow> 'v set" where
  "adjacent E v = {u. (v, u) \<in> E \<union> E\<inverse>}"

definition min_adjacent_label :: "('v::linorder \<times> 'v) set \<Rightarrow> 'v labels \<Rightarrow> 'v \<Rightarrow> 'v" where
  "min_adjacent_label E l v = Min (insert (l v) (l ` adjacent E v))"

subsection \<open>One Propagation Round\<close>

definition round_inv :: "('v::linorder \<times> 'v) set \<Rightarrow> 'v labels \<Rightarrow> 'v set \<times> 'v labels \<times> bool \<Rightarrow> bool" where
  "round_inv E l0 s \<longleftrightarrow> (case s of (todo, l, changed) \<Rightarrow>
     todo \<subseteq> edge_vertices E \<and> labels_inv E l \<and>
     labels_measure E l \<le> labels_measure E l0 \<and>
     (changed \<longrightarrow> labels_measure E l < labels_measure E l0) \<and>
     (\<not> changed \<longrightarrow> (\<forall>v \<in> edge_vertices E - todo. min_adjacent_label E l v = l v)))"

definition wcc_round :: "('v::linorder \<times> 'v) set \<Rightarrow> 'v labels \<Rightarrow> ('v labels \<times> bool) nres" where
  "wcc_round E l = do {
     (_, l', changed) \<leftarrow>
       WHILE\<^sub>T\<^bsup>round_inv E l\<^esup>
         (\<lambda>(todo, l, changed). todo \<noteq> {})
         (\<lambda>(todo, l, changed). do {
            v \<leftarrow> SPEC (\<lambda>v. v \<in> todo);
            let m = min_adjacent_label E l v;
            RETURN (todo - {v}, l(v := m), changed \<or> m < l v)
         })
         (edge_vertices E, l, False);
      RETURN (l', changed)
    }"

subsection \<open>Outer Fixed-Point Loop\<close>

definition outer_inv :: "('v::linorder \<times> 'v) set \<Rightarrow> 'v labels \<times> bool \<Rightarrow> bool" where
  "outer_inv E s \<longleftrightarrow> (case s of (l, changed) \<Rightarrow>
     labels_inv E l \<and> (\<not> changed \<longrightarrow> labels_stable E l))"

definition wcc_labels :: "('v::linorder \<times> 'v) set \<Rightarrow> 'v labels nres" where
  "wcc_labels E = do {
     (l, _) \<leftarrow>
       WHILE\<^sub>T\<^bsup>outer_inv E\<^esup>
         (\<lambda>(l, changed). changed)
         (\<lambda>(l, changed). wcc_round E l)
         (id, True);
      RETURN l
    }"

definition weak_components :: "('v::linorder \<times> 'v) set \<Rightarrow> 'v set set nres" where
  "weak_components E = do {
     l \<leftarrow> wcc_labels E;
     RETURN (components_from_labels E l)
   }"

subsection \<open>Adjacency Facts\<close>

lemma finite_V:
  assumes fin: "finite E"
  shows "finite (edge_vertices E)"
  using fin unfolding edge_vertices_def by (simp add: finite_Field)

lemma adjacent_subset_V: "adjacent E v \<subseteq> edge_vertices E"
  unfolding adjacent_def edge_vertices_def Field_def by auto

lemma finite_adjacent:
  fixes E :: "('v::order \<times> 'v) set"
  assumes fin: "finite E"
  shows "finite (adjacent E v)"
  by (rule finite_subset[OF adjacent_subset_V finite_V[OF fin]])

lemma adjacent_in_V:
  assumes "u \<in> adjacent E v"
  shows "u \<in> edge_vertices E"
  using assms adjacent_subset_V by blast

lemma adjacent_in_cc_of:
  assumes "u \<in> adjacent E v"
  shows "u \<in> cc_of E v"
proof (rule cc_ofI)
  show "u \<in> edge_vertices E"
    using assms by (rule adjacent_in_V)
  show "reachable E v u"
    using assms unfolding adjacent_def reachable_def
    by (auto intro: r_into_rtrancl)
qed

lemma cc_of_adjacent_eq:
  assumes "u \<in> adjacent E v"
  shows "cc_of E u = cc_of E v"
  using adjacent_in_cc_of[OF assms] by (rule cc_of_eq_if_member)

lemma cc_of_subset_V:
  "cc_of E v \<subseteq> edge_vertices E"
  unfolding cc_of_def by blast

lemma labels_inv_in_V:
  assumes "labels_inv E l" and "v \<in> edge_vertices E"
  shows "l v \<in> edge_vertices E"
  using labels_invD[OF assms] cc_of_subset_V by blast

lemma min_adjacent_label_le_self:
  assumes fin: "finite E"
  shows "min_adjacent_label E l v \<le> l v"
  unfolding min_adjacent_label_def
  using finite_adjacent[OF fin] by simp

lemma min_adjacent_label_in_cc_of:
  assumes fin: "finite E" and inv: "labels_inv E l" and v: "v \<in> edge_vertices E"
  shows "min_adjacent_label E l v \<in> cc_of E v"
proof -
  have "insert (l v) (l ` adjacent E v) \<subseteq> cc_of E v"
  proof
    fix x
    assume "x \<in> insert (l v) (l ` adjacent E v)"
    then show "x \<in> cc_of E v"
    proof
      assume "x = l v"
      then show ?thesis
        using inv v by (simp add: labels_invD)
    next
      assume "x \<in> l ` adjacent E v"
      then obtain u where "u \<in> adjacent E v" and "x = l u"
        by auto
      then have "u \<in> edge_vertices E"
        by (simp add: adjacent_in_V)
      have "l u \<in> cc_of E u"
        using inv \<open>u \<in> edge_vertices E\<close> by (rule labels_invD)
      also have "cc_of E u = cc_of E v"
        using \<open>u \<in> adjacent E v\<close> by (rule cc_of_adjacent_eq)
      finally show ?thesis
        using \<open>x = l u\<close> by simp
    qed
  qed
  moreover have "min_adjacent_label E l v \<in> insert (l v) (l ` adjacent E v)"
    unfolding min_adjacent_label_def
    by (intro Min_in) (simp_all add: finite_adjacent[OF fin])
  ultimately show ?thesis
    by blast
qed

lemma labels_inv_update:
  assumes fin: "finite E" and inv: "labels_inv E l" and v: "v \<in> edge_vertices E"
  shows "labels_inv E (l(v := min_adjacent_label E l v))"
  unfolding labels_inv_def
proof (intro ballI)
  fix u
  assume "u \<in> edge_vertices E"
  then show "(l(v := min_adjacent_label E l v)) u \<in> cc_of E u"
    using min_adjacent_label_in_cc_of[OF fin inv v] labels_invD[OF inv]
    by (cases "u = v") simp_all
qed

subsection \<open>Round Invariant Setup\<close>

lemma round_inv_initial:
  assumes "labels_inv E l"
  shows "round_inv E l (edge_vertices E, l, False)"
  using assms unfolding round_inv_def by simp

lemma round_inv_labels_invD:
  assumes "round_inv E l0 (todo, l, changed)"
  shows "labels_inv E l"
  using assms unfolding round_inv_def by simp

lemma round_inv_todo_subsetD:
  assumes "round_inv E l0 (todo, l, changed)"
  shows "todo \<subseteq> edge_vertices E"
  using assms unfolding round_inv_def by simp

lemma round_inv_measure_leD:
  assumes "round_inv E l0 (todo, l, changed)"
  shows "labels_measure E l \<le> labels_measure E l0"
  using assms unfolding round_inv_def by simp

lemma labels_inv_id:
  "labels_inv E id"
  unfolding labels_inv_def
  by (auto intro: cc_of_self)

lemma outer_inv_initial:
  "outer_inv E (id, True)"
  using labels_inv_id unfolding outer_inv_def by simp

subsection \<open>Measure Facts\<close>

lemma finite_rank_set:
  assumes fin: "finite E"
  shows "finite {y \<in> edge_vertices E. y < x}"
  using finite_V[OF fin] by simp

lemma rank_strict_mono:
  assumes fin: "finite E"
    and x: "x \<in> edge_vertices E" and y: "y \<in> edge_vertices E" and xy: "x < y"
  shows "rank E x < rank E y"
proof -
  let ?X = "{z \<in> edge_vertices E. z < x}"
  let ?Y = "{z \<in> edge_vertices E. z < y}"
  have "?X \<subseteq> ?Y"
    using xy by auto
  moreover have "x \<in> ?Y" and "x \<notin> ?X"
    using x xy by simp_all
  ultimately have "?X \<subset> ?Y"
    by blast
  then have "card ?X < card ?Y"
    using finite_rank_set[OF fin] by (intro psubset_card_mono) simp_all
  then show ?thesis
    unfolding rank_def .
qed

lemma rank_min_adjacent_label_le_self:
  assumes fin: "finite E" and inv: "labels_inv E l" and v: "v \<in> edge_vertices E"
  shows "rank E (min_adjacent_label E l v) \<le> rank E (l v)"
proof (cases "min_adjacent_label E l v = l v")
  case True
  then show ?thesis by simp
next
  case False
  then have "min_adjacent_label E l v < l v"
    using min_adjacent_label_le_self[OF fin] by (simp add: order_less_le)
  moreover have "min_adjacent_label E l v \<in> edge_vertices E"
    using min_adjacent_label_in_cc_of[OF fin inv v] cc_of_subset_V by blast
  moreover have "l v \<in> edge_vertices E"
    using inv v by (rule labels_inv_in_V)
  ultimately show ?thesis
    using rank_strict_mono[OF fin] by (simp add: order_less_imp_le)
qed

lemma labels_measure_update_decreases:
  assumes fin: "finite E" and inv: "labels_inv E l" and v: "v \<in> edge_vertices E"
    and less: "min_adjacent_label E l v < l v"
  shows "labels_measure E (l(v := min_adjacent_label E l v)) < labels_measure E l"
proof -
  have "min_adjacent_label E l v \<in> edge_vertices E"
    using min_adjacent_label_in_cc_of[OF fin inv v] cc_of_subset_V by blast
  have "l v \<in> edge_vertices E"
    using inv v by (rule labels_inv_in_V)
  have "rank E (min_adjacent_label E l v) < rank E (l v)"
    using fin \<open>min_adjacent_label E l v \<in> edge_vertices E\<close> \<open>l v \<in> edge_vertices E\<close> less
    by (rule rank_strict_mono)
  have "labels_measure E (l(v := min_adjacent_label E l v)) =
      (\<Sum>u \<in> edge_vertices E - {v}. rank E (l u)) + rank E (min_adjacent_label E l v)"
    unfolding labels_measure_def using finite_V[OF fin] v by (simp add: sum.remove)
  also have "... < (\<Sum>u \<in> edge_vertices E - {v}. rank E (l u)) + rank E (l v)"
    using \<open>rank E (min_adjacent_label E l v) < rank E (l v)\<close> by simp
  also have "... = labels_measure E l"
    unfolding labels_measure_def using finite_V[OF fin] v by (simp add: sum.remove)
  finally show ?thesis .
qed

lemma labels_measure_update_le:
  assumes fin: "finite E" and inv: "labels_inv E l" and v: "v \<in> edge_vertices E"
  shows "labels_measure E (l(v := min_adjacent_label E l v)) \<le> labels_measure E l"
proof -
  have "labels_measure E (l(v := min_adjacent_label E l v)) =
      (\<Sum>u \<in> edge_vertices E - {v}. rank E (l u)) + rank E (min_adjacent_label E l v)"
    unfolding labels_measure_def using finite_V[OF fin] v by (simp add: sum.remove)
  also have "... \<le> (\<Sum>u \<in> edge_vertices E - {v}. rank E (l u)) + rank E (l v)"
    using rank_min_adjacent_label_le_self[OF fin inv v] by simp
  also have "... = labels_measure E l"
    unfolding labels_measure_def using finite_V[OF fin] v by (simp add: sum.remove)
  finally show ?thesis .
qed

subsection \<open>Round Correctness\<close>

lemma round_step_preserves_round_inv:
  assumes fin: "finite E"
    and step: "round_inv E l0 (todo, l, changed)" and v: "v \<in> todo"
  shows "round_inv E l0 (todo - {v}, l(v := min_adjacent_label E l v),
    changed \<or> min_adjacent_label E l v < l v)"
proof -
  have "todo \<subseteq> edge_vertices E"
    using step by (rule round_inv_todo_subsetD)
  then have vV: "v \<in> edge_vertices E"
    using v by auto
  have inv: "labels_inv E l"
    using step by (rule round_inv_labels_invD)
  have "labels_inv E (l(v := min_adjacent_label E l v))"
    using labels_inv_update[OF fin inv vV] .
  have "todo - {v} \<subseteq> edge_vertices E"
    using \<open>todo \<subseteq> edge_vertices E\<close> by auto
  have "labels_measure E (l(v := min_adjacent_label E l v)) \<le> labels_measure E l0"
    using labels_measure_update_le[OF fin inv vV]
      round_inv_measure_leD[OF step] by linarith
  have "changed \<or> min_adjacent_label E l v < l v \<Longrightarrow>
      labels_measure E (l(v := min_adjacent_label E l v)) < labels_measure E l0"
  proof -
    assume "changed \<or> min_adjacent_label E l v < l v"
    then show "labels_measure E (l(v := min_adjacent_label E l v)) < labels_measure E l0"
    proof
      assume "changed"
      then have "labels_measure E l < labels_measure E l0"
        using step unfolding round_inv_def by simp
      moreover have "labels_measure E (l(v := min_adjacent_label E l v)) \<le> labels_measure E l"
        using labels_measure_update_le[OF fin inv vV] .
      ultimately show ?thesis by linarith
    next
      assume "min_adjacent_label E l v < l v"
      then have "labels_measure E (l(v := min_adjacent_label E l v)) < labels_measure E l"
        using labels_measure_update_decreases[OF fin inv vV] by simp
      moreover have "labels_measure E l \<le> labels_measure E l0"
        using step by (rule round_inv_measure_leD)
      ultimately show ?thesis by linarith
    qed
  qed
  have "\<not> (changed \<or> min_adjacent_label E l v < l v) \<Longrightarrow>
      (\<forall>u \<in> edge_vertices E - (todo - {v}).
        min_adjacent_label E (l(v := min_adjacent_label E l v)) u =
        (l(v := min_adjacent_label E l v)) u)"
  proof -
    assume no_change: "\<not> (changed \<or> min_adjacent_label E l v < l v)"
    then have not_changed: "\<not> changed"
      by simp
    have "min_adjacent_label E l v \<le> l v"
      by (rule min_adjacent_label_le_self[OF fin])
    moreover from no_change have "\<not> min_adjacent_label E l v < l v"
      by simp
    then have "l v \<le> min_adjacent_label E l v"
      by simp
    ultimately have m_eq: "min_adjacent_label E l v = l v"
      by (rule order_antisym)
    have upd_id: "l(v := min_adjacent_label E l v) = l"
      using m_eq by simp
    have old_processed: "\<forall>u \<in> edge_vertices E - todo. min_adjacent_label E l u = l u"
      using step not_changed unfolding round_inv_def by simp
    have "\<forall>u \<in> edge_vertices E - (todo - {v}). min_adjacent_label E l u = l u"
    proof
      fix u
      assume "u \<in> edge_vertices E - (todo - {v})"
      then have "u = v \<or> u \<in> edge_vertices E - todo"
        by auto
      then show "min_adjacent_label E l u = l u"
        using m_eq old_processed by auto
    qed
    then show ?thesis
      using upd_id by simp
  qed
  show ?thesis
    using \<open>todo - {v} \<subseteq> edge_vertices E\<close>
      \<open>labels_inv E (l(v := min_adjacent_label E l v))\<close>
      \<open>labels_measure E (l(v := min_adjacent_label E l v)) \<le> labels_measure E l0\<close>
      \<open>changed \<or> min_adjacent_label E l v < l v \<Longrightarrow>
        labels_measure E (l(v := min_adjacent_label E l v)) < labels_measure E l0\<close>
      \<open>\<not> (changed \<or> min_adjacent_label E l v < l v) \<Longrightarrow>
        (\<forall>u \<in> edge_vertices E - (todo - {v}).
          min_adjacent_label E (l(v := min_adjacent_label E l v)) u =
          (l(v := min_adjacent_label E l v)) u)\<close>
    unfolding round_inv_def by simp
qed

lemma min_adjacent_label_all_eq_imp_stable:
  assumes fin: "finite E"
    and all_eq: "\<And>v. v \<in> edge_vertices E \<Longrightarrow> min_adjacent_label E l v = l v"
  shows "labels_stable E l"
  unfolding labels_stable_def
proof (intro allI impI)
  fix v u
  assume vu: "(v, u) \<in> E \<union> E\<inverse>"
  then have "u \<in> adjacent E v"
    unfolding adjacent_def by simp
  then have "l u \<in> insert (l v) (l ` adjacent E v)"
    by simp
  then have "min_adjacent_label E l v \<le> l u"
    unfolding min_adjacent_label_def
    by (intro Min_le) (simp_all add: finite_adjacent[OF fin])
  moreover have "v \<in> edge_vertices E"
    using vu unfolding edge_vertices_def Field_def by auto
  ultimately show "l v \<le> l u"
    using all_eq by simp
qed

lemma round_inv_no_change_stable:
  assumes fin: "finite E" and inv: "round_inv E l0 ({}, l, False)"
  shows "labels_stable E l"
proof (rule min_adjacent_label_all_eq_imp_stable[OF fin])
  fix v
  assume "v \<in> edge_vertices E"
  then show "min_adjacent_label E l v = l v"
    using inv unfolding round_inv_def by simp
qed

lemma wcc_round_correct:
  assumes fin: "finite E" and inv: "labels_inv E l"
  shows "wcc_round E l \<le> SPEC (\<lambda>(l', changed). labels_inv E l' \<and>
    labels_measure E l' \<le> labels_measure E l \<and>
    (changed \<longrightarrow> labels_measure E l' < labels_measure E l) \<and>
    (\<not> changed \<longrightarrow> labels_stable E l'))"
  unfolding wcc_round_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(todo, l, changed). card todo)"])
  subgoal by simp
  subgoal using inv by (rule round_inv_initial)
  subgoal for s a b aa ba x
  proof -
    assume rinv: "round_inv E l s"
      and s_eq: "s = (a, b)"
      and b_eq: "b = (aa, ba)"
      and x: "x \<in> a"
    have "s = (a, aa, ba)"
      using s_eq b_eq by simp
    then have "round_inv E l (a, aa, ba)"
      using rinv by simp
    then show "round_inv E l (a - {x}, aa(x := min_adjacent_label E aa x),
      ba \<or> min_adjacent_label E aa x < aa x)"
      using x by (rule round_step_preserves_round_inv[OF fin])
  qed
  subgoal for s a b aa ba x
  proof -
    assume rinv: "round_inv E l s"
      and s_eq: "s = (a, b)"
      and b_eq: "b = (aa, ba)"
      and x: "x \<in> a"
    have s_trip: "s = (a, aa, ba)"
      using s_eq b_eq by simp
    then have inv_trip: "round_inv E l (a, aa, ba)"
      using rinv by simp
    have "a \<subseteq> edge_vertices E"
      using inv_trip by (rule round_inv_todo_subsetD)
    then have "finite a"
      using finite_V[OF fin] finite_subset by blast
    have "a \<noteq> {}"
      using x by blast
    have "0 < card a"
      using \<open>finite a\<close> \<open>a \<noteq> {}\<close> by (simp add: card_gt_0_iff)
    show "((a - {x}, aa(x := min_adjacent_label E aa x),
      ba \<or> min_adjacent_label E aa x < aa x), s) \<in>
      measure (\<lambda>(todo, l, changed). card todo)"
      using s_trip x \<open>finite a\<close> \<open>0 < card a\<close> by simp
  qed
  subgoal for s
    by (cases s) (simp add: round_inv_def)
  subgoal for s
    by (cases s) (simp add: round_inv_def)
  subgoal for s
    by (cases s) (simp add: round_inv_def)
  subgoal for s
    by (cases s) (auto simp add: round_inv_no_change_stable[OF fin])
  done

subsection \<open>Outer Loop Correctness\<close>

lemma wcc_labels_correct:
  assumes fin: "finite E"
  shows "wcc_labels E \<le> SPEC (\<lambda>l. labels_inv E l \<and> labels_stable E l)"
  unfolding wcc_labels_def
  apply (refine_vcg WHILEIT_rule[where R=
        "measure (\<lambda>(l, changed). labels_measure E l + (if changed then 1 else 0))"])
  subgoal by simp
  subgoal by (rule outer_inv_initial)
  subgoal for s l changed
    apply (rule order_trans[OF wcc_round_correct[OF fin]])
     apply (cases s; simp add: outer_inv_def)
    apply (rule SPEC_rule)
    apply (rename_tac r)
    apply (case_tac r)
    apply (auto simp add: outer_inv_def split: if_splits)
    done
  subgoal for s l changed
    by (cases s) (simp add: outer_inv_def)
  subgoal for s l changed
    by (cases s) (simp add: outer_inv_def)
  done

lemma weak_components_correct:
  assumes fin: "finite E"
  shows "weak_components E \<le> SPEC (\<lambda>Cs. Cs = ccs E)"
  unfolding weak_components_def
  apply (rule bind_rule)
  apply (rule order_trans[OF wcc_labels_correct[OF fin]])
  apply (rule SPEC_rule)
  subgoal for l
    using components_from_labels_correct[of E l] by auto
  done

end
