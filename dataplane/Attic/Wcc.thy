theory Wcc
  imports
    "Refine_Monadic.Refine_Monadic"
begin

section \<open>Weakly Connected Components\<close>

text \<open>
  We work with a finite graph whose edge relation is already symmetric.  Thus
  weak connectivity is ordinary reachability in the edge relation.
\<close>

type_synonym 'v labels = "'v \<Rightarrow> 'v"

locale finite_symmetric_graph =
  fixes V :: "'v::linorder set"
    and E :: "('v \<times> 'v) set"
  assumes finite_V: "finite V"
    and E_wf: "E \<subseteq> V \<times> V"
    and E_sym: "sym E"
begin

subsection \<open>Component Specification\<close>

text \<open>
  The abstract result is a set of connected components over the finite vertex
  set @{term V}.  Since @{term E} is assumed symmetric, weak reachability is
  just reflexive-transitive reachability along @{term E}.
\<close>

definition reachable :: "'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "reachable x y \<longleftrightarrow> (x, y) \<in> E\<^sup>*"

definition cc_of :: "'v \<Rightarrow> 'v set" where
  "cc_of v = {u \<in> V. reachable v u}"

definition wccs :: "'v set set" where
  "wccs = cc_of ` V"

subsection \<open>Labels and Local Updates\<close>

text \<open>
  A label @{term "l v"} is the current representative candidate for vertex
  @{term v}.  The invariant \<open>labels_inv\<close> keeps every label inside the
  connected component of the vertex it labels.  Stability means that no edge can
  witness a strictly smaller neighbor label; by symmetry this later implies
  equal labels along every edge.

  A local update replaces @{term "l v"} by the minimum of its current label and
  the labels currently seen on its neighbors.
\<close>

definition labels_inv :: "'v labels \<Rightarrow> bool" where
  "labels_inv l \<longleftrightarrow> (\<forall>v \<in> V. l v \<in> cc_of v)"

definition labels_stable :: "'v labels \<Rightarrow> bool" where
  "labels_stable l \<longleftrightarrow> (\<forall>v \<in> V. \<forall>u \<in> V. (v, u) \<in> E \<longrightarrow> l v \<le> l u)"

definition neighbors :: "'v \<Rightarrow> 'v set" where
  "neighbors v = {u \<in> V. (v, u) \<in> E}"

definition min_neighbor_label :: "'v labels \<Rightarrow> 'v \<Rightarrow> 'v" where
  "min_neighbor_label l v = Min (insert (l v) (l ` neighbors v))"

definition update_label :: "'v labels \<Rightarrow> 'v \<Rightarrow> 'v labels" where
  "update_label l v = l(v := min_neighbor_label l v)"

subsection \<open>Termination Measure\<close>

text \<open>
  The algorithm only ever decreases labels.  To prove termination, labels are
  embedded into natural numbers by their rank in the finite ordered vertex set,
  and the global measure sums these ranks over all vertices.
\<close>

definition rank :: "'v \<Rightarrow> nat" where
  "rank x = card {y \<in> V. y < x}"

definition labels_measure :: "'v labels \<Rightarrow> nat" where
  "labels_measure l = (\<Sum>v \<in> V. rank (l v))"

subsection \<open>One Propagation Round\<close>

text \<open>
  One round visits every vertex once, in nondeterministic order.

  The round state @{term "(todo, l, changed)"} has the following meaning:
  @{term todo} is the set of vertices not yet visited in this round;
  @{term l} is the current label function; and @{term changed} records whether
  some visited vertex strictly decreased its label.  If no change has happened,
  all already visited vertices must already be locally stable with respect to
  the current labels.
\<close>

definition round_inv :: "'v labels \<Rightarrow> 'v set \<times> 'v labels \<times> bool \<Rightarrow> bool" where
  "round_inv l0 s \<longleftrightarrow> (case s of (todo, l, changed) \<Rightarrow>
     todo \<subseteq> V \<and> labels_inv l \<and> labels_measure l \<le> labels_measure l0 \<and>
     (changed \<longrightarrow> labels_measure l < labels_measure l0) \<and>
     (\<not> changed \<longrightarrow> (\<forall>v \<in> V - todo. min_neighbor_label l v = l v)))"

definition wcc_round :: "'v labels \<Rightarrow> ('v labels \<times> bool) nres" where
  "wcc_round l = do {
     (_, l', changed) \<leftarrow>
       WHILE\<^sub>T\<^bsup>round_inv l\<^esup>
         (\<lambda>(todo, l, changed). todo \<noteq> {})
         (\<lambda>(todo, l, changed). do {
            v \<leftarrow> SPEC (\<lambda>v. v \<in> todo);
            let m = min_neighbor_label l v;
            RETURN (todo - {v}, l(v := m), changed \<or> m < l v)
         })
         (V, l, False);
      RETURN (l', changed)
    }"

subsection \<open>Outer Fixed-Point Loop\<close>

text \<open>
  The outer loop repeats rounds until a whole round makes no strict label
  decrease.  Its state @{term "(l, changed)"} stores the current labels and the
  result of the previous round.  The initial @{term True} forces at least one
  round, which is needed even when the initial labels are already stable.
\<close>

definition init_labels :: "'v labels" where
  "init_labels v = v"

definition outer_inv :: "'v labels \<times> bool \<Rightarrow> bool" where
  "outer_inv s \<longleftrightarrow> (case s of (l, changed) \<Rightarrow>
     labels_inv l \<and> (\<not> changed \<longrightarrow> labels_stable l))"

definition wcc_labels :: "'v labels nres" where
  "wcc_labels = do {
     (l, _) \<leftarrow>
       WHILE\<^sub>T\<^bsup>outer_inv\<^esup>
         (\<lambda>(l, changed). changed)
         (\<lambda>(l, changed). wcc_round l)
         (init_labels, True);
      RETURN l
    }"

subsection \<open>Extracting Components\<close>

text \<open>
  Once labels are stable, each label class inside @{term V} is exactly one
  weakly connected component.  The final program first computes stable labels
  and then returns their label classes as the abstract component set.
\<close>

definition components_from_labels :: "'v labels \<Rightarrow> 'v set set" where
  "components_from_labels l = ((\<lambda>a. {v \<in> V. l v = a}) ` (l ` V))"

definition weak_components :: "'v set set nres" where
  "weak_components = do {
     l \<leftarrow> wcc_labels;
     RETURN (components_from_labels l)
   }"

subsection \<open>Basic Component Facts\<close>

lemma reachable_refl [simp]:
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
  from E_sym step.hyps have "(z, y) \<in> E"
    unfolding sym_def by blast
  then have "(z, y) \<in> E\<^sup>*"
    by simp
  also have "(y, u) \<in> E\<^sup>*"
    by (rule step.IH)
  finally show ?case .
qed

lemma cc_ofI:
  assumes "u \<in> V" and "reachable v u"
  shows "u \<in> cc_of v"
  using assms unfolding cc_of_def by simp

lemma cc_ofD:
  assumes "u \<in> cc_of v"
  shows "u \<in> V" "reachable v u"
  using assms unfolding cc_of_def by simp_all

lemma cc_of_self [simp]:
  assumes "v \<in> V"
  shows "v \<in> cc_of v"
  using assms by (rule cc_ofI) simp

lemma cc_of_nonempty:
  assumes "v \<in> V"
  shows "cc_of v \<noteq> {}"
  using assms cc_of_self by blast

lemma cc_of_subset_V:
  "cc_of v \<subseteq> V"
  unfolding cc_of_def by blast

lemma reachable_cc_of_eq:
  assumes "u \<in> V" and "v \<in> V" and "reachable u v"
  shows "cc_of u = cc_of v"
proof (intro set_eqI iffI)
  fix w
  assume "w \<in> cc_of u"
  then have "w \<in> V" and "reachable u w"
    by (auto dest: cc_ofD)
  moreover from assms(3) have "reachable v u"
    by (rule reachable_sym)
  ultimately have "reachable v w"
    by (meson reachable_trans)
  with \<open>w \<in> V\<close> show "w \<in> cc_of v"
    by (rule cc_ofI)
next
  fix w
  assume "w \<in> cc_of v"
  then have "w \<in> V" and "reachable v w"
    by (auto dest: cc_ofD)
  from assms(3) and \<open>reachable v w\<close> have "reachable u w"
    by (rule reachable_trans)
  with \<open>w \<in> V\<close> show "w \<in> cc_of u"
    by (rule cc_ofI)
qed

lemma cc_of_eq_if_member:
  assumes "u \<in> cc_of v"
  shows "cc_of u = cc_of v"
  using assms cc_ofD reachable_cc_of_eq reachable_sym
  by (metis finite_symmetric_graph.E_wf finite_symmetric_graph_axioms reachable_def trancl_subset_Sigma_aux)

lemma cc_of_disjoint_or_eq:
  assumes "u \<in> V" and "v \<in> V"
  shows "cc_of u \<inter> cc_of v = {} \<or> cc_of u = cc_of v"
proof (cases "cc_of u \<inter> cc_of v = {}")
  case False
  then obtain w where "w \<in> cc_of u" and "w \<in> cc_of v"
    by blast
  then have "cc_of u = cc_of w" and "cc_of w = cc_of v"
    using cc_of_eq_if_member by blast+
  then show ?thesis by blast
qed simp

lemma Union_wccs:
  "\<Union>wccs = V"
  unfolding wccs_def using cc_of_self cc_of_subset_V by blast

lemma wccs_finite:
  "finite wccs"
  unfolding wccs_def using finite_V by simp

subsection \<open>Label and Neighborhood Facts\<close>

lemma labels_invI:
  assumes "\<And>v. v \<in> V \<Longrightarrow> l v \<in> cc_of v"
  shows "labels_inv l"
  using assms unfolding labels_inv_def by simp

lemma labels_invD:
  assumes "labels_inv l" and "v \<in> V"
  shows "l v \<in> cc_of v"
  using assms unfolding labels_inv_def by simp

lemma labels_inv_in_V:
  assumes "labels_inv l" and "v \<in> V"
  shows "l v \<in> V"
  using labels_invD[OF assms] cc_ofD(1) by simp

lemma labels_inv_reachable:
  assumes "labels_inv l" and "v \<in> V"
  shows "reachable v (l v)"
  using labels_invD[OF assms] cc_ofD(2) by simp

lemma labels_stableD:
  assumes "labels_stable l" and "v \<in> V" and "u \<in> V" and "(v, u) \<in> E"
  shows "l v \<le> l u"
  using assms unfolding labels_stable_def by simp

lemma labels_stable_edge_eq:
  assumes "labels_stable l" and "(v, u) \<in> E"
  shows "l v = l u"
proof -
  from E_wf assms(2) have "v \<in> V" and "u \<in> V"
    by auto
  from assms have "l v \<le> l u"
    using \<open>v \<in> V\<close> \<open>u \<in> V\<close> labels_stableD by simp
  moreover from E_sym assms(2) have "(u, v) \<in> E"
    unfolding sym_def by auto
  then have "l u \<le> l v"
    using assms(1) \<open>u \<in> V\<close> \<open>v \<in> V\<close> labels_stableD by simp
  ultimately show ?thesis
    by simp
qed

lemma finite_neighbors [simp]:
  "finite (neighbors v)"
  unfolding neighbors_def using finite_V by simp

lemma neighbor_in_V:
  assumes "u \<in> neighbors v"
  shows "u \<in> V"
  using assms unfolding neighbors_def by simp

lemma neighbor_edge:
  assumes "u \<in> neighbors v"
  shows "(v, u) \<in> E"
  using assms unfolding neighbors_def by simp

lemma neighbor_in_cc_of:
  assumes "v \<in> V" and "u \<in> neighbors v"
  shows "u \<in> cc_of v"
proof (rule cc_ofI)
  show "u \<in> V"
    using assms(2) by (rule neighbor_in_V)
  show "reachable v u"
  proof -
    have "(v, u) \<in> E"
      using assms(2) by (rule neighbor_edge)
    then have "(v, u) \<in> E\<^sup>*"
      by (rule r_into_rtrancl)
    then show ?thesis
      unfolding reachable_def .
  qed
qed

lemma cc_of_neighbor_eq:
  assumes "v \<in> V" and "u \<in> neighbors v"
  shows "cc_of u = cc_of v"
  using neighbor_in_cc_of[OF assms] by (rule cc_of_eq_if_member)

lemma min_neighbor_label_candidate:
  "min_neighbor_label l v \<in> insert (l v) (l ` neighbors v)"
proof -
  have "finite (insert (l v) (l ` neighbors v))"
    by simp
  have "insert (l v) (l ` neighbors v) \<noteq> {}"
    by simp
  show ?thesis
    unfolding min_neighbor_label_def
    using \<open>finite (insert (l v) (l ` neighbors v))\<close>
      \<open>insert (l v) (l ` neighbors v) \<noteq> {}\<close>
    by (rule Min_in)
qed

lemma min_neighbor_label_le_self:
  "min_neighbor_label l v \<le> l v"
  unfolding min_neighbor_label_def by simp

lemma min_neighbor_label_in_cc_of:
  assumes "labels_inv l" and "v \<in> V"
  shows "min_neighbor_label l v \<in> cc_of v"
proof -
  let ?S = "insert (l v) (l ` neighbors v)"
  have "finite ?S"
    by simp
  have "?S \<noteq> {}"
    by simp
  have "?S \<subseteq> cc_of v"
  proof
    fix x
    assume "x \<in> ?S"
    then show "x \<in> cc_of v"
    proof
      assume "x = l v"
      then show ?thesis
        using assms by (simp add: labels_invD)
    next
      assume "x \<in> l ` neighbors v"
      then obtain u where "u \<in> neighbors v" and "x = l u"
        by auto
      then have "u \<in> V"
        by (simp add: neighbor_in_V)
      have "l u \<in> cc_of u"
        using assms(1) \<open>u \<in> V\<close> by (rule labels_invD)
      also have "cc_of u = cc_of v"
        using assms(2) \<open>u \<in> neighbors v\<close> by (rule cc_of_neighbor_eq)
      finally show ?thesis
        using \<open>x = l u\<close> by simp
    qed
  qed
  have "Min ?S \<in> ?S"
    using \<open>finite ?S\<close> \<open>?S \<noteq> {}\<close> by (rule Min_in)
  then show ?thesis
  proof -
    have "Min ?S \<in> cc_of v"
      using \<open>?S \<subseteq> cc_of v\<close> \<open>Min ?S \<in> ?S\<close> by (rule subsetD)
    then show ?thesis
      unfolding min_neighbor_label_def by simp
  qed
qed

lemma update_label_preserves_labels_inv:
  assumes "labels_inv l" and "v \<in> V"
  shows "labels_inv (update_label l v)"
proof (rule labels_invI)
  fix u
  assume "u \<in> V"
  show "update_label l v u \<in> cc_of u"
  proof (cases "u = v")
    case True
    then show ?thesis
      using assms min_neighbor_label_in_cc_of unfolding update_label_def by simp
  next
    case False
    then show ?thesis
      using assms(1) \<open>u \<in> V\<close> labels_invD unfolding update_label_def by simp
  qed
qed

subsection \<open>Round Invariant Setup\<close>

lemma round_inv_initial:
  assumes "labels_inv l"
  shows "round_inv l (V, l, False)"
  using assms unfolding round_inv_def by simp

lemma round_inv_labels_invD:
  assumes "round_inv l0 (todo, l, changed)"
  shows "labels_inv l"
  using assms unfolding round_inv_def by simp

lemma round_inv_todo_subsetD:
  assumes "round_inv l0 (todo, l, changed)"
  shows "todo \<subseteq> V"
  using assms unfolding round_inv_def by simp

lemma round_inv_measure_leD:
  assumes "round_inv l0 (todo, l, changed)"
  shows "labels_measure l \<le> labels_measure l0"
  using assms unfolding round_inv_def by simp

lemma round_inv_changed_measure_lessD:
  assumes "round_inv l0 (todo, l, True)"
  shows "labels_measure l < labels_measure l0"
  using assms unfolding round_inv_def by simp

lemma init_labels_inv:
  "labels_inv init_labels"
proof (rule labels_invI)
  fix v
  assume "v \<in> V"
  then show "init_labels v \<in> cc_of v"
    unfolding init_labels_def by simp
qed

lemma outer_inv_initial:
  "outer_inv (init_labels, True)"
  using init_labels_inv unfolding outer_inv_def by simp

lemma outer_inv_labels_invD:
  assumes "outer_inv (l, changed)"
  shows "labels_inv l"
  using assms unfolding outer_inv_def by simp

lemma outer_inv_stableD:
  assumes "outer_inv (l, False)"
  shows "labels_stable l"
  using assms unfolding outer_inv_def by simp

subsection \<open>Measure Facts\<close>

lemma finite_rank_set [simp]:
  "finite {y \<in> V. y < x}"
  using finite_V by simp

lemma rank_strict_mono:
  assumes "x \<in> V" and "y \<in> V" and "x < y"
  shows "rank x < rank y"
proof -
  let ?X = "{z \<in> V. z < x}"
  let ?Y = "{z \<in> V. z < y}"
  have "?X \<subseteq> ?Y"
    using assms(3) by auto
  have "x \<in> ?Y"
    using assms by simp
  have "x \<notin> ?X"
    by simp
  then have "?X \<noteq> ?Y"
    using \<open>x \<in> ?Y\<close> by auto
  then have "?X \<subset> ?Y"
    using \<open>?X \<subseteq> ?Y\<close> by simp
  have "finite ?Y"
    using finite_V by simp
  then have "card ?X < card ?Y"
    using \<open>?X \<subset> ?Y\<close> by (rule psubset_card_mono)
  then show ?thesis
    unfolding rank_def .
qed

lemma labels_measure_update_decreases:
  assumes "labels_inv l" and "v \<in> V" and "min_neighbor_label l v < l v"
  shows "labels_measure (l(v := min_neighbor_label l v)) < labels_measure l"
proof -
  have "min_neighbor_label l v \<in> V"
    using min_neighbor_label_in_cc_of[OF assms(1,2)] cc_ofD(1) by simp
  have "l v \<in> V"
    using assms(1,2) by (rule labels_inv_in_V)
  have "rank (min_neighbor_label l v) < rank (l v)"
    using \<open>min_neighbor_label l v \<in> V\<close> \<open>l v \<in> V\<close> assms(3)
    by (rule rank_strict_mono)
  have "labels_measure (l(v := min_neighbor_label l v)) =
      (\<Sum>u \<in> V - {v}. rank (l u)) + rank (min_neighbor_label l v)"
    unfolding labels_measure_def using finite_V assms(2) by (simp add: sum.remove)
  also have "... < (\<Sum>u \<in> V - {v}. rank (l u)) + rank (l v)"
    using \<open>rank (min_neighbor_label l v) < rank (l v)\<close> by simp
  also have "... = labels_measure l"
    unfolding labels_measure_def using finite_V assms(2) by (simp add: sum.remove)
  finally show ?thesis .
qed

lemma rank_min_neighbor_label_le_self:
  assumes "labels_inv l" and "v \<in> V"
  shows "rank (min_neighbor_label l v) \<le> rank (l v)"
proof (cases "min_neighbor_label l v = l v")
  case True
  then show ?thesis by simp
next
  case False
  have "min_neighbor_label l v \<le> l v"
    by (rule min_neighbor_label_le_self)
  with False have "min_neighbor_label l v < l v"
    by simp
  have "min_neighbor_label l v \<in> V"
    using min_neighbor_label_in_cc_of[OF assms] cc_ofD(1) by simp
  have "l v \<in> V"
    using assms by (rule labels_inv_in_V)
  show ?thesis
    using rank_strict_mono[OF \<open>min_neighbor_label l v \<in> V\<close> \<open>l v \<in> V\<close> \<open>min_neighbor_label l v < l v\<close>]
    by simp
qed

lemma labels_measure_update_le:
  assumes "labels_inv l" and "v \<in> V"
  shows "labels_measure (l(v := min_neighbor_label l v)) \<le> labels_measure l"
proof -
  have "labels_measure (l(v := min_neighbor_label l v)) =
      (\<Sum>u \<in> V - {v}. rank (l u)) + rank (min_neighbor_label l v)"
    unfolding labels_measure_def using finite_V assms(2) by (simp add: sum.remove)
  also have "... \<le> (\<Sum>u \<in> V - {v}. rank (l u)) + rank (l v)"
    using rank_min_neighbor_label_le_self[OF assms] by simp
  also have "... = labels_measure l"
    unfolding labels_measure_def using finite_V assms(2) by (simp add: sum.remove)
  finally show ?thesis .
qed

lemma round_step_measure_le:
  assumes "round_inv l0 (todo, l, changed)" and "v \<in> todo"
  shows "labels_measure (l(v := min_neighbor_label l v)) \<le> labels_measure l"
proof -
  have "todo \<subseteq> V"
    using assms(1) by (rule round_inv_todo_subsetD)
  then have "v \<in> V"
    using assms(2) by auto
  have "labels_inv l"
    using assms(1) by (rule round_inv_labels_invD)
  show ?thesis
    using labels_measure_update_le[OF \<open>labels_inv l\<close> \<open>v \<in> V\<close>] .
qed

lemma round_step_measure_decreases_if_changed:
  assumes "round_inv l0 (todo, l, changed)" and "v \<in> todo"
    and "min_neighbor_label l v < l v"
  shows "labels_measure (l(v := min_neighbor_label l v)) < labels_measure l"
proof -
  have "todo \<subseteq> V"
    using assms(1) by (rule round_inv_todo_subsetD)
  then have "v \<in> V"
    using assms(2) by auto
  have "labels_inv l"
    using assms(1) by (rule round_inv_labels_invD)
  show ?thesis
    using labels_measure_update_decreases[OF \<open>labels_inv l\<close> \<open>v \<in> V\<close> assms(3)] .
qed

subsection \<open>Round Correctness\<close>

lemma round_step_preserves_round_inv:
  assumes "round_inv l0 (todo, l, changed)" and "v \<in> todo"
  shows "round_inv l0 (todo - {v}, l(v := min_neighbor_label l v),
    changed \<or> min_neighbor_label l v < l v)"
proof -
  have "todo \<subseteq> V"
    using assms(1) by (rule round_inv_todo_subsetD)
  then have "v \<in> V"
    using assms(2) by auto
  have "labels_inv l"
    using assms(1) by (rule round_inv_labels_invD)
  have "l(v := min_neighbor_label l v) = update_label l v"
    unfolding update_label_def by simp
  then have "labels_inv (l(v := min_neighbor_label l v))"
    using update_label_preserves_labels_inv[OF \<open>labels_inv l\<close> \<open>v \<in> V\<close>] by simp
  have "todo - {v} \<subseteq> V"
    using \<open>todo \<subseteq> V\<close> by auto
  have "labels_measure (l(v := min_neighbor_label l v)) \<le> labels_measure l0"
    using labels_measure_update_le[OF \<open>labels_inv l\<close> \<open>v \<in> V\<close>]
      round_inv_measure_leD[OF assms(1)] by linarith
  have "changed \<or> min_neighbor_label l v < l v \<Longrightarrow>
      labels_measure (l(v := min_neighbor_label l v)) < labels_measure l0"
  proof -
    assume "changed \<or> min_neighbor_label l v < l v"
    then show "labels_measure (l(v := min_neighbor_label l v)) < labels_measure l0"
    proof
      assume "changed"
      then have "labels_measure l < labels_measure l0"
        using assms(1) unfolding round_inv_def by simp
      moreover have "labels_measure (l(v := min_neighbor_label l v)) \<le> labels_measure l"
        using labels_measure_update_le[OF \<open>labels_inv l\<close> \<open>v \<in> V\<close>] .
      ultimately show ?thesis by linarith
    next
      assume "min_neighbor_label l v < l v"
      then have "labels_measure (l(v := min_neighbor_label l v)) < labels_measure l"
        using labels_measure_update_decreases[OF \<open>labels_inv l\<close> \<open>v \<in> V\<close>] by simp
      moreover have "labels_measure l \<le> labels_measure l0"
        using assms(1) by (rule round_inv_measure_leD)
      ultimately show ?thesis by linarith
    qed
  qed
  have "\<not> (changed \<or> min_neighbor_label l v < l v) \<Longrightarrow>
      (\<forall>u \<in> V - (todo - {v}).
        min_neighbor_label (l(v := min_neighbor_label l v)) u = (l(v := min_neighbor_label l v)) u)"
  proof -
    assume no_change: "\<not> (changed \<or> min_neighbor_label l v < l v)"
    then have not_changed: "\<not> changed"
      by simp
    have "min_neighbor_label l v \<le> l v"
      by (rule min_neighbor_label_le_self)
    moreover from no_change have "\<not> min_neighbor_label l v < l v"
      by simp
    then have "l v \<le> min_neighbor_label l v"
      by simp
    ultimately have m_eq: "min_neighbor_label l v = l v"
      by (rule order_antisym)
    have upd_id: "l(v := min_neighbor_label l v) = l"
      using m_eq by simp
    have old_processed: "\<forall>u \<in> V - todo. min_neighbor_label l u = l u"
      using assms(1) not_changed unfolding round_inv_def by simp
    have "\<forall>u \<in> V - (todo - {v}). min_neighbor_label l u = l u"
    proof
      fix u
      assume "u \<in> V - (todo - {v})"
      then have "u = v \<or> u \<in> V - todo"
        by auto
      then show "min_neighbor_label l u = l u"
      proof
        assume "u = v"
        then show ?thesis using m_eq by simp
      next
        assume "u \<in> V - todo"
        then show ?thesis using old_processed by simp
      qed
    qed
    have "\<forall>u \<in> V - (todo - {v}).
        min_neighbor_label (l(v := min_neighbor_label l v)) u = (l(v := min_neighbor_label l v)) u"
      using \<open>\<forall>u \<in> V - (todo - {v}). min_neighbor_label l u = l u\<close> upd_id by simp
    then show ?thesis .
  qed
  show ?thesis
    using \<open>todo - {v} \<subseteq> V\<close> \<open>labels_inv (l(v := min_neighbor_label l v))\<close>
      \<open>labels_measure (l(v := min_neighbor_label l v)) \<le> labels_measure l0\<close>
      \<open>changed \<or> min_neighbor_label l v < l v \<Longrightarrow>
        labels_measure (l(v := min_neighbor_label l v)) < labels_measure l0\<close>
      \<open>\<not> (changed \<or> min_neighbor_label l v < l v) \<Longrightarrow>
        (\<forall>u \<in> V - (todo - {v}).
          min_neighbor_label (l(v := min_neighbor_label l v)) u = (l(v := min_neighbor_label l v)) u)\<close>
    unfolding round_inv_def by simp
qed

lemma min_neighbor_label_all_eq_imp_stable:
  assumes "\<And>v. v \<in> V \<Longrightarrow> min_neighbor_label l v = l v"
  shows "labels_stable l"
proof (unfold labels_stable_def, intro ballI impI)
  fix v u
  assume "v \<in> V" and "u \<in> V" and "(v, u) \<in> E"
  then have "u \<in> neighbors v"
    unfolding neighbors_def by simp
  then have "l u \<in> insert (l v) (l ` neighbors v)"
    by simp
  have "min_neighbor_label l v \<le> l u"
  proof -
    have "finite (insert (l v) (l ` neighbors v))"
      by simp
    then have "Min (insert (l v) (l ` neighbors v)) \<le> l u"
      using \<open>l u \<in> insert (l v) (l ` neighbors v)\<close> by (rule Min_le)
    then show ?thesis
      unfolding min_neighbor_label_def .
  qed
  then show "l v \<le> l u"
    using assms[OF \<open>v \<in> V\<close>] by simp
qed

lemma round_inv_no_change_stable:
  assumes "round_inv l0 ({}, l, False)"
  shows "labels_stable l"
proof (rule min_neighbor_label_all_eq_imp_stable)
  fix v
  assume "v \<in> V"
  show "min_neighbor_label l v = l v"
    using assms \<open>v \<in> V\<close> unfolding round_inv_def by simp
qed

lemma wcc_round_correct:
  assumes "labels_inv l"
  shows "wcc_round l \<le> SPEC (\<lambda>(l', changed). labels_inv l' \<and> labels_measure l' \<le> labels_measure l \<and>
    (changed \<longrightarrow> labels_measure l' < labels_measure l) \<and>
    (\<not> changed \<longrightarrow> labels_stable l'))"
  unfolding wcc_round_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(todo, l, changed). card todo)"])
  subgoal by simp
  subgoal using assms by (rule round_inv_initial)
  subgoal for s a b aa ba x
  proof -
    assume inv: "round_inv l s"
      and s_eq: "s = (a, b)"
      and b_eq: "b = (aa, ba)"
      and x: "x \<in> a"
    have "s = (a, aa, ba)"
      using s_eq b_eq by simp
    then have "round_inv l (a, aa, ba)"
      using inv by simp
    then show "round_inv l (a - {x}, aa(x := min_neighbor_label aa x),
      ba \<or> min_neighbor_label aa x < aa x)"
      using x by (rule round_step_preserves_round_inv)
  qed
  subgoal for s a b aa ba x
  proof -
    assume inv: "round_inv l s"
      and s_eq: "s = (a, b)"
      and b_eq: "b = (aa, ba)"
      and x: "x \<in> a"
    have s_trip: "s = (a, aa, ba)"
      using s_eq b_eq by simp
    then have inv_trip: "round_inv l (a, aa, ba)"
      using inv by simp
    have "a \<subseteq> V"
      using inv_trip by (rule round_inv_todo_subsetD)
    then have "finite a"
      using finite_V finite_subset by blast
    have "a \<noteq> {}"
      using x by blast
    have "0 < card a"
      using \<open>finite a\<close> \<open>a \<noteq> {}\<close> by (simp add: card_gt_0_iff)
    show "((a - {x}, aa(x := min_neighbor_label aa x),
      ba \<or> min_neighbor_label aa x < aa x), s) \<in>
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
    by (cases s) (simp add: round_inv_no_change_stable)
  done

lemma wcc_round_preserves_labels_inv:
  assumes "labels_inv l"
  shows "wcc_round l \<le> SPEC (\<lambda>(l', changed). labels_inv l')"
  using wcc_round_correct[OF assms]
  by (rule order_trans) (auto intro: SPEC_rule)

subsection \<open>Outer Loop Correctness\<close>

lemma wcc_labels_correct:
  "wcc_labels \<le> SPEC (\<lambda>l. labels_inv l \<and> labels_stable l)"
  unfolding wcc_labels_def
  apply (refine_vcg WHILEIT_rule[where R=
        "measure (\<lambda>(l, changed). labels_measure l + (if changed then 1 else 0))"])
  subgoal by simp
  subgoal by (rule outer_inv_initial)
  subgoal for s l changed
    apply (rule order_trans[OF wcc_round_correct])
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

subsection \<open>Components Induced by Stable Labels\<close>

lemma labels_stable_reachable_eq:
  assumes "labels_stable l" and "reachable u v"
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

lemma label_class_eq_cc_of:
  assumes "labels_inv l" and "labels_stable l" and "x \<in> V"
  shows "{v \<in> V. l v = l x} = cc_of x"
proof (intro set_eqI iffI)
  fix v
  assume "v \<in> {v \<in> V. l v = l x}"
  then have "v \<in> V" and eq: "l v = l x"
    by simp_all
  have lv_v: "l v \<in> cc_of v"
    using assms(1) \<open>v \<in> V\<close> by (rule labels_invD)
  have lx_x: "l x \<in> cc_of x"
    using assms(1) assms(3) by (rule labels_invD)
  have "cc_of v = cc_of (l v)"
    using cc_of_eq_if_member[OF lv_v] by simp
  also have "... = cc_of (l x)"
    using eq by simp
  also have "... = cc_of x"
    using cc_of_eq_if_member[OF lx_x] by simp
  finally have "cc_of v = cc_of x" .
  moreover have "v \<in> cc_of v"
    using \<open>v \<in> V\<close> by simp
  ultimately show "v \<in> cc_of x"
    by simp
next
  fix v
  assume "v \<in> cc_of x"
  then have "v \<in> V" and "reachable x v"
    by (auto dest: cc_ofD)
  have "l x = l v"
    using assms(2) \<open>reachable x v\<close> by (rule labels_stable_reachable_eq)
  then show "v \<in> {v \<in> V. l v = l x}"
    using \<open>v \<in> V\<close> by simp
qed

lemma components_from_labels_correct:
  assumes "labels_inv l" and "labels_stable l"
  shows "components_from_labels l = wccs"
proof (intro set_eqI iffI)
  fix C
  assume "C \<in> components_from_labels l"
  then obtain x where "x \<in> V" and C: "C = {v \<in> V. l v = l x}"
    unfolding components_from_labels_def by auto
  then have "C = cc_of x"
    using label_class_eq_cc_of[OF assms \<open>x \<in> V\<close>] by simp
  then show "C \<in> wccs"
    unfolding wccs_def using \<open>x \<in> V\<close> by simp
next
  fix C
  assume "C \<in> wccs"
  then obtain x where "x \<in> V" and C: "C = cc_of x"
    unfolding wccs_def by auto
  have "C = {v \<in> V. l v = l x}"
    using C label_class_eq_cc_of[OF assms \<open>x \<in> V\<close>] by simp
  then show "C \<in> components_from_labels l"
    unfolding components_from_labels_def using \<open>x \<in> V\<close> by auto
qed

theorem weak_components_correct:
  "weak_components \<le> SPEC (\<lambda>Cs. Cs = wccs)"
  unfolding weak_components_def
  apply (rule bind_rule)
  apply (rule order_trans[OF wcc_labels_correct])
  apply (rule SPEC_rule)
  subgoal for l
    using components_from_labels_correct[of l] by auto
  done

end

end
