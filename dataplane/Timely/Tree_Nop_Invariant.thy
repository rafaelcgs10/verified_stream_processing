theory Tree_Nop_Invariant

imports
  Dataflow_Opt_Op
  Builder_Op
begin

section ‹A Generic Nop Invariant for Compiled Dataflow Trees›

text ‹This theory discharges the @{const nop_invariant} hypothesis of
@{thm [source] compile_dataflow_opt_wbisim} once and for all for every
dataflow tree whose leaves are well-behaved, in the sense of the
type-erased leaf invariant @{term nop_leaf} below. All operators built
with @{const builder_op} and a frontier-stable logic satisfy it.›

subsection ‹The leaf invariant›

text ‹@{term "nop_leaf k q"} states that the leaf operator @{term q}
answers empty progress writes with a self-loop, answers a re-read of the
frontier it currently knows (@{term k}, if any) with a self-loop, only
emits @{const Inr}-shaped data values, and that all of this is preserved
by every step. A frontier read updates the known frontier.›

coinductive nop_leaf :: "('p ⇒ 't antichain) option ⇒
  ('p option, 'p option, (('p, 't, 'm) shared_state_scheme + ('p ⇒ 't antichain)) + 'dd × 't) op ⇒ bool" where
  nop_leafI: "⟦
     ⋀st op'. ¬ has_progress st ⟹ step (Out None (Inl (Inl st))) q op' ⟹ op' = q;
     ⋀F op'. k = Some F ⟹ step (Inp None (Inl (Inr F))) q op' ⟹ op' = q;
     ⋀op'. step Tau q op' ⟹ nop_leaf k op';
     ⋀p v op'. step (Inp (Some p) (Inr v)) q op' ⟹ nop_leaf k op';
     ⋀p v op'. step (Out (Some p) v) q op' ⟹ is_Inr v ∧ nop_leaf k op';
     ⋀st op'. step (Out None (Inl (Inl st))) q op' ⟹ nop_leaf k op';
     ⋀F op'. step (Inp None (Inl (Inr F))) q op' ⟹ nop_leaf (Some F) op'
   ⟧ ⟹ nop_leaf k q"

lemma nop_leafD_progress_selfloop:
  "nop_leaf k q ⟹ ¬ has_progress st ⟹ step (Out None (Inl (Inl st))) q op' ⟹ op' = q"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_frontier_selfloop:
  "nop_leaf (Some F) q ⟹ step (Inp None (Inl (Inr F))) q op' ⟹ op' = q"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_Tau:
  "nop_leaf k q ⟹ step Tau q op' ⟹ nop_leaf k op'"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_data_in:
  "nop_leaf k q ⟹ step (Inp (Some p) (Inr v)) q op' ⟹ nop_leaf k op'"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_data_out:
  "nop_leaf k q ⟹ step (Out (Some p) v) q op' ⟹ is_Inr v ∧ nop_leaf k op'"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_progress:
  "nop_leaf k q ⟹ step (Out None (Inl (Inl st))) q op' ⟹ nop_leaf k op'"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_frontier:
  "nop_leaf k q ⟹ step (Inp None (Inl (Inr F))) q op' ⟹ nop_leaf (Some F) op'"
  by (erule nop_leaf.cases) blast

subsection ‹Builder operators satisfy the leaf invariant›

definition logic_frontier_stable where
  "logic_frontier_stable logic ⟷
     (∀ os os'. os' |∈| logic os ⟶ front os' = front os ∧ initia os' = initia os)"

lemma front_initia_produces[simp]:
  "front (produces os b) = front os"
  "initia (produces os b) = initia os"
  unfolding produces_def by simp_all

lemma front_initia_drop_caps[simp]:
  "front (drop_caps os caps) = front os"
  "initia (drop_caps os caps) = initia os"
  unfolding drop_caps_def by simp_all

lemma front_initia_add_caps[simp]:
  "front (add_caps os caps) = front os"
  "initia (add_caps os caps) = initia os"
  unfolding add_caps_def by simp_all

lemma front_initia_consumes[simp]:
  "front (consumes os p t d) = front os"
  "initia (consumes os p t d) = initia os"
  unfolding consumes_def by simp_all

lemma front_initia_obtain_progress[simp]:
  "front (fst (obtain_progress os)) = front os"
  "initia (fst (obtain_progress os)) = initia os"
  unfolding obtain_progress_def by simp_all

lemma nop_leaf_builder_op:
  assumes stable: "logic_frontier_stable logic"
    and "k = None ∨ (∃ F. k = Some F ∧ front os = F ∧ initia os)"
  shows "nop_leaf k (builder_op fb tps sps os logic)"
  using assms(2)
proof (coinduction arbitrary: k os)
  case (nop_leaf k os)
  note prem = nop_leaf
  note stable' = stable[unfolded logic_frontier_stable_def, rule_format]
  show ?case
    apply (rule exI[of _ "builder_op fb tps sps os logic"])
    apply (rule exI[of _ k])
    apply (intro conjI)
    subgoal by (rule refl)
    subgoal by (rule refl)
    subgoal
      by (intro allI impI, erule step_builder_op_elim)
         (auto dest: obtain_progress_no_progressD[OF sym])
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply (auto simp add: operator_state_front_initia_upd_triv)
      done
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply (auto simp flip: cin.rep_eq)
      apply (frule stable')
      apply auto
      done
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply auto
      done
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply auto
      done
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply auto
      apply (metis front_initia_obtain_progress(1) front_initia_obtain_progress(2) fst_conv)
      done
    subgoal
      by (intro allI impI, erule step_builder_op_elim) auto
    done
qed

subsection ‹The compiled-tree invariant›

abbreviation node_wrap where
  "node_wrap n ≡ case_option (Inl n) (λ p. Inr (n, p))"

inductive good :: "('id ⇒ bool) ⇒ ('id ⇒ 'p ⇒ 't antichain) ⇒ 'id set ⇒
  ('id + 'id × 'p, 'id + 'id × 'p, (('p, 't, 'm) shared_state_scheme + ('p ⇒ 't antichain)) + 'dd × 't) op ⇒ bool"
  for ok :: "'id ⇒ bool" and F :: "'id ⇒ 'p ⇒ 't antichain" where
  good_Leaf: "⟦ nop_leaf k q; ¬ ok n ⟶ k = Some (F n) ⟧ ⟹
     good ok F {n} (map_op (node_wrap n) (node_wrap n) q)"
| good_Comp: "⟦ good ok F N1 op1; good ok F N2 op2; N1 ∩ N2 = {};
     ∀ nid. wire (Inl nid) = None;
     ∀ p q'. wire p = Some q' ⟶ is_Inr q';
     ∀ q' v. v ∈ set (buf q') ⟶ is_Inr v ⟧ ⟹
     good ok F (N1 ∪ N2) (map_op (case_sum id id) (case_sum id id) (comp_op wire buf op1 op2))"
| good_Loop: "⟦ good ok F N op;
     ∀ nid. wire (Inl nid) = None;
     ∀ p q'. wire p = Some q' ⟶ is_Inr q';
     ∀ q' v. v ∈ set (buf q') ⟶ is_Inr v ⟧ ⟹
     good ok F N (loop_op wire buf op)"

lemma good_mono:
  assumes "good ok F N op"
    and "⋀ m. m ∈ N ⟹ ¬ ok' m ⟹ ¬ ok m ∧ F' m = F m"
  shows "good ok' F' N op"
  using assms
  by (induct rule: good.induct) (auto intro: good.intros)

subsection ‹Self-loops of stale choices›

lemma good_progress_selfloop:
  assumes g: "good ok F N op" and np: "¬ has_progress st"
    and s: "step (Out (Inl nid) (Inl (Inl st))) op op'"
  shows "op' = op"
  using g s
proof (induct arbitrary: op' rule: good.induct)
  case (good_Leaf k q n)
  obtain io' q'' where *: "step io' q q''"
    "map_IO (node_wrap n) (node_wrap n) id io' = Out (Inl nid) (Inl (Inl st))"
    "map_op (node_wrap n) (node_wrap n) q'' = op'"
    using step_map_op_elim[OF good_Leaf(3)] by metis
  have io': "io' = Out None (Inl (Inl st))"
    using *(2) by (cases io') (auto split: option.splits)
  have q'': "q'' = q"
    by (rule nop_leafD_progress_selfloop[OF good_Leaf(1) np *(1)[unfolded io']])
  show ?case
    using *(3) unfolding q'' by simp
next
  case (good_Comp N1 op1 N2 op2 wire buf)
  obtain io' c'' where *: "step io' (comp_op wire buf op1 op2) c''"
    "map_IO (case_sum id id) (case_sum id id) id io' = Out (Inl nid) (Inl (Inl st))"
    "map_op (case_sum id id) (case_sum id id) c'' = op'"
    using step_map_op_elim[OF good_Comp.prems] by metis
  have cases: "io' = Out (Inl (Inl nid)) (Inl (Inl st)) ∨ io' = Out (Inr (Inl nid)) (Inl (Inl st))"
    using *(2) by (cases io') (auto split: sum.splits)
  show ?case
    using cases
  proof (elim disjE)
    assume A: "io' = Out (Inl (Inl nid)) (Inl (Inl st))"
    from *(1)[unfolded A] obtain op1' where s1: "step (Out (Inl nid) (Inl (Inl st))) op1 op1'"
      and c'': "c'' = comp_op wire buf op1' op2"
      by (cases rule: step_comp_op_elim) auto
    have "op1' = op1" by (rule good_Comp.hyps(2)[OF s1])
    then show ?case using *(3) c'' by auto
  next
    assume A: "io' = Out (Inr (Inl nid)) (Inl (Inl st))"
    from *(1)[unfolded A] obtain op2' where s2: "step (Out (Inl nid) (Inl (Inl st))) op2 op2'"
      and c'': "c'' = comp_op wire buf op1 op2'"
      by (cases rule: step_comp_op_elim) auto
    have "op2' = op2" by (rule good_Comp.hyps(4)[OF s2])
    then show ?case using *(3) c'' by auto
  qed
next
  case (good_Loop N op wire buf)
  from good_Loop.prems obtain op0' where s0: "step (Out (Inl nid) (Inl (Inl st))) op op0'"
    and o': "op' = loop_op wire buf op0'"
    by (cases rule: step_loop_op_elim) auto
  have "op0' = op" by (rule good_Loop.hyps(2)[OF s0])
  then show ?case using o' by simp
qed

lemma good_frontier_selfloop:
  assumes g: "good ok F N op" and no: "¬ ok nid"
    and s: "step (Inp (Inl nid) (Inl (Inr (F nid)))) op op'"
  shows "op' = op"
  using g s
proof (induct arbitrary: op' rule: good.induct)
  case (good_Leaf k q n)
  obtain io' q'' where *: "step io' q q''"
    "map_IO (node_wrap n) (node_wrap n) id io' = Inp (Inl nid) (Inl (Inr (F nid)))"
    "map_op (node_wrap n) (node_wrap n) q'' = op'"
    using step_map_op_elim[OF good_Leaf(3)] by metis
  have io': "io' = Inp None (Inl (Inr (F nid)))" and n: "n = nid"
    using *(2) by (cases io'; force split: option.splits)+
  have k: "k = Some (F n)"
    using good_Leaf(2) no n by blast
  have q'': "q'' = q"
    using nop_leafD_frontier_selfloop[OF good_Leaf(1)[unfolded k]] *(1)[unfolded io'] n by blast
  show ?case
    using *(3) unfolding q'' by simp
next
  case (good_Comp N1 op1 N2 op2 wire buf)
  obtain io' c'' where *: "step io' (comp_op wire buf op1 op2) c''"
    "map_IO (case_sum id id) (case_sum id id) id io' = Inp (Inl nid) (Inl (Inr (F nid)))"
    "map_op (case_sum id id) (case_sum id id) c'' = op'"
    using step_map_op_elim[OF good_Comp.prems] by metis
  have cases: "io' = Inp (Inl (Inl nid)) (Inl (Inr (F nid))) ∨ io' = Inp (Inr (Inl nid)) (Inl (Inr (F nid)))"
    using *(2) by (cases io') (auto split: sum.splits)
  show ?case
    using cases
  proof (elim disjE)
    assume A: "io' = Inp (Inl (Inl nid)) (Inl (Inr (F nid)))"
    from *(1)[unfolded A] obtain op1' where s1: "step (Inp (Inl nid) (Inl (Inr (F nid)))) op1 op1'"
      and c'': "c'' = comp_op wire buf op1' op2"
      by (cases rule: step_comp_op_elim) auto
    have "op1' = op1" by (rule good_Comp.hyps(2)[OF s1])
    then show ?case using *(3) c'' by auto
  next
    assume A: "io' = Inp (Inr (Inl nid)) (Inl (Inr (F nid)))"
    from *(1)[unfolded A] obtain op2' where s2: "step (Inp (Inl nid) (Inl (Inr (F nid)))) op2 op2'"
      and c'': "c'' = comp_op wire buf op1 op2'"
      by (cases rule: step_comp_op_elim) auto
    have "op2' = op2" by (rule good_Comp.hyps(4)[OF s2])
    then show ?case using *(3) c'' by auto
  qed
next
  case (good_Loop N op wire buf)
  from good_Loop.prems obtain op0' where s0: "step (Inp (Inl nid) (Inl (Inr (F nid)))) op op0'"
    and o': "op' = loop_op wire buf op0'"
    by (cases rule: step_loop_op_elim) auto
  have "op0' = op" by (rule good_Loop.hyps(2)[OF s0])
  then show ?case using o' by simp
qed

subsection ‹Closure under steps›

lemma good_step_data_in:
  assumes "good ok F N op" and "step (Inp (Inr (nid, p)) (Inr x)) op op'"
  shows "good ok F N op'"
  using assms
proof (induct arbitrary: op' rule: good.induct)
  case (good_Leaf k q n)
  obtain io' q'' where *: "step io' q q''"
    "map_IO (node_wrap n) (node_wrap n) id io' = Inp (Inr (nid, p)) (Inr x)"
    "map_op (node_wrap n) (node_wrap n) q'' = op'"
    using step_map_op_elim[OF good_Leaf(3)] by metis
  have io': "io' = Inp (Some p) (Inr x)"
    using *(2) by (cases io') (auto split: option.splits)
  have leaf': "nop_leaf k q''"
    by (rule nop_leafD_data_in[OF good_Leaf(1) *(1)[unfolded io']])
  have g': "good ok F {n} (map_op (node_wrap n) (node_wrap n) q'')"
    using good.intros(1)[where k = k and ok = ok and F = F, OF leaf'] good_Leaf(2) by blast
  show ?case
    using g' *(3) by simp
next
  case (good_Comp N1 op1 N2 op2 wire buf)
  obtain io' c'' where *: "step io' (comp_op wire buf op1 op2) c''"
    "map_IO (case_sum id id) (case_sum id id) id io' = Inp (Inr (nid, p)) (Inr x)"
    "map_op (case_sum id id) (case_sum id id) c'' = op'"
    using step_map_op_elim[OF good_Comp.prems] by metis
  have cases: "io' = Inp (Inl (Inr (nid, p))) (Inr x) ∨ io' = Inp (Inr (Inr (nid, p))) (Inr x)"
    using *(2) by (cases io') (auto split: sum.splits)
  show ?case
    using cases
  proof (elim disjE)
    assume A: "io' = Inp (Inl (Inr (nid, p))) (Inr x)"
    from *(1)[unfolded A] obtain op1' where s1: "step (Inp (Inr (nid, p)) (Inr x)) op1 op1'"
      and c'': "c'' = comp_op wire buf op1' op2"
      by (cases rule: step_comp_op_elim) auto
    have g1: "good ok F N1 op1'"
      by (rule good_Comp.hyps(2)[OF s1])
    show ?case
      using good.intros(2)[OF g1 good_Comp.hyps(3) good_Comp.hyps(5) good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)]
        *(3) c'' by simp
  next
    assume A: "io' = Inp (Inr (Inr (nid, p))) (Inr x)"
    from *(1)[unfolded A] obtain op2' where s2: "step (Inp (Inr (nid, p)) (Inr x)) op2 op2'"
      and c'': "c'' = comp_op wire buf op1 op2'"
      by (cases rule: step_comp_op_elim) auto
    have g2: "good ok F N2 op2'"
      by (rule good_Comp.hyps(4)[OF s2])
    show ?case
      using good.intros(2)[OF good_Comp.hyps(1) g2 good_Comp.hyps(5) good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)]
        *(3) c'' by simp
  qed
next
  case (good_Loop N op wire buf)
  from good_Loop.prems obtain op0' where s0: "step (Inp (Inr (nid, p)) (Inr x)) op op0'"
    and o': "op' = loop_op wire buf op0'"
    by (cases rule: step_loop_op_elim) auto
  have g0: "good ok F N op0'"
    by (rule good_Loop.hyps(2)[OF s0])
  show ?case
    unfolding o'
    by (rule good.intros(3)[OF g0 good_Loop.hyps(3) good_Loop.hyps(4) good_Loop.hyps(5)])
qed

lemma good_step_data_out:
  assumes "good ok F N op" and "step (Out (Inr (nid, p)) v) op op'"
  shows "is_Inr v ∧ good ok F N op'"
  using assms
proof (induct arbitrary: op' rule: good.induct)
  case (good_Leaf k q n)
  obtain io' q'' where *: "step io' q q''"
    "map_IO (node_wrap n) (node_wrap n) id io' = Out (Inr (nid, p)) v"
    "map_op (node_wrap n) (node_wrap n) q'' = op'"
    using step_map_op_elim[OF good_Leaf(3)] by metis
  have io': "io' = Out (Some p) v"
    using *(2) by (cases io') (auto split: option.splits)
  have leaf': "is_Inr v ∧ nop_leaf k q''"
    by (rule nop_leafD_data_out[OF good_Leaf(1) *(1)[unfolded io']])
  have g': "good ok F {n} (map_op (node_wrap n) (node_wrap n) q'')"
    using good.intros(1)[where k = k and ok = ok and F = F, OF conjunct2[OF leaf']] good_Leaf(2) by blast
  show ?case
    using conjunct1[OF leaf'] g' *(3) by simp
next
  case (good_Comp N1 op1 N2 op2 wire buf)
  obtain io' c'' where *: "step io' (comp_op wire buf op1 op2) c''"
    "map_IO (case_sum id id) (case_sum id id) id io' = Out (Inr (nid, p)) v"
    "map_op (case_sum id id) (case_sum id id) c'' = op'"
    using step_map_op_elim[OF good_Comp.prems] by metis
  have cases: "io' = Out (Inl (Inr (nid, p))) v ∨ io' = Out (Inr (Inr (nid, p))) v"
    using *(2) by (cases io') (auto split: sum.splits)
  show ?case
    using cases
  proof (elim disjE)
    assume A: "io' = Out (Inl (Inr (nid, p))) v"
    from *(1)[unfolded A] obtain op1' where s1: "step (Out (Inr (nid, p)) v) op1 op1'"
      and c'': "c'' = comp_op wire buf op1' op2"
      by (cases rule: step_comp_op_elim) auto
    have ih: "is_Inr v ∧ good ok F N1 op1'"
      by (rule good_Comp.hyps(2)[OF s1])
    show ?case
      using conjunct1[OF ih]
        good.intros(2)[OF conjunct2[OF ih] good_Comp.hyps(3) good_Comp.hyps(5) good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)]
        *(3) c'' by simp
  next
    assume A: "io' = Out (Inr (Inr (nid, p))) v"
    from *(1)[unfolded A] obtain op2' where s2: "step (Out (Inr (nid, p)) v) op2 op2'"
      and c'': "c'' = comp_op wire buf op1 op2'"
      by (cases rule: step_comp_op_elim) auto
    have ih: "is_Inr v ∧ good ok F N2 op2'"
      by (rule good_Comp.hyps(4)[OF s2])
    show ?case
      using conjunct1[OF ih]
        good.intros(2)[OF good_Comp.hyps(1) conjunct2[OF ih] good_Comp.hyps(5) good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)]
        *(3) c'' by simp
  qed
next
  case (good_Loop N op wire buf)
  from good_Loop.prems obtain op0' where s0: "step (Out (Inr (nid, p)) v) op op0'"
    and o': "op' = loop_op wire buf op0'"
    by (cases rule: step_loop_op_elim) auto
  have ih: "is_Inr v ∧ good ok F N op0'"
    by (rule good_Loop.hyps(2)[OF s0])
  show ?case
    unfolding o'
    using conjunct1[OF ih] good.intros(3)[OF conjunct2[OF ih] good_Loop.hyps(3) good_Loop.hyps(4) good_Loop.hyps(5)]
    by simp
qed

lemma step_comp_op_Tau_elim:
  assumes "step Tau (comp_op wire buf op1 op2) op'"
  obtains
    (left_wired) p x op1' q where "wire p = Some q"
      "op' = comp_op wire (BENQ q x buf) op1' op2" "step (Out p x) op1 op1'"
  | (right_buf) p x op2' where "p ∈ ran wire"
      "op' = comp_op wire (BTL p buf) op1 op2'" "step (Inp p x) op2 op2'"
      "buf p ≠ []" "BHD p buf = x"
  | (left_Tau) op1' where "op' = comp_op wire buf op1' op2" "step Tau op1 op1'"
  | (right_Tau) op2' where "op' = comp_op wire buf op1 op2'" "step Tau op2 op2'"
  using assms by (cases rule: step_comp_op_elim) auto

lemma good_step_Tau:
  assumes "good ok F N op" and "step Tau op op'"
  shows "good ok F N op'"
  using assms
proof (induct arbitrary: op' rule: good.induct)
  case (good_Leaf k q n)
  obtain io' q'' where *: "step io' q q''"
    "map_IO (node_wrap n) (node_wrap n) id io' = Tau"
    "map_op (node_wrap n) (node_wrap n) q'' = op'"
    using step_map_op_elim[OF good_Leaf(3)] by metis
  have io': "io' = Tau"
    using *(2) by (cases io') auto
  have leaf': "nop_leaf k q''"
    by (rule nop_leafD_Tau[OF good_Leaf(1) *(1)[unfolded io']])
  have g': "good ok F {n} (map_op (node_wrap n) (node_wrap n) q'')"
    using good.intros(1)[where k = k and ok = ok and F = F, OF leaf'] good_Leaf(2) by blast
  show ?case
    using g' *(3) by simp
next
  case (good_Comp N1 op1 N2 op2 wire buf)
  obtain io' c'' where *: "step io' (comp_op wire buf op1 op2) c''"
    "map_IO (case_sum id id) (case_sum id id) id io' = Tau"
    "map_op (case_sum id id) (case_sum id id) c'' = op'"
    using step_map_op_elim[OF good_Comp.prems] by metis
  have io': "io' = Tau"
    using *(2) by (cases io') auto
  from *(1)[unfolded io'] have g'': "good ok F (N1 ∪ N2) (map_op (case_sum id id) (case_sum id id) c'')"
  proof (cases rule: step_comp_op_Tau_elim)
    case (left_wired p x op1' q')
    obtain nidp pp where p: "p = Inr (nidp, pp)"
      using good_Comp.hyps(6) left_wired(1) by (metis obj_sumE option.distinct(1) surj_pair)
    have dout: "is_Inr x ∧ good ok F N1 op1'"
      by (rule good_step_data_out[OF good_Comp.hyps(1) left_wired(3)[unfolded p]])
    have bufok: "∀ q'' v. v ∈ set (BENQ q' x buf q'') ⟶ is_Inr v"
      using good_Comp.hyps(8) conjunct1[OF dout] by (auto simp add: BENQ_def)
    show ?thesis
      unfolding left_wired(2)
      by (rule good.intros(2)[OF conjunct2[OF dout] good_Comp.hyps(3) good_Comp.hyps(5)
            good_Comp.hyps(6) good_Comp.hyps(7) bufok])
  next
    case (right_buf p x op2')
    obtain q0 where q0: "wire q0 = Some p"
      using right_buf(1) by (auto simp add: ran_def)
    have pInr: "is_Inr p"
      using good_Comp.hyps(7) q0 by blast
    obtain y where pY: "p = Inr y"
      using pInr by (cases p) auto
    obtain nidp pp where p: "p = Inr (nidp, pp)"
      using pY by (cases y) auto
    have xin: "x ∈ set (buf p)"
      using right_buf(4,5) by (auto simp add: BHD_def intro: hd_in_set)
    have xInr: "is_Inr x"
      using good_Comp.hyps(8) xin by blast
    obtain z where xZ: "x = Inr z"
      using xInr by (cases x) auto
    obtain d t where x: "x = Inr (d, t)"
      using xZ by (cases z) auto
    have din: "good ok F N2 op2'"
      by (rule good_step_data_in[OF good_Comp.hyps(3) right_buf(3)[unfolded p x]])
    have bufok: "∀ q'' v. v ∈ set (BTL p buf q'') ⟶ is_Inr v"
      using good_Comp.hyps(8) by (auto simp add: BTL_def dest: in_set_tlD)
    show ?thesis
      unfolding right_buf(2)
      by (rule good.intros(2)[OF good_Comp.hyps(1) din good_Comp.hyps(5)
            good_Comp.hyps(6) good_Comp.hyps(7) bufok])
  next
    case (left_Tau op1')
    have "good ok F N1 op1'" by (rule good_Comp.hyps(2)[OF left_Tau(2)])
    then show ?thesis
      unfolding left_Tau(1)
      by (rule good.intros(2)[OF _ good_Comp.hyps(3) good_Comp.hyps(5)
            good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)])
  next
    case (right_Tau op2')
    have "good ok F N2 op2'" by (rule good_Comp.hyps(4)[OF right_Tau(2)])
    then show ?thesis
      unfolding right_Tau(1)
      by (rule good.intros(2)[OF good_Comp.hyps(1) _ good_Comp.hyps(5)
            good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)])
  qed
  show ?case
    using g'' *(3) by simp
next
  case (good_Loop N op wire buf)
  from good_Loop.prems show ?case
  proof (cases rule: step_loop_op_elim)
    case (1 p x op'')
    then show ?thesis by simp
  next
    case (2 p x op'')
    then show ?thesis by simp
  next
    case (3 op'')
    have "good ok F N op''" by (rule good_Loop.hyps(2)[OF 3(3)])
    then show ?thesis
      unfolding 3(2)
      by (rule good.intros(3)[OF _ good_Loop.hyps(3) good_Loop.hyps(4) good_Loop.hyps(5)])
  next
    case (4 op'' p x)
    obtain q0 where q0: "wire q0 = Some p"
      using 4(2) by (auto simp add: ran_def)
    have pInr: "is_Inr p"
      using good_Loop.hyps(4) q0 by blast
    obtain y where pY: "p = Inr y"
      using pInr by (cases p) auto
    obtain nidp pp where p: "p = Inr (nidp, pp)"
      using pY by (cases y) auto
    have xin: "x ∈ set (buf p)"
      using 4(5,6) by (auto simp add: BHD_def intro: hd_in_set)
    have xInr: "is_Inr x"
      using good_Loop.hyps(5) xin by blast
    obtain z where xZ: "x = Inr z"
      using xInr by (cases x) auto
    obtain d t where x: "x = Inr (d, t)"
      using xZ by (cases z) auto
    have din: "good ok F N op''"
      by (rule good_step_data_in[OF good_Loop.hyps(1) 4(4)[unfolded p x]])
    have bufok: "∀ q'' v. v ∈ set (BTL p buf q'') ⟶ is_Inr v"
      using good_Loop.hyps(5) by (auto simp add: BTL_def dest: in_set_tlD)
    show ?thesis
      unfolding 4(3)
      by (rule good.intros(3)[OF din good_Loop.hyps(3) good_Loop.hyps(4) bufok])
  next
    case (5 op'' p q' x)
    obtain nidp pp where p: "p = Inr (nidp, pp)"
      using good_Loop.hyps(3) 5(2) by (metis obj_sumE option.distinct(1) surj_pair)
    have dout: "is_Inr x ∧ good ok F N op''"
      by (rule good_step_data_out[OF good_Loop.hyps(1) 5(4)[unfolded p]])
    have bufok: "∀ q'' v. v ∈ set (BENQ q' x buf q'') ⟶ is_Inr v"
      using good_Loop.hyps(5) conjunct1[OF dout] by (auto simp add: BENQ_def)
    show ?thesis
      unfolding 5(3)
      by (rule good.intros(3)[OF conjunct2[OF dout] good_Loop.hyps(3) good_Loop.hyps(4) bufok])
  qed
qed

lemma good_step_progress:
  assumes "good ok F N op" and "step (Out (Inl nid) (Inl (Inl st))) op op'"
  shows "good (λ _. True) F' N op'"
  using assms
proof (induct arbitrary: op' rule: good.induct)
  case (good_Leaf k q n)
  obtain io' q'' where *: "step io' q q''"
    "map_IO (node_wrap n) (node_wrap n) id io' = Out (Inl nid) (Inl (Inl st))"
    "map_op (node_wrap n) (node_wrap n) q'' = op'"
    using step_map_op_elim[OF good_Leaf(3)] by metis
  have io': "io' = Out None (Inl (Inl st))"
    using *(2) by (cases io') (auto split: option.splits)
  have leaf': "nop_leaf k q''"
    by (rule nop_leafD_progress[OF good_Leaf(1) *(1)[unfolded io']])
  have g': "good (λ _. True) F' {n} (map_op (node_wrap n) (node_wrap n) q'')"
    using good.intros(1)[where k = k and ok = "λ _. True" and F = F', OF leaf'] by blast
  show ?case
    using g' *(3) by simp
next
  case (good_Comp N1 op1 N2 op2 wire buf)
  obtain io' c'' where *: "step io' (comp_op wire buf op1 op2) c''"
    "map_IO (case_sum id id) (case_sum id id) id io' = Out (Inl nid) (Inl (Inl st))"
    "map_op (case_sum id id) (case_sum id id) c'' = op'"
    using step_map_op_elim[OF good_Comp.prems] by metis
  have cases: "io' = Out (Inl (Inl nid)) (Inl (Inl st)) ∨ io' = Out (Inr (Inl nid)) (Inl (Inl st))"
    using *(2) by (cases io') (auto split: sum.splits)
  have gB2: "good (λ _. True) F' N2 op2"
    by (rule good_mono[OF good_Comp.hyps(3)]) simp
  have gB1: "good (λ _. True) F' N1 op1"
    by (rule good_mono[OF good_Comp.hyps(1)]) simp
  show ?case
    using cases
  proof (elim disjE)
    assume A: "io' = Out (Inl (Inl nid)) (Inl (Inl st))"
    from *(1)[unfolded A] obtain op1' where s1: "step (Out (Inl nid) (Inl (Inl st))) op1 op1'"
      and c'': "c'' = comp_op wire buf op1' op2"
      by (cases rule: step_comp_op_elim) auto
    have g1: "good (λ _. True) F' N1 op1'"
      by (rule good_Comp.hyps(2)[OF s1])
    show ?case
      using good.intros(2)[OF g1 gB2 good_Comp.hyps(5) good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)]
        *(3) c'' by simp
  next
    assume A: "io' = Out (Inr (Inl nid)) (Inl (Inl st))"
    from *(1)[unfolded A] obtain op2' where s2: "step (Out (Inl nid) (Inl (Inl st))) op2 op2'"
      and c'': "c'' = comp_op wire buf op1 op2'"
      by (cases rule: step_comp_op_elim) auto
    have g2: "good (λ _. True) F' N2 op2'"
      by (rule good_Comp.hyps(4)[OF s2])
    show ?case
      using good.intros(2)[OF gB1 g2 good_Comp.hyps(5) good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)]
        *(3) c'' by simp
  qed
next
  case (good_Loop N op wire buf)
  from good_Loop.prems obtain op0' where s0: "step (Out (Inl nid) (Inl (Inl st))) op op0'"
    and o': "op' = loop_op wire buf op0'"
    by (cases rule: step_loop_op_elim) auto
  have g0: "good (λ _. True) F' N op0'"
    by (rule good_Loop.hyps(2)[OF s0])
  show ?case
    unfolding o'
    by (rule good.intros(3)[OF g0 good_Loop.hyps(3) good_Loop.hyps(4) good_Loop.hyps(5)])
qed

lemma good_step_frontier:
  assumes "good ok F N op" and "step (Inp (Inl nid) (Inl (Inr G))) op op'"
    and ok': "ok' = ok(nid := False)" and F': "F' = F(nid := G)"
  shows "nid ∈ N ∧ good ok' F' N op'"
  using assms(1,2)
proof (induct arbitrary: op' rule: good.induct)
  case (good_Leaf k q n)
  obtain io' q'' where *: "step io' q q''"
    "map_IO (node_wrap n) (node_wrap n) id io' = Inp (Inl nid) (Inl (Inr G))"
    "map_op (node_wrap n) (node_wrap n) q'' = op'"
    using step_map_op_elim[OF good_Leaf(3)] by metis
  have io': "io' = Inp None (Inl (Inr G))" and n: "n = nid"
    using *(2) by (cases io'; force split: option.splits)+
  have leaf': "nop_leaf (Some G) q''"
    by (rule nop_leafD_frontier[OF good_Leaf(1) *(1)[unfolded io']])
  have g': "good ok' F' {n} (map_op (node_wrap n) (node_wrap n) q'')"
    using good.intros(1)[where k = "Some G" and ok = ok' and F = F', OF leaf'] n F'
    by auto
  show ?case
    using g' *(3) n by simp
next
  case (good_Comp N1 op1 N2 op2 wire buf)
  obtain io' c'' where *: "step io' (comp_op wire buf op1 op2) c''"
    "map_IO (case_sum id id) (case_sum id id) id io' = Inp (Inl nid) (Inl (Inr G))"
    "map_op (case_sum id id) (case_sum id id) c'' = op'"
    using step_map_op_elim[OF good_Comp.prems] by metis
  have cases: "io' = Inp (Inl (Inl nid)) (Inl (Inr G)) ∨ io' = Inp (Inr (Inl nid)) (Inl (Inr G))"
    using *(2) by (cases io') (auto split: sum.splits)
  show ?case
    using cases
  proof (elim disjE)
    assume A: "io' = Inp (Inl (Inl nid)) (Inl (Inr G))"
    from *(1)[unfolded A] obtain op1' where s1: "step (Inp (Inl nid) (Inl (Inr G))) op1 op1'"
      and c'': "c'' = comp_op wire buf op1' op2"
      by (cases rule: step_comp_op_elim) auto
    have ih: "nid ∈ N1 ∧ good ok' F' N1 op1'"
      by (rule good_Comp.hyps(2)[OF s1])
    have gB: "good ok' F' N2 op2"
      apply (rule good_mono[OF good_Comp.hyps(3)])
      using conjunct1[OF ih] good_Comp.hyps(5) ok' F' by auto
    show ?case
      using conjunct1[OF ih]
        good.intros(2)[OF conjunct2[OF ih] gB good_Comp.hyps(5) good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)]
        *(3) c'' by simp
  next
    assume A: "io' = Inp (Inr (Inl nid)) (Inl (Inr G))"
    from *(1)[unfolded A] obtain op2' where s2: "step (Inp (Inl nid) (Inl (Inr G))) op2 op2'"
      and c'': "c'' = comp_op wire buf op1 op2'"
      by (cases rule: step_comp_op_elim) auto
    have ih: "nid ∈ N2 ∧ good ok' F' N2 op2'"
      by (rule good_Comp.hyps(4)[OF s2])
    have gB: "good ok' F' N1 op1"
      apply (rule good_mono[OF good_Comp.hyps(1)])
      using conjunct1[OF ih] good_Comp.hyps(5) ok' F' by auto
    show ?case
      using conjunct1[OF ih]
        good.intros(2)[OF gB conjunct2[OF ih] good_Comp.hyps(5) good_Comp.hyps(6) good_Comp.hyps(7) good_Comp.hyps(8)]
        *(3) c'' by simp
  qed
next
  case (good_Loop N op wire buf)
  from good_Loop.prems obtain op0' where s0: "step (Inp (Inl nid) (Inl (Inr G))) op op0'"
    and o': "op' = loop_op wire buf op0'"
    by (cases rule: step_loop_op_elim) auto
  have ih: "nid ∈ N ∧ good ok' F' N op0'"
    by (rule good_Loop.hyps(2)[OF s0])
  show ?case
    unfolding o'
    using conjunct1[OF ih]
      good.intros(3)[OF conjunct2[OF ih] good_Loop.hyps(3) good_Loop.hyps(4) good_Loop.hyps(5)]
    by simp
qed

subsection ‹The nop invariant›

definition tree_nopP where
  "tree_nopP N sg op ⟷
     good (upfro sg) (λ nid. frontier ∘ (λ p. c_imp (pt_tr sg) (Loc nid (Trg p)))) N op ∧
     ((∃ nid. ¬ upfro sg nid) ⟶ propagate_all (summ sg) (pt_tr sg) = Some (pt_tr sg))"

lemma tree_nopP_step_frontier:
  assumes P: "tree_nopP N sg op"
    and pall: "propagate_all (summ sg) (pt_tr sg) = Some conf'"
    and s: "step (Inp (Inl nid) (Inl (Inr (frontier o (λ p. c_imp conf' (Loc nid (Trg p))))))) op op'"
  shows "tree_nopP N (sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈) op'"
proof -
  let ?sg' = "sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈"
  let ?F = "λ m. frontier ∘ (λ p. c_imp (pt_tr sg) (Loc m (Trg p)))"
  let ?G = "frontier o (λ p. c_imp conf' (Loc nid (Trg p)))"
  let ?FT = "λ m. frontier ∘ (λ p. c_imp conf' (Loc m (Trg p)))"
  have g: "good (upfro sg) ?F N op"
    and fixp: "(∃ m. ¬ upfro sg m) ⟶ propagate_all (summ sg) (pt_tr sg) = Some (pt_tr sg)"
    using P unfolding tree_nopP_def by blast+
  have step': "nid ∈ N ∧ good ((upfro sg)(nid := False)) (?F(nid := ?G)) N op'"
    by (rule good_step_frontier[OF g s refl refl])
  have conf'_cases: "(∀ m. upfro sg m) ∨ conf' = pt_tr sg"
    using fixp pall by auto
  have g': "good ((upfro sg)(nid := False)) ?FT N op'"
    apply (rule good_mono[OF conjunct2[OF step']])
    subgoal for m
      using conf'_cases by (cases "m = nid") auto
    done
  have fix': "propagate_all (summ sg) conf' = Some conf'"
    by (rule propagate_all_idem[OF pall])
  show ?thesis
    unfolding tree_nopP_def using g' fix' by simp
qed

theorem nop_invariant_tree_nopP:
  "nop_invariant (tree_nopP N)"
  unfolding nop_invariant_def
  apply (intro conjI allI impI)
  subgoal for sg op
    unfolding tree_nopP_def nop_sound_def
    by (auto intro: good_frontier_selfloop good_progress_selfloop)
  subgoal for sg op op'
    unfolding tree_nopP_def by (blast intro: good_step_Tau)
  subgoal for sg op op' nid p x
    unfolding tree_nopP_def by (blast intro: good_step_data_in)
  subgoal for sg op op' nid p x
    unfolding tree_nopP_def by (blast dest: good_step_data_out)
  subgoal for sg op op' nid st
    unfolding tree_nopP_def by (auto intro: good_step_progress)
  subgoal for sg op op' nid conf'
    by (rule tree_nopP_step_frontier)
  done

subsection ‹Compiled trees satisfy the invariant›

fun builder_tree where
  "builder_tree (Logic q su) = (∃ k. nop_leaf k q)"
| "builder_tree (Comp wire dt1 dt2) = (builder_tree dt1 ∧ builder_tree dt2)"
| "builder_tree (Loop wire dt) = builder_tree dt"

fun tree_ids :: "('id :: {plus, one}) ⇒ ('id, 'p, 's, 'd, 't) dataflow_tree ⇒ 'id list × 'id" where
  "tree_ids n (Logic q su) = ([n], n + 1)"
| "tree_ids n (Comp wire dt1 dt2) =
    (let (l1, n') = tree_ids n dt1; (l2, n'') = tree_ids n' dt2 in (l1 @ l2, n''))"
| "tree_ids n (Loop wire dt) = tree_ids n dt"

lemma good_dataflow_tree_to_operator_aux:
  assumes "builder_tree dt"
    and "distinct (fst (tree_ids n dt))"
    and "dataflow_tree_to_operator_aux n chns dt = (n', op)"
  shows "good (λ _. True) F (set (fst (tree_ids n dt))) op ∧ n' = snd (tree_ids n dt)"
  using assms
proof (induct dt arbitrary: n n' op)
  case (Logic q su)
  obtain k where k: "nop_leaf k q"
    using Logic.prems(1) by auto
  have aux: "n' = n + 1" "op = map_op (node_wrap n) (node_wrap n) q"
    using Logic.prems(3) by auto
  have g: "good (λ _. True) F {n} (map_op (node_wrap n) (node_wrap n) q)"
    using good.intros(1)[where k = k and ok = "λ _. True" and F = F, OF k] by blast
  show ?case
    using g aux by simp
next
  case (Comp wire dt1 dt2)
  obtain na op1 where a1: "dataflow_tree_to_operator_aux n chns dt1 = (na, op1)"
    by (cases "dataflow_tree_to_operator_aux n chns dt1") auto
  obtain nb op2 where a2: "dataflow_tree_to_operator_aux na chns dt2 = (nb, op2)"
    by (cases "dataflow_tree_to_operator_aux na chns dt2") auto
  obtain l1 na' where t1: "tree_ids n dt1 = (l1, na')"
    by (cases "tree_ids n dt1") auto
  have tC0: "fst (tree_ids n (Comp wire dt1 dt2)) = l1 @ fst (tree_ids na' dt2)"
    and tC1: "snd (tree_ids n (Comp wire dt1 dt2)) = snd (tree_ids na' dt2)"
    using t1 by (auto split: prod.splits)
  have d1: "distinct l1" and d2: "distinct (fst (tree_ids na' dt2))"
    and dis12: "set l1 ∩ set (fst (tree_ids na' dt2)) = {}"
    using Comp.prems(2) unfolding tC0 by auto
  have IH1: "good (λ _. True) F (set (fst (tree_ids n dt1))) op1 ∧ na = snd (tree_ids n dt1)"
    using Comp.hyps(1)[OF _ _ a1] Comp.prems(1) d1 t1 by auto
  have na': "na = na'"
    using IH1 t1 by simp
  have IH2: "good (λ _. True) F (set (fst (tree_ids na' dt2))) op2 ∧ nb = snd (tree_ids na' dt2)"
    using Comp.hyps(2)[OF _ _ a2[unfolded na']] Comp.prems(1) d2 by auto
  have opn': "op = map_op (case_sum id id) (case_sum id id)
      (comp_op (case_sum (λ _. None) (λ (nid, p). case wire (nid - n, p) of None ⇒ None
          | Some (offset, q) ⇒ Some (Inr (na + offset, q))))
        (case_sum (λ x. []) (λ x. map Inr (chns x))) op1 op2)"
    and n'nb: "n' = nb"
    using Comp.prems(3) by (auto simp add: a1 a2 split: prod.splits)
  have g1: "good (λ _. True) F (set l1) op1"
    using IH1 t1 by simp
  have g2: "good (λ _. True) F (set (fst (tree_ids na' dt2))) op2"
    using IH2 by blast
  have gC: "good (λ _. True) F (set l1 ∪ set (fst (tree_ids na' dt2))) op"
    unfolding opn'
    apply (rule good.intros(2)[OF g1 g2 dis12])
    subgoal by simp
    subgoal by (auto split: sum.splits prod.splits option.splits)
    subgoal by (auto split: sum.splits)
    done
  show ?case
    using gC n'nb IH2 unfolding tC0 tC1 by auto
next
  case (Loop wire dt)
  obtain na op0 where a0: "dataflow_tree_to_operator_aux n chns dt = (na, op0)"
    by (cases "dataflow_tree_to_operator_aux n chns dt") auto
  have IH: "good (λ _. True) F (set (fst (tree_ids n dt))) op0 ∧ na = snd (tree_ids n dt)"
    using Loop.hyps(1)[OF _ _ a0] Loop.prems(1,2) by auto
  have opn': "op = loop_op
      (case_sum (λ _. None) (λ (nid, p). case wire (nid - n, p) of None ⇒ None
          | Some (offset, q) ⇒ Some (Inr (n + offset, q))))
      (case_sum (λ x. []) (λ x. map Inr (chns x))) op0"
    and n'na: "n' = na"
    using Loop.prems(3) by (auto simp add: a0 split: prod.splits)
  have gL: "good (λ _. True) F (set (fst (tree_ids n dt))) op"
    unfolding opn'
    apply (rule good.intros(3)[OF conjunct1[OF IH]])
    subgoal by simp
    subgoal by (auto split: sum.splits prod.splits option.splits)
    subgoal by (auto split: sum.splits)
    done
  show ?case
    using gL n'na IH by auto
qed

theorem tree_nopP_compile:
  assumes bt: "builder_tree dt"
    and dis: "distinct (fst (tree_ids 0 dt))"
  shows "tree_nopP (set (fst (tree_ids 0 dt)))
     (init_subgraph_opt (antichain_from_list oo (dataflow_tree_to_graph dt)))
     (dataflow_tree_to_operator chns dt)"
proof -
  obtain n' op where aux: "dataflow_tree_to_operator_aux 0 chns dt = (n', op)"
    by (cases "dataflow_tree_to_operator_aux 0 chns dt") auto
  show ?thesis
    unfolding tree_nopP_def dataflow_tree_to_operator_def aux
    using good_dataflow_tree_to_operator_aux[OF bt dis aux]
    by (auto simp add: init_subgraph_opt_def)
qed

subsection ‹The generic equivalence theorems›

theorem compile_dataflow_opt_wbisim_generic:
  assumes "builder_tree dt"
    and "distinct (fst (tree_ids 0 dt))"
  shows "compile_dataflow_opt chns dt ≈ compile_dataflow chns dt"
  by (rule compile_dataflow_opt_wbisim[OF nop_invariant_tree_nopP tree_nopP_compile[OF assms]])

theorem compile_dataflow_opt_wtraces_generic:
  assumes "builder_tree dt"
    and "distinct (fst (tree_ids 0 dt))"
  shows "compile_dataflow_opt chns dt ≡⇩t compile_dataflow chns dt"
  by (rule wbisim_wtraces[OF compile_dataflow_opt_wbisim_generic[OF assms]])

end
