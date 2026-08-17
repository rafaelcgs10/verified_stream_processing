theory Dataflow_Opt_Op

imports
  Dataflow_Op
  Propagation_Idempotence
  Nop_Step_Lemmas
begin

section ‹Optimized Dataflow Wrapper Operator›


text ‹A copy of @{const dataflow_op} whose choice set is filtered by
@{term "not_nop sg"}: frontier reads at nodes whose frontier is already
up to date and progress writes without progress are pruned away.›

corec dataflow_opt_op where
  "dataflow_opt_op sg op = Choice (cimage (λ op. case op of
     Read (Inl nid) f ⇒ (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' ⇒ let sg' = sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈ in
         let imp_fron = (λ p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_opt_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None ⇒ ⊘)
   | Read (Inr (nid, p)) f ⇒ Read (nid, p) (λ x. dataflow_opt_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) ⇒ Write (dataflow_opt_op sg op') (nid, p) x
   | Silent op' ⇒ Silent (dataflow_opt_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) ⇒ Silent (dataflow_opt_op (sg⦇ upfro := (λ _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈) op')
   | _ ⇒ Code.abort (STR ''Operator in dataflow_opt_op breaks contract'') (λ _. ⊘))
   (cfilter (not_nop sg) (choices op))
   )"

lemmas dataflow_opt_op_code[code] = dataflow_opt_op.code

subsection ‹Transition Rules for @{const dataflow_opt_op}›

lemma step_dataflow_opt_op_elim:
  assumes "step io (dataflow_opt_op sg op) op'"
  obtains
    (read_data) nid p op'' x where "io = Inp (nid, p) x" "op' = dataflow_opt_op sg op''"
      "step (Inp (Inr (nid, p)) (Inr x)) op op''"
  | (write_data) nid p op'' x where "io = Out (nid, p) x" "op' = dataflow_opt_op sg op''"
      "step (Out (Inr (nid, p)) (Inr x)) op op''"
  | (silent) op'' where "io = Tau" "op' = dataflow_opt_op sg op''" "step Tau op op''"
  | (write_progress) nid op'' st where "io = Tau" "has_progress st"
      "op' = dataflow_opt_op (sg⦇ upfro := (λ _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈) op''"
      "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | (read_frontier) nid op'' conf' sg' imp_fron where "io = Tau" "upfro sg nid"
      "propagate_all (summ sg) (pt_tr sg) = Some conf'"
      "sg' = sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈"
      "imp_fron = (λ p. c_imp (pt_tr sg') (Loc nid (Trg p)))"
      "op' = dataflow_opt_op sg' op''"
      "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) dataflow_opt_op.code)
  apply (elim stepChoiceE)
  subgoal for opc
    apply (auto del: disjCI split: op.splits sum.splits option.splits simp flip: cin.rep_eq)
    apply fastforce+
    done
  done

lemma step_dataflow_op_elim':
  assumes "step io (dataflow_op sg op) op'"
  obtains
    (read_data) nid p op'' x where "io = Inp (nid, p) x" "op' = dataflow_op sg op''"
      "step (Inp (Inr (nid, p)) (Inr x)) op op''"
  | (write_data) nid p op'' x where "io = Out (nid, p) x" "op' = dataflow_op sg op''"
      "step (Out (Inr (nid, p)) (Inr x)) op op''"
  | (silent) op'' where "io = Tau" "op' = dataflow_op sg op''" "step Tau op op''"
  | (write_progress) nid op'' st where "io = Tau"
      "op' = dataflow_op (sg⦇ pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈) op''"
      "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | (read_frontier) nid op'' conf' sg' imp_fron where "io = Tau"
      "propagate_all (summ sg) (pt_tr sg) = Some conf'"
      "sg' = sg⦇ pt_tr := conf' ⦈"
      "imp_fron = (λ p. c_imp (pt_tr sg') (Loc nid (Trg p)))"
      "op' = dataflow_op sg' op''"
      "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) dataflow_op.code)
  apply (elim stepChoiceE)
  subgoal for opc
    apply (auto del: disjCI split: op.splits sum.splits option.splits simp flip: cin.rep_eq)
    apply fastforce+
    done
  done

lemma step_Tau_dataflow_opt_op_Inp_Inl_intro[intro]:
  "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op' ⟹
   upfro sg nid ⟹
   propagate_all (summ sg) (pt_tr sg) = Some conf' ⟹
   sg' = sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈ ⟹
   imp_fron = (λ p. c_imp (pt_tr sg') (Loc nid (Trg p))) ⟹
   step Tau (dataflow_opt_op sg op) (dataflow_opt_op sg' op')"
  apply (subst dataflow_opt_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_opt_op_Out_Inl_intro[intro]:
  "step (Out (Inl nid) (Inl (Inl st))) op op' ⟹
   has_progress st ⟹
   sg' = sg⦇ upfro := (λ _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈ ⟹
   step Tau (dataflow_opt_op sg op) (dataflow_opt_op sg' op')"
  apply (subst dataflow_opt_op.code)
  apply (force elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_opt_op_Tau_intro[intro]:
  "step Tau op op' ⟹
   step Tau (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply (subst dataflow_opt_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Out_dataflow_opt_op_Out_Inr_intro[intro!]:
  "step (Out (Inr (nid, p)) (Inr x)) op op' ⟹
   step (Out (nid, p) x) (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply (subst dataflow_opt_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Inp_dataflow_opt_op_Inp_Inr_intro[intro!]:
  "step (Inp (Inr (nid, p)) (Inr x)) op op' ⟹
   step (Inp (nid, p) x) (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply (subst dataflow_opt_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma steps_Tau_dataflow_opt_op_Tau_intro[intro]:
  "steps (replicate n Tau) op op' ⟹
   (step Tau ^^ n) (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply (induct n arbitrary: op op' sg)
   apply clarsimp+
  apply (metis (no_types, lifting) relcompp_apply relpowp_commute step_Tau_dataflow_opt_op_Tau_intro)
  done

lemma steps_Tau_dataflow_opt_op_steps_Out_intro[intro]:
  "steps (map (λ x. Out (Inr (nid, p)) (Inr x)) xs) op op' ⟹
   ys = map (λ x. Out (nid, p) x) xs ⟹
   (steps ys) (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply hypsubst_thin
  apply (induct xs arbitrary: op op' sg rule: rev_induct)
   apply clarsimp+
  apply fastforce
  done

lemma step_Taus_dataflow_opt_op_Taus_intro[intro]:
  "(step Tau)⇧*⇧* op op' ⟹
   (step Tau)⇧*⇧* (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply (induct op' rule: rtranclp_induct)
   apply force
  apply (meson rtranclp.intros(2) step_Tau_dataflow_opt_op_Tau_intro)
  done

lemma step_tau_pow_dataflow_opt_op[intro]:
  "(step Tau ^^ n) op op' ⟹
   (step Tau ^^ n) (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  by (induct n arbitrary: op') auto

lemma dataflow_opt_op_simps[simp]:
  "¬ is_Read (dataflow_opt_op sg op)"
  "¬ is_Write (dataflow_opt_op sg op)"
  "¬ is_Silent (dataflow_opt_op sg op)"
  "is_Choice (dataflow_opt_op sg op)"
  by (subst dataflow_opt_op.code; simp)+

section ‹The Nop Invariant›

text ‹Local soundness of the pruned choices: whenever some node's frontier
flag is stale, the progress-tracker configuration is a @{const propagate_all}
fixpoint; frontier reads at stale nodes deliver exactly what the node already
knows (the continuation is the operator itself); and progress writes without
progress are self-loops.›

definition nop_sound where
  "nop_sound sg op ⟷
     (∀ nid. ¬ upfro sg nid ⟶ propagate_all (summ sg) (pt_tr sg) = Some (pt_tr sg)) ∧
     (∀ nid op'. ¬ upfro sg nid ⟶
        step (Inp (Inl nid) (Inl (Inr (frontier o (λ p. c_imp (pt_tr sg) (Loc nid (Trg p))))))) op op' ⟶ op' = op) ∧
     (∀ nid st op'. ¬ has_progress st ⟶ step (Out (Inl nid) (Inl (Inl st))) op op' ⟶ op' = op)"

text ‹@{term "nop_invariant P"} states that @{term P} implies local soundness
and is closed under all transition shapes of the (optimized) dataflow wrapper.
The coinduction below is parameterized by any such @{term P}.›

definition nop_invariant where
  "nop_invariant P ⟷
     (∀ sg op. P sg op ⟶ nop_sound sg op) ∧
     (∀ sg op op'. P sg op ⟶ step Tau op op' ⟶ P sg op') ∧
     (∀ sg op op' nid p x. P sg op ⟶ step (Inp (Inr (nid, p)) (Inr x)) op op' ⟶ P sg op') ∧
     (∀ sg op op' nid p x. P sg op ⟶ step (Out (Inr (nid, p)) (Inr x)) op op' ⟶ P sg op') ∧
     (∀ sg op op' nid st. P sg op ⟶ step (Out (Inl nid) (Inl (Inl st))) op op' ⟶ has_progress st ⟶
        P (sg⦇ upfro := (λ _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈) op') ∧
     (∀ sg op op' nid conf'. P sg op ⟶ upfro sg nid ⟶ propagate_all (summ sg) (pt_tr sg) = Some conf' ⟶
        step (Inp (Inl nid) (Inl (Inr (frontier o (λ p. c_imp conf' (Loc nid (Trg p))))))) op op' ⟶
        P (sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈) op')"

lemma nop_soundD_propagate:
  "nop_sound sg op ⟹ ¬ upfro sg nid ⟹ propagate_all (summ sg) (pt_tr sg) = Some (pt_tr sg)"
  unfolding nop_sound_def by blast

lemma nop_soundD_read_frontier:
  "nop_sound sg op ⟹ ¬ upfro sg nid ⟹
   step (Inp (Inl nid) (Inl (Inr (frontier o (λ p. c_imp (pt_tr sg) (Loc nid (Trg p))))))) op op' ⟹
   op' = op"
  unfolding nop_sound_def by blast

lemma nop_soundD_write_progress:
  "nop_sound sg op ⟹ ¬ has_progress st ⟹ step (Out (Inl nid) (Inl (Inl st))) op op' ⟹ op' = op"
  unfolding nop_sound_def by blast

lemma nop_invariantD_sound:
  assumes "nop_invariant P" and "P sg op"
  shows "nop_sound sg op"
  using assms(1)[unfolded nop_invariant_def, THEN conjunct1, rule_format, OF assms(2)] .

lemma nop_invariantD_Tau:
  assumes "nop_invariant P" and "P sg op" and "step Tau op op'"
  shows "P sg op'"
  using assms(1)[unfolded nop_invariant_def, THEN conjunct2, THEN conjunct1, rule_format,
    OF assms(2) assms(3)] .

lemma nop_invariantD_Inp:
  assumes "nop_invariant P" and "P sg op" and "step (Inp (Inr (nid, p)) (Inr x)) op op'"
  shows "P sg op'"
  using assms(1)[unfolded nop_invariant_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
    rule_format, OF assms(2) assms(3)] .

lemma nop_invariantD_Out:
  assumes "nop_invariant P" and "P sg op" and "step (Out (Inr (nid, p)) (Inr x)) op op'"
  shows "P sg op'"
  using assms(1)[unfolded nop_invariant_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
    THEN conjunct1, rule_format, OF assms(2) assms(3)] .

lemma nop_invariantD_progress:
  assumes "nop_invariant P" and "P sg op" and "step (Out (Inl nid) (Inl (Inl st))) op op'"
    and "has_progress st"
  shows "P (sg⦇ upfro := (λ _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈) op'"
  using assms(1)[unfolded nop_invariant_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
    THEN conjunct2, THEN conjunct1, rule_format, OF assms(2) assms(3) assms(4)] .

lemma nop_invariantD_frontier:
  assumes "nop_invariant P" and "P sg op" and "upfro sg nid"
    and "propagate_all (summ sg) (pt_tr sg) = Some conf'"
    and "step (Inp (Inl nid) (Inl (Inr (frontier o (λ p. c_imp conf' (Loc nid (Trg p))))))) op op'"
  shows "P (sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈) op'"
  using assms(1)[unfolded nop_invariant_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
    THEN conjunct2, THEN conjunct2, rule_format, OF assms(2) assms(3) assms(4) assms(5)] .

section ‹Weak Bisimilarity of the Optimized and Plain Operators›

text ‹The plain wrapper runs on the truncation of the optimized wrapper's
subgraph: the two agree on all fields except the @{const upfro} bookkeeping,
which only the optimized wrapper maintains.›

lemma subgraph_truncate_simps[simp]:
  "pt_tr (subgraph.truncate sgo) = pt_tr sgo"
  "nxt (subgraph.truncate sgo) = nxt sgo"
  "summ (subgraph.truncate sgo) = summ sgo"
  "subgraph.truncate (sgo⦇ pt_tr := c ⦈) = subgraph.truncate sgo ⦇ pt_tr := c ⦈"
  "subgraph.truncate (sgo⦇ upfro := u ⦈) = subgraph.truncate sgo"
  by (simp_all add: subgraph.truncate_def)

lemma dataflow_opt_op_sim1:
  assumes inv: "nop_invariant P"
    and Pop: "P sg op"
    and stp: "step io (dataflow_opt_op sg op) op1'"
  shows "∃ sg' op''. wstep io (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg') op'') ∧
     op1' = dataflow_opt_op sg' op'' ∧ P sg' op''"
  using stp
proof (cases rule: step_dataflow_opt_op_elim)
  case (read_data nid p op'' x)
  have s2: "step (Inp (nid, p) x) (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg) op'')"
    using read_data(3) by blast
  have P': "P sg op''"
    by (rule nop_invariantD_Inp[OF inv Pop read_data(3)])
  show ?thesis
    unfolding read_data(1)
    using s2 P' read_data(2) by blast
next
  case (write_data nid p op'' x)
  have s2: "step (Out (nid, p) x) (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg) op'')"
    using write_data(3) by blast
  have P': "P sg op''"
    by (rule nop_invariantD_Out[OF inv Pop write_data(3)])
  show ?thesis
    unfolding write_data(1)
    using s2 P' write_data(2) by blast
next
  case (silent op'')
  have s2: "step Tau (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg) op'')"
    using silent(3) by blast
  have P': "P sg op''"
    by (rule nop_invariantD_Tau[OF inv Pop silent(3)])
  show ?thesis
    unfolding silent(1)
    using s2 P' silent(2) by blast
next
  case (write_progress nid op'' st)
  let ?sg' = "sg⦇ upfro := (λ _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈"
  have s2: "step Tau (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate ?sg') op'')"
    by (rule step_Tau_dataflow_op_Out_Inl_intro[OF write_progress(4)]) simp
  have P': "P ?sg' op''"
    by (rule nop_invariantD_progress[OF inv Pop write_progress(4) write_progress(2)])
  show ?thesis
  proof (intro exI conjI)
    show "wstep io (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate ?sg') op'')"
      unfolding write_progress(1) using s2 by blast
    show "op1' = dataflow_opt_op ?sg' op''"
      by (rule write_progress(3))
    show "P ?sg' op''"
      by (rule P')
  qed
next
  case (read_frontier nid op'' conf' sg' imp_fron)
  have imp_eq: "imp_fron = (λ p. c_imp conf' (Loc nid (Trg p)))"
    unfolding read_frontier(5) read_frontier(4) by simp
  have step0: "step (Inp (Inl nid) (Inl (Inr (frontier o (λ p. c_imp conf' (Loc nid (Trg p))))))) op op''"
    using read_frontier(7) unfolding imp_eq .
  have prop2: "propagate_all (summ (subgraph.truncate sg)) (pt_tr (subgraph.truncate sg)) = Some conf'"
    using read_frontier(3) by simp
  have s2: "step Tau (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg ⦇ pt_tr := conf' ⦈) op'')"
    by (rule step_Tau_dataflow_op_Inp_Inl_intro[OF step0 prop2 refl]) simp
  have P': "P sg' op''"
    unfolding read_frontier(4)
    by (rule nop_invariantD_frontier[OF inv Pop read_frontier(2) read_frontier(3) step0])
  have trunc: "subgraph.truncate sg ⦇ pt_tr := conf' ⦈ = subgraph.truncate sg'"
    unfolding read_frontier(4) by simp
  show ?thesis
  proof (intro exI conjI)
    show "wstep io (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg') op'')"
      unfolding read_frontier(1) using s2 unfolding trunc by blast
    show "op1' = dataflow_opt_op sg' op''"
      by (rule read_frontier(6))
    show "P sg' op''"
      by (rule P')
  qed
qed

lemma dataflow_opt_op_sim2:
  assumes inv: "nop_invariant P"
    and Pop: "P sg op"
    and stp: "step io (dataflow_op (subgraph.truncate sg) op) op2'"
  shows "∃ sg' op''. wstep io (dataflow_opt_op sg op) (dataflow_opt_op sg' op'') ∧
     op2' = dataflow_op (subgraph.truncate sg') op'' ∧ P sg' op''"
  using stp
proof (cases rule: step_dataflow_op_elim')
  case (read_data nid p op'' x)
  have s1: "step (Inp (nid, p) x) (dataflow_opt_op sg op) (dataflow_opt_op sg op'')"
    using read_data(3) by blast
  have P': "P sg op''"
    by (rule nop_invariantD_Inp[OF inv Pop read_data(3)])
  show ?thesis
    unfolding read_data(1)
    using s1 P' read_data(2) by blast
next
  case (write_data nid p op'' x)
  have s1: "step (Out (nid, p) x) (dataflow_opt_op sg op) (dataflow_opt_op sg op'')"
    using write_data(3) by blast
  have P': "P sg op''"
    by (rule nop_invariantD_Out[OF inv Pop write_data(3)])
  show ?thesis
    unfolding write_data(1)
    using s1 P' write_data(2) by blast
next
  case (silent op'')
  have s1: "step Tau (dataflow_opt_op sg op) (dataflow_opt_op sg op'')"
    using silent(3) by blast
  have P': "P sg op''"
    by (rule nop_invariantD_Tau[OF inv Pop silent(3)])
  show ?thesis
    unfolding silent(1)
    using s1 P' silent(2) by blast
next
  case (write_progress nid op'' st)
  show ?thesis
  proof (cases "has_progress st")
    case True
    let ?sg' = "sg⦇ upfro := (λ _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈"
    have s1: "step Tau (dataflow_opt_op sg op) (dataflow_opt_op ?sg' op'')"
      by (rule step_Tau_dataflow_opt_op_Out_Inl_intro[OF write_progress(3) True refl])
    have P': "P ?sg' op''"
      by (rule nop_invariantD_progress[OF inv Pop write_progress(3) True])
    have eq2: "subgraph.truncate sg ⦇ pt_tr := change_multiplicities (summ (subgraph.truncate sg)) (extract_progress nid (nxt (subgraph.truncate sg)) st) (pt_tr (subgraph.truncate sg)) ⦈ = subgraph.truncate ?sg'"
      by simp
    show ?thesis
    proof (intro exI conjI)
      show "wstep io (dataflow_opt_op sg op) (dataflow_opt_op ?sg' op'')"
        unfolding write_progress(1) using s1 by blast
      show "op2' = dataflow_op (subgraph.truncate ?sg') op''"
        using write_progress(2) unfolding eq2 .
      show "P ?sg' op''"
        by (rule P')
    qed
  next
    case False
    have op''_eq: "op'' = op"
      by (rule nop_soundD_write_progress[OF nop_invariantD_sound[OF inv Pop] False write_progress(3)])
    have eq2: "subgraph.truncate sg ⦇ pt_tr := change_multiplicities (summ (subgraph.truncate sg)) (extract_progress nid (nxt (subgraph.truncate sg)) st) (pt_tr (subgraph.truncate sg)) ⦈ = subgraph.truncate sg"
      using False by simp
    show ?thesis
    proof (intro exI conjI)
      show "wstep io (dataflow_opt_op sg op) (dataflow_opt_op sg op)"
        unfolding write_progress(1) wstep_steps_Tau by (rule rtranclp.rtrancl_refl)
      show "op2' = dataflow_op (subgraph.truncate sg) op"
        using write_progress(2) unfolding eq2 op''_eq .
      show "P sg op"
        by (rule Pop)
    qed
  qed
next
  case (read_frontier nid op'' conf' sg' imp_fron)
  show ?thesis
  proof (cases "upfro sg nid")
    case True
    let ?sg' = "sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈"
    have prop1: "propagate_all (summ sg) (pt_tr sg) = Some conf'"
      using read_frontier(2) by simp
    have imp_eq: "imp_fron = (λ p. c_imp conf' (Loc nid (Trg p)))"
      unfolding read_frontier(4) read_frontier(3) by simp
    have step0: "step (Inp (Inl nid) (Inl (Inr (frontier o (λ p. c_imp conf' (Loc nid (Trg p))))))) op op''"
      using read_frontier(6) unfolding imp_eq .
    have s1: "step Tau (dataflow_opt_op sg op) (dataflow_opt_op ?sg' op'')"
      by (rule step_Tau_dataflow_opt_op_Inp_Inl_intro[OF step0 True prop1 refl]) simp
    have P': "P ?sg' op''"
      by (rule nop_invariantD_frontier[OF inv Pop True prop1 step0])
    have trunc: "sg' = subgraph.truncate ?sg'"
      unfolding read_frontier(3) by simp
    show ?thesis
    proof (intro exI conjI)
      show "wstep io (dataflow_opt_op sg op) (dataflow_opt_op ?sg' op'')"
        unfolding read_frontier(1) using s1 by blast
      show "op2' = dataflow_op (subgraph.truncate ?sg') op''"
        using read_frontier(5) unfolding trunc .
      show "P ?sg' op''"
        by (rule P')
    qed
  next
    case False
    have sound: "nop_sound sg op"
      by (rule nop_invariantD_sound[OF inv Pop])
    have fix1: "propagate_all (summ sg) (pt_tr sg) = Some (pt_tr sg)"
      by (rule nop_soundD_propagate[OF sound False])
    have conf'_eq: "conf' = pt_tr sg"
      using read_frontier(2) fix1 by simp
    have imp_eq: "imp_fron = (λ p. c_imp (pt_tr sg) (Loc nid (Trg p)))"
      unfolding read_frontier(4) read_frontier(3) by (simp add: conf'_eq)
    have step0: "step (Inp (Inl nid) (Inl (Inr (frontier o (λ p. c_imp (pt_tr sg) (Loc nid (Trg p))))))) op op''"
      using read_frontier(6) unfolding imp_eq .
    have op''_eq: "op'' = op"
      by (rule nop_soundD_read_frontier[OF sound False step0])
    have sg'_eq: "sg' = subgraph.truncate sg"
      unfolding read_frontier(3) by (simp add: conf'_eq)
    show ?thesis
    proof (intro exI conjI)
      show "wstep io (dataflow_opt_op sg op) (dataflow_opt_op sg op)"
        unfolding read_frontier(1) wstep_steps_Tau by (rule rtranclp.rtrancl_refl)
      show "op2' = dataflow_op (subgraph.truncate sg) op"
        using read_frontier(5) unfolding sg'_eq op''_eq .
      show "P sg op"
        by (rule Pop)
    qed
  qed
qed

theorem dataflow_opt_op_wbisim:
  assumes inv: "nop_invariant P"
    and Pop: "P sg op"
  shows "dataflow_opt_op sg op ≈ dataflow_op (subgraph.truncate sg) op"
proof -
  define R where "R = (λ op1 op2. ∃ sg op.
     op1 = dataflow_opt_op sg op ∧ op2 = dataflow_op (subgraph.truncate sg) op ∧ P sg op)"
  have init: "R (dataflow_opt_op sg op) (dataflow_op (subgraph.truncate sg) op)"
    unfolding R_def using Pop by blast
  have sim1: "⋀ opa opb io opa'. R opa opb ⟹ step io opa opa' ⟹
     ∃ opb'. wstep io opb opb' ∧ 𝒲 R opa' opb'"
  proof -
    fix opa opb io opa'
    assume R: "R opa opb" and s: "step io opa opa'"
    obtain sg op where *: "opa = dataflow_opt_op sg op" "opb = dataflow_op (subgraph.truncate sg) op"
      "P sg op"
      using R unfolding R_def by blast
    obtain sg' op'' where **: "wstep io (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg') op'')"
      "opa' = dataflow_opt_op sg' op''" "P sg' op''"
      using dataflow_opt_op_sim1[OF inv *(3) s[unfolded *(1)]] by blast
    have "R opa' (dataflow_op (subgraph.truncate sg') op'')"
      unfolding R_def using **(2,3) by blast
    then show "∃ opb'. wstep io opb opb' ∧ 𝒲 R opa' opb'"
      using **(1) unfolding *(2) by (blast intro: wbcr_base)
  qed
  have sim2: "⋀ opa opb io opb'. R opa opb ⟹ step io opb opb' ⟹
     ∃ opa'. wstep io opa opa' ∧ 𝒲 R opa' opb'"
  proof -
    fix opa opb io opb'
    assume R: "R opa opb" and s: "step io opb opb'"
    obtain sg op where *: "opa = dataflow_opt_op sg op" "opb = dataflow_op (subgraph.truncate sg) op"
      "P sg op"
      using R unfolding R_def by blast
    obtain sg' op'' where **: "wstep io (dataflow_opt_op sg op) (dataflow_opt_op sg' op'')"
      "opb' = dataflow_op (subgraph.truncate sg') op''" "P sg' op''"
      using dataflow_opt_op_sim2[OF inv *(3) s[unfolded *(2)]] by blast
    have "R (dataflow_opt_op sg' op'') opb'"
      unfolding R_def **(2) using **(3) by blast
    then show "∃ opa'. wstep io opa opa' ∧ 𝒲 R opa' opb'"
      using **(1) unfolding *(1) by (blast intro: wbcr_base)
  qed
  show ?thesis
    by (rule wbisim_coinduct[OF init sim1 sim2])
qed

section ‹Compilation Entry Points›

definition "init_subgraph_opt summary =
   ⦇ pt_tr = init_conf summary,
   nxt = graph_to_nxt summary,
   summ = summary, upfro = (λ _. True) ⦈"

lemma truncate_init_subgraph_opt[simp]:
  "subgraph.truncate (init_subgraph_opt summary) = init_subgraph summary"
  by (simp add: init_subgraph_opt_def init_subgraph_def subgraph.truncate_def)

definition "compile_dataflow_opt chns dt = (let summary = antichain_from_list oo (dataflow_tree_to_graph dt) in
                                    let op = dataflow_tree_to_operator chns dt in
                                    let sg = init_subgraph_opt summary in
                                    dataflow_opt_op sg op)"

corollary dataflow_opt_op_wbisim_start:
  assumes "nop_invariant P" and "P (init_subgraph_opt summary) op"
  shows "dataflow_opt_op (init_subgraph_opt summary) op ≈ dataflow_op (init_subgraph summary) op"
  using dataflow_opt_op_wbisim[OF assms] by simp

corollary compile_dataflow_opt_wbisim:
  assumes "nop_invariant P"
    and "P (init_subgraph_opt (antichain_from_list oo (dataflow_tree_to_graph dt)))
         (dataflow_tree_to_operator chns dt)"
  shows "compile_dataflow_opt chns dt ≈ compile_dataflow chns dt"
  unfolding compile_dataflow_opt_def compile_dataflow_def Let_def
  by (rule dataflow_opt_op_wbisim_start[OF assms])

corollary compile_dataflow_opt_wtraces:
  assumes "nop_invariant P"
    and "P (init_subgraph_opt (antichain_from_list oo (dataflow_tree_to_graph dt)))
         (dataflow_tree_to_operator chns dt)"
  shows "compile_dataflow_opt chns dt ≡⇩t compile_dataflow chns dt"
  by (rule wbisim_wtraces[OF compile_dataflow_opt_wbisim[OF assms]])

end
