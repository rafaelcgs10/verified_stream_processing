theory Dataflow_Opt_Op

imports
  Dataflow_Op
  Propagation_Idempotence
  Nop_Step_Lemmas
begin

section \<open>Optimized Dataflow Wrapper Operator\<close>


text \<open>A copy of @{const dataflow_op} whose choice set is filtered by
@{term "not_nop sg"}: frontier reads at nodes whose frontier is already
up to date and progress writes without progress are pruned away.\<close>

corec dataflow_opt_op where
  "dataflow_opt_op sg op = Choice (cimage (\<lambda> op. case op of
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_opt_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None \<Rightarrow> \<oslash>)
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. dataflow_opt_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_opt_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (dataflow_opt_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (dataflow_opt_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_opt_op breaks contract'') (\<lambda> _. \<oslash>))
   (cfilter (not_nop sg) (choices op))
   )"

lemmas dataflow_opt_op_code[code] = dataflow_opt_op.code

subsection \<open>Transition Rules for @{const dataflow_opt_op}\<close>

lemma step_dataflow_opt_op_elim:
  assumes "step io (dataflow_opt_op sg op) op'"
  obtains
    (read_data) nid p op'' x where "io = Inp (nid, p) x" "op' = dataflow_opt_op sg op''"
      "step (Inp (Inr (nid, p)) (Inr x)) op op''"
  | (write_data) nid p op'' x where "io = Out (nid, p) x" "op' = dataflow_opt_op sg op''"
      "step (Out (Inr (nid, p)) (Inr x)) op op''"
  | (silent) op'' where "io = Tau" "op' = dataflow_opt_op sg op''" "step Tau op op''"
  | (write_progress) nid op'' st where "io = Tau" "has_progress st"
      "op' = dataflow_opt_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op''"
      "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | (read_frontier) nid op'' conf' sg' imp_fron where "io = Tau" "upfro sg nid"
      "propagate_all (summ sg) (pt_tr sg) = Some conf'"
      "sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr>"
      "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))"
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
      "op' = dataflow_op (sg\<lparr> pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op''"
      "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | (read_frontier) nid op'' conf' sg' imp_fron where "io = Tau"
      "propagate_all (summ sg) (pt_tr sg) = Some conf'"
      "sg' = sg\<lparr> pt_tr := conf' \<rparr>"
      "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))"
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
  "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op' \<Longrightarrow>
   upfro sg nid \<Longrightarrow>
   propagate_all (summ sg) (pt_tr sg) = Some conf' \<Longrightarrow>
   sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> \<Longrightarrow>
   imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) \<Longrightarrow>
   step Tau (dataflow_opt_op sg op) (dataflow_opt_op sg' op')"
  apply (subst dataflow_opt_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_opt_op_Out_Inl_intro[intro]:
  "step (Out (Inl nid) (Inl (Inl st))) op op' \<Longrightarrow>
   has_progress st \<Longrightarrow>
   sg' = sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr> \<Longrightarrow>
   step Tau (dataflow_opt_op sg op) (dataflow_opt_op sg' op')"
  apply (subst dataflow_opt_op.code)
  apply (force elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_opt_op_Tau_intro[intro]:
  "step Tau op op' \<Longrightarrow>
   step Tau (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply (subst dataflow_opt_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Out_dataflow_opt_op_Out_Inr_intro[intro!]:
  "step (Out (Inr (nid, p)) (Inr x)) op op' \<Longrightarrow>
   step (Out (nid, p) x) (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply (subst dataflow_opt_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Inp_dataflow_opt_op_Inp_Inr_intro[intro!]:
  "step (Inp (Inr (nid, p)) (Inr x)) op op' \<Longrightarrow>
   step (Inp (nid, p) x) (dataflow_opt_op sg op) (dataflow_opt_op sg op')"
  apply (subst dataflow_opt_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma dataflow_opt_op_simps[simp]:
  "\<not> is_Read (dataflow_opt_op sg op)"
  "\<not> is_Write (dataflow_opt_op sg op)"
  "\<not> is_Silent (dataflow_opt_op sg op)"
  "is_Choice (dataflow_opt_op sg op)"
  by (subst dataflow_opt_op.code; simp)+

section \<open>The Nop Invariant\<close>

text \<open>Local soundness of the pruned choices: whenever some node's frontier
flag is stale, the progress-tracker configuration is a @{const propagate_all}
fixpoint; frontier reads at stale nodes deliver exactly what the node already
knows (the continuation is the operator itself); and progress writes without
progress are self-loops.\<close>

definition nop_sound where
  "nop_sound sg op \<longleftrightarrow>
     (\<forall> nid. \<not> upfro sg nid \<longrightarrow> propagate_all (summ sg) (pt_tr sg) = Some (pt_tr sg)) \<and>
     (\<forall> nid op'. \<not> upfro sg nid \<longrightarrow>
        step (Inp (Inl nid) (Inl (Inr (frontier o (\<lambda> p. c_imp (pt_tr sg) (Loc nid (Trg p))))))) op op' \<longrightarrow> op' = op) \<and>
     (\<forall> nid st op'. \<not> has_progress st \<longrightarrow> step (Out (Inl nid) (Inl (Inl st))) op op' \<longrightarrow> op' = op)"

text \<open>@{term "nop_invar P"} states that @{term P} implies local soundness
and is closed under all transition shapes of the (optimized) dataflow wrapper.
The coinduction below is parameterized by any such @{term P}.\<close>

definition nop_invar where
  "nop_invar P \<longleftrightarrow>
     (\<forall> sg op. P sg op \<longrightarrow> nop_sound sg op) \<and>
     (\<forall> sg op op'. P sg op \<longrightarrow> step Tau op op' \<longrightarrow> P sg op') \<and>
     (\<forall> sg op op' nid p x. P sg op \<longrightarrow> step (Inp (Inr (nid, p)) (Inr x)) op op' \<longrightarrow> P sg op') \<and>
     (\<forall> sg op op' nid p x. P sg op \<longrightarrow> step (Out (Inr (nid, p)) (Inr x)) op op' \<longrightarrow> P sg op') \<and>
     (\<forall> sg op op' nid st. P sg op \<longrightarrow> step (Out (Inl nid) (Inl (Inl st))) op op' \<longrightarrow> has_progress st \<longrightarrow>
        P (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op') \<and>
     (\<forall> sg op op' nid conf'. P sg op \<longrightarrow> upfro sg nid \<longrightarrow> propagate_all (summ sg) (pt_tr sg) = Some conf' \<longrightarrow>
        step (Inp (Inl nid) (Inl (Inr (frontier o (\<lambda> p. c_imp conf' (Loc nid (Trg p))))))) op op' \<longrightarrow>
        P (sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr>) op')"

lemma nop_soundD_propagate:
  "nop_sound sg op \<Longrightarrow> \<not> upfro sg nid \<Longrightarrow> propagate_all (summ sg) (pt_tr sg) = Some (pt_tr sg)"
  unfolding nop_sound_def by blast

lemma nop_soundD_read_frontier:
  "nop_sound sg op \<Longrightarrow> \<not> upfro sg nid \<Longrightarrow>
   step (Inp (Inl nid) (Inl (Inr (frontier o (\<lambda> p. c_imp (pt_tr sg) (Loc nid (Trg p))))))) op op' \<Longrightarrow>
   op' = op"
  unfolding nop_sound_def by blast

lemma nop_soundD_write_progress:
  "nop_sound sg op \<Longrightarrow> \<not> has_progress st \<Longrightarrow> step (Out (Inl nid) (Inl (Inl st))) op op' \<Longrightarrow> op' = op"
  unfolding nop_sound_def by blast

lemma nop_invarD_sound:
  assumes "nop_invar P" and "P sg op"
  shows "nop_sound sg op"
  using assms(1)[unfolded nop_invar_def, THEN conjunct1, rule_format, OF assms(2)] .

lemma nop_invarD_Tau:
  assumes "nop_invar P" and "P sg op" and "step Tau op op'"
  shows "P sg op'"
  using assms(1)[unfolded nop_invar_def, THEN conjunct2, THEN conjunct1, rule_format,
    OF assms(2) assms(3)] .

lemma nop_invarD_Inp:
  assumes "nop_invar P" and "P sg op" and "step (Inp (Inr (nid, p)) (Inr x)) op op'"
  shows "P sg op'"
  using assms(1)[unfolded nop_invar_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
    rule_format, OF assms(2) assms(3)] .

lemma nop_invarD_Out:
  assumes "nop_invar P" and "P sg op" and "step (Out (Inr (nid, p)) (Inr x)) op op'"
  shows "P sg op'"
  using assms(1)[unfolded nop_invar_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
    THEN conjunct1, rule_format, OF assms(2) assms(3)] .

lemma nop_invarD_progress:
  assumes "nop_invar P" and "P sg op" and "step (Out (Inl nid) (Inl (Inl st))) op op'"
    and "has_progress st"
  shows "P (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op'"
  using assms(1)[unfolded nop_invar_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
    THEN conjunct2, THEN conjunct1, rule_format, OF assms(2) assms(3) assms(4)] .

lemma nop_invarD_frontier:
  assumes "nop_invar P" and "P sg op" and "upfro sg nid"
    and "propagate_all (summ sg) (pt_tr sg) = Some conf'"
    and "step (Inp (Inl nid) (Inl (Inr (frontier o (\<lambda> p. c_imp conf' (Loc nid (Trg p))))))) op op'"
  shows "P (sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr>) op'"
  using assms(1)[unfolded nop_invar_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
    THEN conjunct2, THEN conjunct2, rule_format, OF assms(2) assms(3) assms(4) assms(5)] .

section \<open>Weak Bisimilarity of the Optimized and Plain Operators\<close>

text \<open>The plain wrapper runs on the truncation of the optimized wrapper's
subgraph: the two agree on all fields except the @{const upfro} bookkeeping,
which only the optimized wrapper maintains.\<close>

lemma subgraph_truncate_simps[simp]:
  "pt_tr (subgraph.truncate sgo) = pt_tr sgo"
  "nxt (subgraph.truncate sgo) = nxt sgo"
  "summ (subgraph.truncate sgo) = summ sgo"
  "subgraph.truncate (sgo\<lparr> pt_tr := c \<rparr>) = subgraph.truncate sgo \<lparr> pt_tr := c \<rparr>"
  "subgraph.truncate (sgo\<lparr> upfro := u \<rparr>) = subgraph.truncate sgo"
  by (simp_all add: subgraph.truncate_def)

lemma dataflow_opt_op_sim1:
  assumes inv: "nop_invar P"
    and Pop: "P sg op"
    and stp: "step io (dataflow_opt_op sg op) op1'"
  shows "\<exists> sg' op''. wstep io (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg') op'') \<and>
     op1' = dataflow_opt_op sg' op'' \<and> P sg' op''"
  using stp
proof (cases rule: step_dataflow_opt_op_elim)
  case (read_data nid p op'' x)
  have s2: "step (Inp (nid, p) x) (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg) op'')"
    using read_data(3) by blast
  have P': "P sg op''"
    by (rule nop_invarD_Inp[OF inv Pop read_data(3)])
  show ?thesis
    unfolding read_data(1)
    using s2 P' read_data(2) by blast
next
  case (write_data nid p op'' x)
  have s2: "step (Out (nid, p) x) (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg) op'')"
    using write_data(3) by blast
  have P': "P sg op''"
    by (rule nop_invarD_Out[OF inv Pop write_data(3)])
  show ?thesis
    unfolding write_data(1)
    using s2 P' write_data(2) by blast
next
  case (silent op'')
  have s2: "step Tau (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg) op'')"
    using silent(3) by blast
  have P': "P sg op''"
    by (rule nop_invarD_Tau[OF inv Pop silent(3)])
  show ?thesis
    unfolding silent(1)
    using s2 P' silent(2) by blast
next
  case (write_progress nid op'' st)
  let ?sg' = "sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>"
  have s2: "step Tau (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate ?sg') op'')"
    by (rule step_Tau_dataflow_op_Out_Inl_intro[OF write_progress(4)]) simp
  have P': "P ?sg' op''"
    by (rule nop_invarD_progress[OF inv Pop write_progress(4) write_progress(2)])
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
  have imp_eq: "imp_fron = (\<lambda> p. c_imp conf' (Loc nid (Trg p)))"
    unfolding read_frontier(5) read_frontier(4) by simp
  have step0: "step (Inp (Inl nid) (Inl (Inr (frontier o (\<lambda> p. c_imp conf' (Loc nid (Trg p))))))) op op''"
    using read_frontier(7) unfolding imp_eq .
  have prop2: "propagate_all (summ (subgraph.truncate sg)) (pt_tr (subgraph.truncate sg)) = Some conf'"
    using read_frontier(3) by simp
  have s2: "step Tau (dataflow_op (subgraph.truncate sg) op) (dataflow_op (subgraph.truncate sg \<lparr> pt_tr := conf' \<rparr>) op'')"
    by (rule step_Tau_dataflow_op_Inp_Inl_intro[OF step0 prop2 refl]) simp
  have P': "P sg' op''"
    unfolding read_frontier(4)
    by (rule nop_invarD_frontier[OF inv Pop read_frontier(2) read_frontier(3) step0])
  have trunc: "subgraph.truncate sg \<lparr> pt_tr := conf' \<rparr> = subgraph.truncate sg'"
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
  assumes inv: "nop_invar P"
    and Pop: "P sg op"
    and stp: "step io (dataflow_op (subgraph.truncate sg) op) op2'"
  shows "\<exists> sg' op''. wstep io (dataflow_opt_op sg op) (dataflow_opt_op sg' op'') \<and>
     op2' = dataflow_op (subgraph.truncate sg') op'' \<and> P sg' op''"
  using stp
proof (cases rule: step_dataflow_op_elim')
  case (read_data nid p op'' x)
  have s1: "step (Inp (nid, p) x) (dataflow_opt_op sg op) (dataflow_opt_op sg op'')"
    using read_data(3) by blast
  have P': "P sg op''"
    by (rule nop_invarD_Inp[OF inv Pop read_data(3)])
  show ?thesis
    unfolding read_data(1)
    using s1 P' read_data(2) by blast
next
  case (write_data nid p op'' x)
  have s1: "step (Out (nid, p) x) (dataflow_opt_op sg op) (dataflow_opt_op sg op'')"
    using write_data(3) by blast
  have P': "P sg op''"
    by (rule nop_invarD_Out[OF inv Pop write_data(3)])
  show ?thesis
    unfolding write_data(1)
    using s1 P' write_data(2) by blast
next
  case (silent op'')
  have s1: "step Tau (dataflow_opt_op sg op) (dataflow_opt_op sg op'')"
    using silent(3) by blast
  have P': "P sg op''"
    by (rule nop_invarD_Tau[OF inv Pop silent(3)])
  show ?thesis
    unfolding silent(1)
    using s1 P' silent(2) by blast
next
  case (write_progress nid op'' st)
  show ?thesis
  proof (cases "has_progress st")
    case True
    let ?sg' = "sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>"
    have s1: "step Tau (dataflow_opt_op sg op) (dataflow_opt_op ?sg' op'')"
      by (rule step_Tau_dataflow_opt_op_Out_Inl_intro[OF write_progress(3) True refl])
    have P': "P ?sg' op''"
      by (rule nop_invarD_progress[OF inv Pop write_progress(3) True])
    have eq2: "subgraph.truncate sg \<lparr> pt_tr := change_multiplicities (summ (subgraph.truncate sg)) (extract_progress nid (nxt (subgraph.truncate sg)) st) (pt_tr (subgraph.truncate sg)) \<rparr> = subgraph.truncate ?sg'"
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
      by (rule nop_soundD_write_progress[OF nop_invarD_sound[OF inv Pop] False write_progress(3)])
    have eq2: "subgraph.truncate sg \<lparr> pt_tr := change_multiplicities (summ (subgraph.truncate sg)) (extract_progress nid (nxt (subgraph.truncate sg)) st) (pt_tr (subgraph.truncate sg)) \<rparr> = subgraph.truncate sg"
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
    let ?sg' = "sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr>"
    have prop1: "propagate_all (summ sg) (pt_tr sg) = Some conf'"
      using read_frontier(2) by simp
    have imp_eq: "imp_fron = (\<lambda> p. c_imp conf' (Loc nid (Trg p)))"
      unfolding read_frontier(4) read_frontier(3) by simp
    have step0: "step (Inp (Inl nid) (Inl (Inr (frontier o (\<lambda> p. c_imp conf' (Loc nid (Trg p))))))) op op''"
      using read_frontier(6) unfolding imp_eq .
    have s1: "step Tau (dataflow_opt_op sg op) (dataflow_opt_op ?sg' op'')"
      by (rule step_Tau_dataflow_opt_op_Inp_Inl_intro[OF step0 True prop1 refl]) simp
    have P': "P ?sg' op''"
      by (rule nop_invarD_frontier[OF inv Pop True prop1 step0])
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
      by (rule nop_invarD_sound[OF inv Pop])
    have fix1: "propagate_all (summ sg) (pt_tr sg) = Some (pt_tr sg)"
      by (rule nop_soundD_propagate[OF sound False])
    have conf'_eq: "conf' = pt_tr sg"
      using read_frontier(2) fix1 by simp
    have imp_eq: "imp_fron = (\<lambda> p. c_imp (pt_tr sg) (Loc nid (Trg p)))"
      unfolding read_frontier(4) read_frontier(3) by (simp add: conf'_eq)
    have step0: "step (Inp (Inl nid) (Inl (Inr (frontier o (\<lambda> p. c_imp (pt_tr sg) (Loc nid (Trg p))))))) op op''"
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

lemma dataflow_opt_op_wbisim:
  assumes inv: "nop_invar P"
    and Pop: "P sg op"
  shows "dataflow_opt_op sg op \<approx> dataflow_op (subgraph.truncate sg) op"
proof -
  define R where "R = (\<lambda> op1 op2. \<exists> sg op.
     op1 = dataflow_opt_op sg op \<and> op2 = dataflow_op (subgraph.truncate sg) op \<and> P sg op)"
  have init: "R (dataflow_opt_op sg op) (dataflow_op (subgraph.truncate sg) op)"
    unfolding R_def using Pop by blast
  have sim1: "\<And> opa opb io opa'. R opa opb \<Longrightarrow> step io opa opa' \<Longrightarrow>
     \<exists> opb'. wstep io opb opb' \<and> \<W> R opa' opb'"
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
    then show "\<exists> opb'. wstep io opb opb' \<and> \<W> R opa' opb'"
      using **(1) unfolding *(2) by (blast intro: wbcr_base)
  qed
  have sim2: "\<And> opa opb io opb'. R opa opb \<Longrightarrow> step io opb opb' \<Longrightarrow>
     \<exists> opa'. wstep io opa opa' \<and> \<W> R opa' opb'"
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
    then show "\<exists> opa'. wstep io opa opa' \<and> \<W> R opa' opb'"
      using **(1) unfolding *(1) by (blast intro: wbcr_base)
  qed
  show ?thesis
    by (rule wbisim_coinduct[OF init sim1 sim2])
qed

section \<open>Compilation Entry Points\<close>

definition "init_subgraph_opt summary =
   \<lparr> pt_tr = init_conf summary,
   nxt = graph_to_nxt summary,
   summ = summary, upfro = (\<lambda> _. True) \<rparr>"

lemma truncate_init_subgraph_opt[simp]:
  "subgraph.truncate (init_subgraph_opt summary) = init_subgraph summary"
  by (simp add: init_subgraph_opt_def init_subgraph_def subgraph.truncate_def)

definition "compile_dataflow_opt chns dt = (let summary = antichain_from_list oo (dataflow_tree_to_graph dt) in
                                    let op = dataflow_tree_to_operator chns dt in
                                    let sg = init_subgraph_opt summary in
                                    dataflow_opt_op sg op)"

corollary dataflow_opt_op_wbisim_start:
  assumes "nop_invar P" and "P (init_subgraph_opt summary) op"
  shows "dataflow_opt_op (init_subgraph_opt summary) op \<approx> dataflow_op (init_subgraph summary) op"
  using dataflow_opt_op_wbisim[OF assms] by simp

corollary compile_dataflow_opt_wbisim:
  assumes "nop_invar P"
    and "P (init_subgraph_opt (antichain_from_list oo (dataflow_tree_to_graph dt)))
         (dataflow_tree_to_operator chns dt)"
  shows "compile_dataflow_opt chns dt \<approx> compile_dataflow chns dt"
  unfolding compile_dataflow_opt_def compile_dataflow_def Let_def
  by (rule dataflow_opt_op_wbisim_start[OF assms])

corollary compile_dataflow_opt_wtraces:
  assumes "nop_invar P"
    and "P (init_subgraph_opt (antichain_from_list oo (dataflow_tree_to_graph dt)))
         (dataflow_tree_to_operator chns dt)"
  shows "compile_dataflow_opt chns dt \<equiv>\<^sub>t compile_dataflow chns dt"
  by (rule wbisim_wtraces[OF compile_dataflow_opt_wbisim[OF assms]])

end
