theory Mset_Op

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.CSet_LList_Impl
  "../Lib/LList_Haskell_Setup"
  "../Lib/Operators_Utils"
  "../Lib/Cmset_Utils"
begin

section \<open>The Mset Operator\<close>

text \<open>The mset_op definition and introduction rules for its (weak) steps.\<close>

abbreviation eval_mset_op_aux where
  \<open>eval_mset_op_aux b S S' op aux \<equiv> (case aux of
    Inl op \<Rightarrow> (case op of
      Write op p x \<Rightarrow> Silent (b (cminsert (p, x) S) S' op)
    | Silent op \<Rightarrow> Silent (b S S' op)
    | Read _ _ \<Rightarrow> Code.abort (STR ''Mset_op can only output'') (\<lambda> _. \<oslash>))
  | Inr (p, x) \<Rightarrow> Write (b S (cminsert (p, x) S') op) p x)\<close>

corec mset_op :: \<open>('o \<times> 'd) cmset \<Rightarrow> ('o \<times> 'd) cmset \<Rightarrow> ('i, 'o, 'd) op \<Rightarrow> ('i, 'o, 'd) op\<close> where
  \<open>mset_op S S' op = Choice (cimage (eval_mset_op_aux mset_op S S' op)
     (cUn (cimage Inl (choices op)) (cimage Inr (cset_of_cmset (S - S')))))\<close>

lemma mset_op_code:
  \<open>mset_op S S' op = Choice (cUn
  (cimage (\<lambda>op. case op of
      Write op p x \<Rightarrow> Silent (mset_op (cminsert (p, x) S) S' op)
    | Silent op \<Rightarrow> Silent (mset_op S S' op)
    | Read _ _ \<Rightarrow> Code.abort (STR ''Mset_op can only output'') (\<lambda> _. \<oslash>))
    (choices op))
  (cimage (\<lambda>(p, x). Write (mset_op S (cminsert (p, x) S') op) p x) (cset_of_cmset (S - S'))))\<close>
  by (subst mset_op.code) force

lemma step_mset_op_elim:
  assumes \<open>step io (mset_op S S' op) op'\<close>
  obtains p x where \<open>io = Out p x\<close> \<open>in_cmset (p, x) (S - S')\<close>
    \<open>op' = mset_op S (cminsert (p, x) S') op\<close>
  | op'' where \<open>io = Tau\<close> \<open>step Tau op op''\<close> \<open>op' = mset_op S S' op''\<close>
  | p x op'' where \<open>io = Tau\<close> \<open>step (Out p x) op op''\<close> \<open>op' = mset_op (cminsert (p, x) S) S' op''\<close>
  using assms cin.rep_eq
  by (atomize_elim, subst (asm) mset_op.code) (auto del: disjCI split: op.splits; fastforce)

lemma step_mset_op_intro_Out[intro]:
  \<open>io = Out p x \<Longrightarrow> in_cmset (p, x) (S - S') \<Longrightarrow> op' = mset_op S (cminsert (p, x) S') op \<Longrightarrow>
  step io (mset_op S S' op) op'\<close>
  using cin.rep_eq by (subst mset_op_code) fastforce

lemma step_mset_op_intro_Tau_1[intro]:
  \<open>step (Out p x) op op'' \<Longrightarrow> io = Tau \<Longrightarrow> op' = mset_op (cminsert (p, x) S) S' op'' \<Longrightarrow>
  step io (mset_op S S' op) op'\<close>
  by (subst mset_op_code) (erule step_choicesE; fastforce)

lemma step_set_op_intro_Tau_2[intro]:
  \<open>io = Tau \<Longrightarrow> step Tau op op'' \<Longrightarrow> op' = mset_op S S' op'' \<Longrightarrow> step io (mset_op S S' op) op'\<close>
  by (subst mset_op_code) (erule step_choicesE; fastforce)

lemma step_Taus_mset_op[intro]:
  \<open>(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow> op'' = mset_op S S' op' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (mset_op S S' op) op''\<close>
  by (induction op rule: converse_rtranclp_induct)
    (clarsimp, metis converse_rtranclp_into_rtranclp step_set_op_intro_Tau_2)

lemma step_n_Taus_mset_op[intro]:
  \<open>(step Tau ^^ n) op op' \<Longrightarrow> op'' = mset_op S S' op' \<Longrightarrow> (step Tau ^^ n) (mset_op S S' op) op''\<close>
  by (induction n arbitrary: op)
    (simp, metis (no_types, opaque_lifting) relcompp.cases relpowp_Suc_I2 relpowp_Suc_left
      step_set_op_intro_Tau_2)

lemma step_mset_op_steps_Out_intro[intro]:
  \<open>steps (map (Out p) xs) op op'' \<Longrightarrow> n = length xs \<Longrightarrow>
  op' = mset_op (cmset_of_list (map (Pair p) xs) + S) S' op'' \<Longrightarrow>
  (step Tau ^^ n) (mset_op S S' op) op'\<close>
proof (induction xs arbitrary: n op S)
  case (Cons x xs n op S)
  then obtain op''' m where op''': \<open>step (Out p x) op op'''\<close> \<open>steps (map (Out p) xs) op''' op''\<close>
    and m: \<open>n = Suc m\<close> by auto
  have \<open>op' = mset_op (cmset_of_list (map (Pair p) xs) + cminsert (p, x) S) S' op''\<close>
    using Cons.prems(3) cmset_of_list_Cons cminsert_plus_left cminsert_plus_right list.map(2)
    by metis
  then have \<open>(step Tau ^^ m) (mset_op (cminsert (p, x) S) S' op''') op'\<close>
    using Cons.IH[OF op'''(2)] Cons.prems(2) m by auto
  then show ?case using op'''(1) m relpowp_Suc_I2 step_mset_op_intro_Tau_1 by metis
qed simp

lemma mset_op_not_step_Inp[simp]:
  \<open>\<not>step (Inp p x) (mset_op S S' op) op'\<close>
  using step_mset_op_elim by blast

lemma step_taus_mset_op_elim:
  assumes \<open>(step Tau)\<^sup>*\<^sup>* (mset_op S S' op) op'\<close>
  obtains op'' xs where \<open>wsteps (map (case_prod VOut) xs) op op''\<close>
    \<open>op' = mset_op (cmset_of_list xs + S) S' op''\<close>
proof (atomize_elim, insert assms, induction \<open>mset_op S S' op\<close> arbitrary: op S
    rule: converse_rtranclp_induct)
  case base
  then show ?case by (auto intro!: exI[of _ Nil])
next
  case (step op'' op S)
  consider (Tau) op''' where \<open>step Tau op op'''\<close> \<open>op'' = mset_op S S' op'''\<close>
    | (Out) p x op''' where \<open>step (Out p x) op op'''\<close> \<open>op'' = mset_op (cminsert (p, x) S) S' op'''\<close>
    using step_mset_op_elim[OF step(1)] IO.simps(8) by metis
  then show ?case
  proof cases
    case Tau
    then show ?thesis using step by fast
  next
    case Out
    then obtain xs op'''' where xs_op'''': \<open>wsteps (map (case_prod VOut) xs) op''' op''''\<close>
      \<open>op' = mset_op (cmset_of_list xs + cminsert (p, x) S) S' op''''\<close> using step(3) by blast
    then have \<open>wsteps (map (case_prod VOut) ((p, x) # xs)) op op''''\<close> using Out(1) by auto
    moreover have \<open>op' = mset_op (cmset_of_list ((p, x) # xs) + S) S' op''''\<close>
      using xs_op''''(2) cmset_of_list_Cons cminsert_plus_left cminsert_plus_right by metis
    ultimately show ?thesis by blast
  qed
qed

lemma wstep_mset_op_elim:
  assumes \<open>wstep io (mset_op S S' op) op'\<close>
  obtains (Output) op'' op''' xs ys p x where \<open>io = Out p x\<close>
    \<open>wsteps (map (case_prod VOut) xs) op op''\<close>
    \<open>in_cmset (p, x) (cmset_of_list xs + S - S')\<close>
    \<open>wsteps (map (case_prod VOut) ys) op'' op'''\<close>
    \<open>op' = mset_op (cmset_of_list (xs @ ys) + S) (cminsert (p, x) S') op'''\<close>
  | (Silent) op'' op''' xs ys where \<open>io = Tau\<close>
    \<open>wsteps (map (case_prod VOut) xs) op op''\<close>
    \<open>wsteps (map (case_prod VOut) ys) op'' op'''\<close>
    \<open>op' = mset_op (cmset_of_list (xs @ ys) + S) S' op'''\<close>
proof -
  obtain op1 op2 where op1_op2: \<open>(step Tau)\<^sup>*\<^sup>* (mset_op S S' op) op1\<close> \<open>estep io op1 op2\<close>
    \<open>(step Tau)\<^sup>*\<^sup>* op2 op'\<close> using assms unfolding wstep_def by blast
  then obtain op'' xs where op''_xs: \<open>wsteps (map (case_prod VOut) xs) op op''\<close>
    \<open>op1 = mset_op (cmset_of_list xs + S) S' op''\<close> using step_taus_mset_op_elim by meson
  then show ?thesis
  proof (cases io)
    case (Inp p x)
    then show ?thesis using op1_op2(2) op''_xs by force
  next
    case (Out p x)
    then have \<open>step (Out p x) op1 op2\<close> using op1_op2(2) by simp
    then have p_x: \<open>in_cmset (p, x) (cmset_of_list xs + S - S')\<close>
      and \<open>op2 = mset_op (cmset_of_list xs + S) (cminsert (p, x) S') op''\<close>
      using op''_xs step_mset_op_elim by blast+
    then obtain op''' ys where \<open>wsteps (map (case_prod VOut) ys) op'' op'''\<close>
      \<open>op' = mset_op (cmset_of_list (xs @ ys) + S) (cminsert (p, x) S') op'''\<close> using op1_op2(3)
        step_taus_mset_op_elim add.assoc add.commute cmset_of_list_append by (smt (verit))
    then show ?thesis using op''_xs(1) p_x Output[OF Out] by blast
  next
    case Tau
    then consider \<open>op1 = op2\<close> | \<open>step Tau op1 op2\<close> using op1_op2(2) by fastforce
    then consider \<open>op1 = op2\<close>
      | op''' where \<open>step Tau op'' op'''\<close> \<open>op2 = mset_op (cmset_of_list xs + S) S' op'''\<close>
      | p x op''' where \<open>step (Out p x) op'' op'''\<close>
        \<open>op2 = mset_op (cminsert (p, x) (cmset_of_list xs + S)) S' op'''\<close>
      using op1_op2(2) op''_xs(2) step_mset_op_elim IO.simps(8) by metis
    then show ?thesis
    proof cases
      case 1
      then obtain op''' ys where \<open>wsteps (map (case_prod VOut) ys) op'' op'''\<close>
        \<open>op' = mset_op (cmset_of_list (xs @ ys) + S) S' op'''\<close> using op1_op2(3) op''_xs
          step_taus_mset_op_elim add.assoc add.commute cmset_of_list_append by (smt (verit))
      then show ?thesis using op''_xs(1) Silent[OF Tau] by blast
    next
      case 2
      then obtain op'''' ys where \<open>wsteps (map (case_prod VOut) ys) op''' op''''\<close>
        \<open>op' = mset_op (cmset_of_list (xs @ ys) + S) S' op''''\<close> using op1_op2(3) op''_xs
          step_taus_mset_op_elim add.assoc add.commute cmset_of_list_append by (smt (verit))
      then show ?thesis using op''_xs(1) 2 Silent[OF Tau] by blast
    next
      case 3
      then obtain op'''' ys where \<open>wsteps (map (case_prod VOut) ys) op''' op''''\<close>
        \<open>op' = mset_op (cmset_of_list (xs @ (p, x) # ys) + S) S' op''''\<close> using op1_op2(3) op''_xs
          step_taus_mset_op_elim add.assoc add.commute cmset_of_list_append cmset_of_list_Cons
          cminsert_plus_right by (smt (verit, ccfv_threshold))
      moreover from this have \<open>wsteps (map (case_prod VOut) ((p, x) # ys)) op'' op''''\<close>
        using 3(1) by auto
      ultimately show ?thesis using op''_xs(1) Silent[OF Tau] by blast
    qed
  qed
qed

section \<open>Output Traces\<close>

text \<open>Weak-step lemmas pushing outputs through sequences of silent steps.\<close>

lemma wsteps_map_VOut_step_taus_mset_op:
  \<open>wsteps (map (case_prod VOut) xs) op op' \<Longrightarrow> op'' = mset_op (cmset_of_list xs + S) S' op' \<Longrightarrow>
  (step Tau)\<^sup>*\<^sup>* (mset_op S S' op) op''\<close>
proof (induction \<open>map (case_prod VOut) xs\<close> arbitrary: xs op S rule: wsteps.induct)
  case (2 vio vios)
  then obtain p x xs' op''' where p_x_xs': \<open>xs = (p, x) # xs'\<close>
    and op''': \<open>wsteps [VOut p x] op op'''\<close> \<open>wsteps (map (case_prod VOut) xs') op''' op'\<close>
    by fastforce
  moreover have \<open>op'' = mset_op (cmset_of_list xs' + cminsert (p, x) S) S' op'\<close>
    using 2(4) p_x_xs' cminsert_plus_left cminsert_plus_right cmset_of_list_Cons by metis
  ultimately have \<open>(step Tau)\<^sup>*\<^sup>* (mset_op (cminsert (p, x) S) S' op''') op''\<close>
    using 2(1,2) op''' by blast
  moreover have \<open>(step Tau)\<^sup>*\<^sup>* (mset_op S S' op) (mset_op (cminsert (p, x) S) S' op''')\<close>
  proof -
    have \<open>wstep (Out p x) op op'''\<close> using op'''(1) by (fastforce simp add: wstep_def)
    then obtain op1 op2 where op1_op2: \<open>(step Tau)\<^sup>*\<^sup>* op op1\<close> \<open>step (Out p x) op1 op2\<close>
      \<open>(step Tau)\<^sup>*\<^sup>* op2 op'''\<close> using wstep_def estep.simps(3) relcomppE by metis
    then show ?thesis using step_Taus_mset_op step_mset_op_intro_Tau_1 rtranclp.intros(2)
        rtranclp_trans by (metis (no_types, opaque_lifting))
  qed
  ultimately show ?case by simp
qed auto

lemma wsteps_map_VOut_wstep_out_mset_op:
  \<open>wsteps (map (case_prod VOut) xs) op op' \<Longrightarrow> in_cmset (p, x) (cmset_of_list xs + S - S') \<Longrightarrow>
  wstep (Out p x) (mset_op S S' op) (mset_op (cmset_of_list xs + S) (cminsert (p, x) S') op')\<close>
  using wsteps_map_VOut_step_taus_mset_op wstep_trans(1) step_mset_op_intro_Out by metis

coinductive mset_op_trace where
  \<open>\<forall>op' xs. wsteps (map (case_prod VOut) xs) op op' \<longrightarrow> cmset_of_list xs + S - S' = cmempty \<Longrightarrow>
  mset_op_trace S S' op LNil\<close>
| \<open>wsteps (map (case_prod VOut) xs) op op' \<Longrightarrow> in_cmset (p, x) (cmset_of_list xs + S - S') \<Longrightarrow>
  mset_op_trace (cmset_of_list xs + S) (cminsert (p, x) S') op' vios \<Longrightarrow>
  mset_op_trace S S' op (LCons (VOut p x) vios)\<close>

lemma mset_op_trace_LNil_cmempty:
  assumes \<open>mset_op_trace S S' op LNil\<close>
  shows \<open>S - S' = cmempty\<close>
proof -
  have \<open>\<forall>op' xs. wsteps (map (case_prod VOut) xs) op op' \<longrightarrow> cmset_of_list xs + S - S' = cmempty\<close>
    using assms mset_op_trace.cases by blast
  moreover have \<open>wsteps [] op op\<close> by fastforce
  ultimately show ?thesis using cmempty_plus(1) cmset_of_list_Nil list.map(1) by metis
qed

lemma wstep_exec_VOut_sound:
  "(VOut p x, op') |\<in>| wsteps_exec op \<Longrightarrow>
   wstep (Out p x) op op'"
  unfolding wsteps_exec_def
  apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
  subgoal premises prems for n
    using prems(2-) apply -
    apply (induct n arbitrary: op op')
    subgoal for op op'
      apply (cases op; (auto simp flip: cin.rep_eq))
      done
    subgoal for n op op'
      apply (cases op; (auto simp flip: cin.rep_eq))
      apply (metis WSC io_of_vio.simps(2))
      done
    done
  done

lemma wstep_exec_VInp_sound:
  "(VInp p x, op') |\<in>| wsteps_exec op \<Longrightarrow>
   wstep (Inp p x) op op'"
  unfolding wsteps_exec_def
  apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
  subgoal premises prems for n
    using prems(2-) apply -
    apply (induct n arbitrary: op op')
    subgoal for op op'
      apply (cases op; (auto simp flip: cin.rep_eq))
      done
    subgoal for n op op'
      apply (cases op; (auto simp flip: cin.rep_eq))
      apply (metis WSC io_of_vio.simps(1))
      done
    done
  done


lemma step_exec_VOut_completeness:
  "step io op op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   (VOut p x, op') |\<in>| wsteps_exec op"
  apply (induct op' rule: step.induct)
     apply (simp_all add: wsteps_exec_def flip: cin.rep_eq)
   apply simp
  subgoal for op ops io op'
    apply safe
    subgoal for n
      apply (rule cBexI[of _ "Suc n"])
       apply auto
      done
    done
  done

lemma step_exec_VInp_completeness:
  "step io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   \<exists> f. (VInp p undefined, f undefined) |\<in>| wsteps_exec op"
  apply (induct op' rule: step.induct)
     apply (simp_all add: wsteps_exec_def flip: cin.rep_eq)
   apply simp
  apply fast
  subgoal for op ops io op'
    apply safe
    subgoal for f n
      apply (rule exI[of _ f])
      apply (rule cBexI[of _ "Suc n"])
       apply auto
      done
    done
  done

lemma step_Tau_exec_completeness:
  "step io op op' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   (vio, op'') |\<in>| wsteps_exec op' \<Longrightarrow>
   (vio, op'') |\<in>| wsteps_exec op"
  unfolding wsteps_exec_def
  apply (induct op' rule: step.induct)
     apply (auto simp add: simp flip: cin.rep_eq )
  subgoal for op n
    apply (rule cBexI[of _ "Suc n"])
     apply auto
    done
  subgoal for op ops op' n n'
    apply (rule cBexI[of _ "Suc n"])
     apply auto
    done
  done

lemma wstep_exec_VOut_completeness:
  "wstep (Out p x) op op' \<Longrightarrow>
   \<exists> op'. (VOut p x, op') |\<in>| wsteps_exec op"
  unfolding wstep_def
  apply (simp flip: cin.rep_eq)
  apply (elim relcomppE)
  subgoal premises prems for op' op''
    using prems(1,2) apply -
    apply (drule step_exec_VOut_completeness)
     apply (rule refl)
    unfolding wsteps_exec_def
    apply (induct op rule: converse_rtranclp_induct)
    subgoal
      by (auto simp add: wsteps_exec_def simp flip: cin.rep_eq)
    subgoal for op1 op2
      apply (drule meta_mp)
       apply assumption
      apply safe
      apply (drule step_Tau_exec_completeness)
        apply simp
      unfolding wsteps_exec_def
       apply simp
       apply fast
      apply (auto del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits)[1]
      done
    done
  done

lemma wstep_exec_VInp_completeness:
  "wstep (Inp p x) op op' \<Longrightarrow>
  \<exists> f. (VInp p undefined, f undefined) |\<in>| wsteps_exec op"
  unfolding wstep_def
  apply (simp flip: cin.rep_eq)
  apply (elim relcomppE)
  subgoal premises prems for op' op''
    using prems(1,2) apply -
    apply (drule step_exec_VInp_completeness)
     apply (rule refl)
    unfolding wsteps_exec_def
    apply (induct op rule: converse_rtranclp_induct)
    subgoal
      by (auto simp add: wsteps_exec_def simp flip: cin.rep_eq)
    subgoal for op1 op2
      apply (drule meta_mp)
       apply assumption
      apply safe
      apply (drule step_Tau_exec_completeness)
        apply simp
      unfolding wsteps_exec_def
       apply simp
       apply fast
      apply (auto del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits)[1]
      done
    done
  done

lemma wfinished_cis_empty_wsteps_exec:
  "wfinished op \<Longrightarrow> cis_empty (wsteps_exec op)"
  unfolding cis_empty_def wfinished_no_wstep
  apply (auto del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
  subgoal for vio op'
    apply (cases vio)
    subgoal
      apply hypsubst_thin
      apply (drule wstep_exec_VInp_sound)
      apply (metis io_of_vio.simps(1))
      done
    subgoal
      apply hypsubst_thin
      apply (drule wstep_exec_VOut_sound)
      apply (metis io_of_vio.simps(2))
      done
    done
  done

lemma cis_empty_wsteps_exec_wfinished:
  "cis_empty (wsteps_exec op) \<longleftrightarrow> wfinished op"
  apply (rule iffI)
  subgoal
  unfolding cis_empty_def wfinished_no_wstep
  apply (auto del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)[1]
   apply (metis cemptyE io_of_vio_not_Tau(2) vio_of_io.cases wstep_exec_VInp_completeness wstep_exec_VOut_completeness)
  done
  subgoal
    using wfinished_cis_empty_wsteps_exec by auto
  done

lemma wtraced_trace_exec:
  "wtraced op (trace_exec op)"
  apply (coinduction arbitrary: op)
  subgoal for op
    apply simp
    apply (cases "wfinished op")
    subgoal
      apply simp
      apply (rule disjI1)
      apply (subst trace_exec.code)
      apply (clarsimp split: prod.splits)
      using wfinished_cis_empty_wsteps_exec apply fast
      done
    subgoal
      unfolding wfinished_no_wstep
      apply simp
      apply (subst trace_exec.code)
      apply (clarsimp split: prod.splits)
      subgoal for vio a vio' op'
        apply (cases vio')
        subgoal for p x
          unfolding csome_elem_def some_elem_def
          apply (clarsimp del: disjCI simp flip: cin.rep_eq ; hypsubst_thin?)
          apply (intro exI conjI[rotated] disjI1)
            apply (rule refl)
          subgoal
            apply (cases vio; simp; hypsubst_thin?)
            subgoal
              apply (drule wstep_exec_VInp_completeness)
              apply (elim exE)
              apply (rule wstep_exec_VInp_sound)
              apply (rule some_eq_imp[where P="\<lambda> x. x |\<in>| wsteps_exec op"])
               apply auto
              done
            subgoal
              apply (drule wstep_exec_VOut_completeness)
              apply (elim exE)
              apply (rule wstep_exec_VInp_sound)
              apply (rule some_eq_imp[where P="\<lambda> x. x |\<in>| wsteps_exec op"])
               apply auto
              done
            done
          subgoal
            apply (cases vio; simp; hypsubst_thin?)
             apply (metis all_not_cin_conv cis_empty_def wstep_exec_VInp_completeness)
            apply (metis all_not_cin_conv cis_empty_def wstep_exec_VOut_completeness)
            done
          done
        subgoal for p x
          unfolding csome_elem_def some_elem_def
          apply (clarsimp del: disjCI simp flip: cin.rep_eq ; hypsubst_thin?)
          apply (intro exI conjI[rotated] disjI1)
            apply (rule refl)
          subgoal
            apply (cases vio; simp; hypsubst_thin?)
            subgoal
              apply (drule wstep_exec_VInp_completeness)
              apply (elim exE)
              apply (rule wstep_exec_VOut_sound)
              apply (rule some_eq_imp[where P="\<lambda> x. x |\<in>| wsteps_exec op"])
               apply auto
              done
            subgoal
              apply (drule wstep_exec_VOut_completeness)
              apply (elim exE)
              apply (rule wstep_exec_VOut_sound)
              apply (rule some_eq_imp[where P="\<lambda> x. x |\<in>| wsteps_exec op"])
               apply auto
              done
            done
          subgoal
            apply (cases vio; simp; hypsubst_thin?)
             apply (metis all_not_cin_conv cis_empty_def wstep_exec_VInp_completeness)
            apply (metis all_not_cin_conv cis_empty_def wstep_exec_VOut_completeness)
            done
          done
        done
      done
    done
  done

section \<open>Trace Soundness\<close>

text \<open>Outputs of the operator agree with the set semantics.\<close>

lemma mset_op_trace_soundness:
  assumes \<open>VOut p x \<in> lset vios\<close> \<open>mset_op_trace S S' op vios\<close> \<open>\<not>in_cmset (p, x) (S - S')\<close>
  obtains vios' where \<open>VOut p x \<in> lset vios'\<close> \<open>wtraced op vios'\<close>
proof (atomize_elim, insert assms, induction vios arbitrary: op S S' rule: lset_induct)
  case (find vios op S S')
  obtain xs op' where wsteps_xs: \<open>wsteps (map (case_prod VOut) xs) op op'\<close>
    and \<open>in_cmset (p, x) (cmset_of_list xs + S - S')\<close>
    using mset_op_trace.cases[OF find(1)] by blast
  then have p_x: \<open>(p, x) \<in> set xs\<close>
    using in_cmset_plus_minus[OF _ find(2)] by fastforce
  have \<open>wtraced op' (trace_exec op')\<close> using wtraced_trace_exec by blast
  then show ?case using wsteps_xs p_x wsteps_wtraced by force
next
  case (step vio vios op S S')
  obtain p' x' where p'_x': \<open>vio = VOut p' x'\<close>
    using mset_op_trace.cases[OF step.prems(1)] by fastforce
  then obtain xs op' where xs_op': \<open>wsteps (map (case_prod VOut) xs) op op'\<close>
    \<open>in_cmset (p', x') (cmset_of_list xs + S - S')\<close>
    \<open>mset_op_trace (cmset_of_list xs + S) (cminsert (p', x') S') op' vios\<close>
    using mset_op_trace.cases[OF step.prems(1)] by blast
  then show ?case
  proof (cases \<open>(p, x) \<in> set xs\<close>)
    case True
    have \<open>wtraced op' (trace_exec op')\<close> using wtraced_trace_exec by blast
    then show ?thesis using xs_op'(1) True wsteps_wtraced by force
  next
    case False
    then have \<open>\<not>in_cmset (p, x) (cmset_of_list xs + S - S')\<close>
      using in_cmset_plus_minus[OF _ step.prems(2)] by fastforce
    then have \<open>\<not>in_cmset (p, x) (cmset_of_list xs + S - cminsert (p', x') S')\<close>
      using cminsert_is_plus cmset_minus_plus add.commute in_cmset_minus_left by metis
    then obtain vios' where vios': \<open>VOut p x \<in> lset vios'\<close> \<open>wtraced op' vios'\<close>
      using step.IH[OF xs_op'(3)] by blast
    then show ?thesis using wsteps_not_finished_wtraced wtraced_not_LNil_not_wfinished xs_op'(1)
        in_lset_shift_eq llist.set_cases llist.simps(3) by metis
  qed
qed

section \<open>Finished Computations\<close>

text \<open>The wfinished predicate and closure properties.\<close>

lemma wfinished_mset_op_cmempty[intro]:
  assumes \<open>wfinished (mset_op S S' op)\<close>
  shows \<open>S - S' = cmempty\<close>
proof (rule ccontr)
  assume \<open>S - S' \<noteq> cmempty\<close>
  then obtain p x where p_x: \<open>in_cmset (p, x) (S - S')\<close>
    unfolding cmset_alt cmset_eq_iff by fastforce
  then show False using assms step_not_wfinished[of \<open>VOut p x\<close>] step_mset_op_intro_Out by auto
qed

lemma wfinished_mset_op_trace_LNil:
  \<open>wfinished (mset_op S S' op) \<Longrightarrow> mset_op_trace S S' op LNil\<close>
  using wfinished_mset_op_cmempty wsteps_map_VOut_step_taus_mset_op mset_op_trace.intros(1)
    wfinished_step_taus by metis

lemma in_wtraced_in_wsteps:
  "VOut p x \<in> lset ios \<Longrightarrow>
   wtraced op ios \<Longrightarrow>
   (\<forall> vio \<in> lset ios. \<not> is_VInp vio) \<Longrightarrow>
   \<exists> op' xs. wsteps (map (\<lambda>(p, x). VOut p x) xs) op op' \<and> (p, x) \<in> set xs"
  apply (induct ios arbitrary: op rule: lset_induct)
  subgoal for lxs op
    apply (erule wtraced.cases; simp flip: cin.rep_eq; hypsubst_thin)
    subgoal for vio op' op''
      apply (rule exI[of _ op''])
      apply (rule exI[of _ "[(p, x)]"])
      apply auto
      done
    done
  subgoal for x' xs op'
    apply (erule wtraced.cases; simp flip: cin.rep_eq; hypsubst_thin)
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    apply (elim exE conjE)
    subgoal for vio op op'' op''' vios
      apply (cases x'; simp)
      subgoal for p' x'
      apply (rule exI[of _ op'''])
      apply (rule exI[of _ "(p', x') # vios"])
      apply auto
      done
    done
  done
  done

lemma mset_op_trace_trace_exec:
  \<open>mset_op_trace S S' op (trace_exec (mset_op S S' op))\<close>
proof (coinduction arbitrary: op S S')
  case (mset_op_trace op S S')
  show ?case
  proof (cases \<open>cis_empty (wsteps_exec (mset_op S S' op))\<close>)
    case True
    have \<open>wfinished (mset_op S S' op)\<close> using cis_empty_wsteps_exec_wfinished True by blast
    then have \<open>trace_exec (mset_op S S' op) = LNil\<close> using True by (subst trace_exec.code) force
    moreover have \<open>\<forall>op' xs. wsteps (map (\<lambda>(x, y). VOut x y) xs) op op'
  \<longrightarrow> cmset_of_list xs + S - S' = cmempty\<close>
      using \<open>wfinished (mset_op S S' op)\<close> wsteps_map_VOut_step_taus_mset_op by fast
    ultimately show ?thesis by simp
  next
    case False
    then obtain vio op' where vio_op': \<open>(vio, op') = csome_elem (wsteps_exec (mset_op S S' op))\<close>
      \<open>(vio, op') |\<in>| wsteps_exec (mset_op S S' op)\<close>
      using prod.exhaust cis_empty_def some_elem_nonempty bot_cset.rep_eq cin.rep_eq
        csome_elem.rep_eq rcset_inject by metis
    obtain p x where p_x: \<open>vio = VOut p x\<close> using VIO.exhaust wstep_exec_VInp_sound vio_op'(2)
        wstep_mset_op_elim IO.simps(4,6) by (smt (verit, best))
    have \<open>wstep (Out p x) (mset_op S S' op) op'\<close> using wstep_exec_VOut_sound vio_op'(2) p_x by meson
    then obtain op'' op''' xs ys where \<open>wsteps (map (case_prod VOut) xs) op op''\<close>
      and in_cmset_p_x: \<open>in_cmset (p, x) (cmset_of_list xs + S - S')\<close>
      and \<open>wsteps (map (case_prod VOut) ys) op'' op'''\<close>
      and op': \<open>op' = mset_op (cmset_of_list (xs @ ys) + S) (cminsert (p, x) S') op'''\<close>
      using wstep_mset_op_elim IO.inject(2) IO.simps(8) by (smt (verit, best))
    then have \<open>wsteps (map (case_prod VOut) (xs @ ys)) op op'''\<close> by auto
    moreover have \<open>trace_exec (mset_op S S' op) = LCons (VOut p x) (trace_exec op')\<close>
      using False vio_op'(1) p_x by (subst trace_exec.code) (auto split: prod.splits)
    moreover have \<open>in_cmset (p, x) (cmset_of_list (xs @ ys) + S - S')\<close> using in_cmset_p_x
    proof (cases rule: in_cmset_minus_elim)
      case (less n m)
      then show ?thesis using add.assoc add.commute cmcount_less_in_cmset_minus cmcount_plus
          cmset_of_list_append enat_less_enat_plusI by (smt (verit, ccfv_threshold))
    next
      case infinity
      then show ?thesis unfolding cmset_alt cmset_of_list_append cmcount_plus cmcount_minus
        using plus_eq_infty_iff_enat by force
    qed
    ultimately show ?thesis using op' by fast
  qed
qed

section \<open>Trace Completeness\<close>

text \<open>Every specified output is eventually produced by the operator.\<close>

lemma mset_op_trace_completeness:
  assumes \<open>VOut p x \<in> lset vios\<close> \<open>wtraced op (vios :: ('i, 'o, 'd) VIO llist)\<close>
    \<open>\<forall>vio \<in> lset vios. \<not>is_VInp vio\<close> \<open>\<not>in_cmset (p, x) S'\<close>
  obtains vios' :: \<open>('i, 'o, 'd) VIO llist\<close> where \<open>mset_op_trace S S' op vios'\<close>
    \<open>VOut p x \<in> lset vios'\<close>
proof -
  obtain op' xs where op'_xs: \<open>wsteps (map (case_prod VOut) xs) op op'\<close> and \<open>(p, x) \<in> set xs\<close>
    using in_wtraced_in_wsteps[OF assms(1-3)] by blast
  then have \<open>in_cmset (p, x) (cmset_of_list xs + S - S')\<close> using assms(4) cmcount_less_in_cmset_minus
      cmcount_plus cmset_alt iadd_is_0 cmset_cmset_of_list linorder_not_less mem_Collect_eq
      zero_order(2) by (metis (mono_tags, lifting))
  then show ?thesis
    using that mset_op_trace.intros(2)[OF op'_xs] mset_op_trace_trace_exec by fastforce
qed

lemma wtraced_mset_op:
  \<open>wtraced (mset_op S S' op) vios \<longleftrightarrow> mset_op_trace S S' op vios\<close>
proof (rule iffI; coinduction arbitrary: op S S' vios)
  case wtraced
  then show ?case
  proof cases
    case 1
    then show ?thesis using io_of_vio_not_Tau(1) cmset_cmempty empty_iff wfinished_no_wstep
        wstep_mset_op_elim by (smt (verit, best))
  next
    case (2 xs op' p x vios')
    then show ?thesis using io_of_vio.simps(2) wsteps_map_VOut_wstep_out_mset_op by metis
  qed
next
  case mset_op_trace
  then show ?case
  proof cases
    case Nil
    then show ?thesis using wfinished_mset_op_cmempty wfinished_step_taus
        wsteps_map_VOut_step_taus_mset_op by meson
  next
    case (Step vio op' vios')
    then obtain p x where p_x: \<open>vio = VOut p x\<close> using wstep_mset_op_elim io_of_vio_inverse
        io_of_vio_not_Tau(1) vio_of_io.simps(2) by (smt (verit))
    then obtain op'' op''' xs ys where op''_xs: \<open>wsteps (map (case_prod VOut) xs) op op''\<close>
      and in_cmset_p_x: \<open>in_cmset (p, x) (cmset_of_list xs + S - S')\<close>
      and op'''_ys: \<open>wsteps (map (case_prod VOut) ys) op'' op'''\<close>
      and op': \<open>op' = mset_op (cmset_of_list (xs @ ys) + S) (cminsert (p, x) S') op'''\<close>
      using wstep_mset_op_elim Step(2) IO.inject(2) io_of_vio.simps(2) io_of_vio_not_Tau(1)
      by (smt (verit, best))
    then have \<open>wsteps (map (case_prod VOut) (xs @ ys)) op op'''\<close> by auto
    moreover have \<open>in_cmset (p, x) (cmset_of_list (xs @ ys) + S - S')\<close> using in_cmset_p_x
    proof (cases rule: in_cmset_minus_elim)
      case (less n m)
      then show ?thesis using add.assoc add.commute cmcount_less_in_cmset_minus cmcount_plus
          cmset_of_list_append enat_less_enat_plusI by (smt (verit, ccfv_threshold))
    next
      case infinity
      then show ?thesis unfolding cmset_alt cmset_of_list_append cmcount_plus cmcount_minus
        using plus_eq_infty_iff_enat by force
    qed
    ultimately show ?thesis using Step(1,3) op' p_x by force
  qed
qed

end