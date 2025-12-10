theory Set_op

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.CSet_LList_Impl
  "../Timely_Infrastructure"
  "../LList_Haskell_Setup"
begin


abbreviation "eccard S \<equiv> (if cinfinite S then infinity else ccard S)"

corec set_op :: "('a \<times> 'b) cset \<Rightarrow> ('a \<times> 'b) cset \<Rightarrow> ('c, 'a, 'b) op \<Rightarrow> ('c, 'a, 'b) op" where
  "set_op S S' op = choice2
  (Choice (cimage (\<lambda> op. case op of
     Write op p x \<Rightarrow> Silent (set_op (cinsert (p, x) S) S' op) 
   | Silent op \<Rightarrow> Silent (set_op S S' op)
   | Read _ _ \<Rightarrow> Code.abort (STR ''Set_op can only output'') (\<lambda> _. \<oslash>)
   ) (choices op))
   )
  (Choice (cimage (\<lambda> (p, x). Write (set_op S (cinsert (p, x) S') op) p x) (S - S')))"

lemma step_set_op_elim:
  assumes "step io (set_op S S' op) op'"
  obtains p x where "io = Out p x" "(p, x) |\<in>| S" "\<not> (p, x) |\<in>| S'"
    "op' = set_op S (cinsert (p, x) S') op"
  | op'' where "io = Tau" "step Tau op op''" "op' = set_op S S' op''"
  | p x op'' where "io = Tau" "step (Out p x) op op''" "op' = set_op (cinsert (p, x) S) S' op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) set_op.code)
  apply (auto del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
    apply fastforce+
  done

lemma step_set_op_intro_Out[intro]:
  "io = Out p x \<Longrightarrow>
   (p, x) |\<in>| S \<Longrightarrow>
   \<not> (p, x) |\<in>| S' \<Longrightarrow>
   op' = set_op S (cinsert (p, x) S') op \<Longrightarrow>
   step io (set_op S S' op) op'"
  apply (subst set_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply fast
  done

lemma step_set_op_intro_Tau_1[intro]:
  "step (Out p x) op op'' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   op' = set_op (cinsert (p, x) S) S' op'' \<Longrightarrow>
   step io (set_op S S' op) op'"
  apply (subst set_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply (smt (verit) IO.distinct(1,5) IO.inject(2) SC Silent_in_choices_step String.Literal'_def cDiff_cancel cDiff_cinsert2
      cDiff_cinsert_absorb choices_Silent cimage_eqI cinsert_absorb cinsert_cDiff1 cinsert_cDiff_if cinsert_cDiff_single cinsert_commute
      cinsert_not_cempty csingleton_iff internal_case_prod_def op.simps(18) step.simps step_choicesE)
  done

lemma step_set_op_intro_Tau_2[intro]:
  "io = Tau \<Longrightarrow>
   step Tau op op'' \<Longrightarrow>
   op' = set_op S S' op'' \<Longrightarrow>
   step io (set_op S S' op) op'"
  apply (subst set_op.code)
  apply (subst set_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply (metis (no_types, lifting) IO.distinct(5) IO.simps(6) cimageI cinsertI1 op.simps(20) step.simps step_choicesE)
  done


lemma step_Taus_set_op[intro]:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   op'' = set_op S S' op' \<Longrightarrow>
   (step Tau)\<^sup>*\<^sup>* (set_op S S' op) op''"
  apply (induct op arbitrary: S S' rule: converse_rtranclp_induct)
   apply clarsimp+
  apply (metis converse_rtranclp_into_rtranclp step_set_op_intro_Tau_2)
  done

lemma wstep_Out_set_op[intro]:
  "wstep (Out p x) op op' \<Longrightarrow>
   \<not> (p, x) |\<in>| S' \<Longrightarrow>
   op'' = set_op (cinsert (p, x) S) (cinsert (p, x) S') op' \<Longrightarrow>
   wstep (Out p x) (set_op S S' op) op''"
  unfolding wstep_def
  apply (clarsimp  simp flip: cin.rep_eq)
  apply hypsubst_thin+
  apply (intro "relcomppI")
    prefer 3
  apply (rule step_Taus_set_op[rotated])
     apply (rule refl)+
    prefer 3
      apply (rule step_set_op_intro_Out)
  apply (rule refl)
    defer
      defer
      apply (rule refl)
     defer
  apply (rule rtranclp.intros(2)[rotated])
      apply (rule step_set_op_intro_Tau_1)
        apply assumption
  apply simp
      apply (rule refl)
     apply auto
  done

coinductive set_op_trace where
  "S - S' = {||} \<Longrightarrow> wfinished op \<Longrightarrow> set_op_trace S S' op LNil"
|  "wstep (Out p' x') op op' \<Longrightarrow>
    S2 = cinsert (p', x') S1 \<Longrightarrow>
    (p, x) |\<in>| S2 - S' \<Longrightarrow>
    set_op_trace S2 (cinsert (p, x) S') op' lxs \<Longrightarrow>
    set_op_trace S1 S' op (LCons (VOut p x) lxs)"
|  "(p, x) |\<in>| S - S' \<Longrightarrow>
    set_op_trace S (cinsert (p, x) S') op lxs \<Longrightarrow>
    set_op_trace S S' op (LCons (VOut p x) lxs)"

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

lemma set_op_trace_soundness:
  "VOut p x \<in> lset ios \<Longrightarrow>
   set_op_trace S S' op ios \<Longrightarrow>
   \<not> (p, x) |\<in>| (S - S') \<Longrightarrow>
   (\<exists> ios'. wtraced op ios' \<and> VOut p x \<in> lset ios')"
  apply (induct ios arbitrary: S S' op rule: lset_induct)
  subgoal for xs S S'
    apply (erule set_op_trace.cases; simp)
    apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
    subgoal for op'
      using wtraced_trace_exec[of op'] apply -
      apply (intro exI conjI)
       apply (rule wtraced.Step[of "VOut p x"])
        apply simp
       apply auto
      done
    done
  subgoal for x xs S S' op'
    apply (erule set_op_trace.cases; simp; hypsubst)
    subgoal for p' x' op op'' S2 S1 pa xa S''
      apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
      apply (metis wtraced_trace_exec cinsert_iff io_of_vio.simps(2) lset_intros(1,2) prod.simps(1) wtraced.intros(2))
      done
    subgoal for pa xa S S' op''
      apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
      done
    done
  done



lemma wtraced_set_op_trace:
  "wtraced (set_op S S' op) ios \<longleftrightarrow> set_op_trace S S' op ios"
  sorry

corec set_spec_op :: "('a \<times> 'b) cset \<Rightarrow> ('a \<times> 'b) cset \<Rightarrow> ('a, 'a, 'b) op"  where
  "set_spec_op S S' = 
  (Choice (cimage (\<lambda> (p, x). Write (set_spec_op S (cinsert (p, x) S')) p x) (S - S')))"

lemma step_set_spec_op_elim:
  assumes "step io (set_spec_op S S') op'"
  obtains p x where "io = Out p x" "(p, x) |\<in>| S" "\<not> (p, x) |\<in>| S'"
    "op' = set_spec_op S (cinsert (p, x) S')"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) set_spec_op.code)
  apply (auto del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  done

lemma step_set_spec_op_intro_Out[intro!]:
  "io = Out p x \<Longrightarrow>
   (p, x) |\<in>| S \<Longrightarrow>
   \<not> (p, x) |\<in>| S' \<Longrightarrow>
   op' = set_spec_op S (cinsert (p, x) S') \<Longrightarrow>
   step io (set_spec_op S S') op'"
  apply (subst set_spec_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply fast
  done

lemma set_spec_op_no_Tau_step[simp]:
  "\<not> step Tau (set_spec_op S S') op'"
  apply (subst set_spec_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  done

lemma set_spec_op_no_Inp_step[simp]:
  "\<not> step (Inp p x) (set_spec_op S S') op'"
  apply (subst set_spec_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  done


lemma wstep_set_spec_op_eq_step[simp]:
  "io \<noteq> Tau \<Longrightarrow>
   wstep io (set_spec_op S S') op' = step io (set_spec_op S S') op'"
  unfolding wstep_def
  apply (cases io; simp)
  using converse_rtranclpE apply fastforce
  apply (smt (verit, ccfv_threshold) converse_rtranclpE relcompp_apply rtranclp_reflclp_absorb set_spec_op_no_Tau_step step_set_spec_op_elim sup2CI)
  done

lemma set_op_bisim_set_spec_op:
  "set_op S S' \<oslash> ~ set_spec_op S S'"
  apply (coinduction arbitrary: S S' rule: bisim_coinduct_upto'')
  subgoal for io op1'
    apply (elim step_set_op_elim)
      apply simp_all
      apply (metis (mono_tags, lifting) bc_base cin.rep_eq step_set_spec_op_intro_Out)
    done
  subgoal for io op1'
    apply (elim step_set_spec_op_elim)
    apply simp
    apply (metis (mono_tags, lifting) bc_base cin.rep_eq step_set_op_intro_Out)
    done
  done

definition "set_spec_op_trace S S' ios =
  (ldistinct ios \<and> (cset_of_llist ios \<le> cimage (\<lambda> (p, x). VOut p x) (S - S')) \<and> llength ios = eccard (S - S'))"

coinductive set_spec_op_trace_alt where
  "S - S' = {||} \<Longrightarrow>set_spec_op_trace_alt S S' LNil"
|  "(p, x) |\<in>| S - S' \<Longrightarrow> set_spec_op_trace_alt S (cinsert (p, x) S') lxs \<Longrightarrow>
   set_spec_op_trace_alt S S' (LCons (VOut p x) lxs)"

lemma set_spec_op_trace_alt_no_repeat:
  "VOut p x \<in> lset lxs \<Longrightarrow> set_spec_op_trace_alt S S' lxs \<Longrightarrow> (p, x) |\<in>| S' \<Longrightarrow> False"
  apply (induct lxs arbitrary: S S' rule: lset_induct)
  subgoal for lxs
    by (metis VIO.inject(2) cDiffD2 llist.inject llist.simps(3) set_spec_op_trace_alt.cases)
  subgoal
    by (metis cinsertCI llist.distinct(1) llist.inject set_spec_op_trace_alt.cases)
  done

lemma set_spec_op_trace_alt_no_VInp:
  "VInp p x \<in> lset lxs \<Longrightarrow> set_spec_op_trace_alt S S' lxs \<Longrightarrow> False"
  apply (induct lxs arbitrary: S S' rule: lset_induct)
  subgoal for lxs
    using set_spec_op_trace_alt.cases by auto
  subgoal
    by (metis llist.distinct(1) llist.inject set_spec_op_trace_alt.cases)
  done


lemma set_spec_op_trace_alt_in_cDiff:
  "x \<in> lset ios \<Longrightarrow> set_spec_op_trace_alt S S' ios \<Longrightarrow> x |\<in>| ((\<lambda>(x, y). VOut x y) |`| cDiff S S')"
  apply (induct ios arbitrary: S S' rule: lset_induct)
  subgoal for lxs
    by (metis (no_types, lifting) case_prod_conv cimage_eqI llist.distinct(1) llist.inject set_spec_op_trace_alt.cases)
  subgoal
    by (smt (verit, ccfv_threshold) cDiff_cinsert cimage_cinsert cinsert_cDiff cinsert_iff llist.distinct(1) llist.inject set_spec_op_trace_alt.simps)
  done

lemma set_spec_op_trace_alt_ldistinct:
  "set_spec_op_trace_alt S S' lxs \<Longrightarrow> ldistinct lxs"
  apply (coinduction arbitrary: S S' lxs)
  subgoal for S S' lxs
    apply (erule set_spec_op_trace_alt.cases)
    subgoal
      by simp
    subgoal
     apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
      apply (metis (lifting) cinsertI1 ldistinct_cong.intros(1) set_spec_op_trace_alt_no_repeat)
      done
    done
  done

lemma set_spec_op_trace_alt_card:
  "set_spec_op_trace_alt S S' lxs \<Longrightarrow>
   llength lxs = eccard (S - S')"
  apply (coinduction arbitrary: lxs S S' rule: enat_coinduct)
  subgoal for lxs S S'
    apply (erule set_spec_op_trace_alt.cases)
    subgoal
      by (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)
    subgoal
      apply hypsubst_thin
      apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)
      apply (intro conjI impI)
      subgoal
        by auto
      subgoal
        apply (intro exI conjI disjI1)
           apply (rule refl)+
          prefer 3
          apply assumption
         apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: ccard.rep_eq minus_cset_def less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
        done
      subgoal
        apply (intro exI conjI disjI1)
          apply (rule refl)+
         defer
         apply assumption
        apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: ccard.rep_eq minus_cset_def less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
        done
      done
    done
  done


lemma set_spec_op_trace_soundness:
  "set_spec_op_trace S S' ios \<Longrightarrow> set_spec_op_trace_alt S S' ios"
  apply (coinduction arbitrary: S S' ios)
  subgoal for S S' ios
    unfolding set_spec_op_trace_def
    apply (cases ios)
    subgoal
      apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)
      done
    subgoal for x lxs'
      apply (cases x; simp)
       apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
       apply (metis VIO.simps(3) case_prod_conv cimageE cinsert_code cinsert_csubset surj_pair)
      apply (intro conjI)
      subgoal
        apply (clarsimp del: disjCI simp add: cinfinite_def simp flip: cinsert_code cin.rep_eq split: if_splits)
        subgoal
          by (metis cinsert.rep_eq finite_Diff_insert minus_cset.rep_eq)
        subgoal
          by (smt (verit, ccfv_threshold) cDiff_cinsert2 cimage_cinsert cin_code cinsert_cDiff cinsert_cDiff_if csubset_cinsert infinity_eq_eSuc_iff prod.simps(2))
        done
      subgoal
        apply (clarsimp del: disjCI simp add: ccard_def cinfinite_def simp flip: cinsert_code cin.rep_eq split: if_splits)
        subgoal
          apply (intro conjI disjI1)
          using cDiff_cinsert cin_code cin_mono
           apply (smt (verit, ccfv_SIG) cinsert_cDiff_single csubset_cinsert prod.simps(2) rev_cimage_eqI subset_cimage_iff)
          apply (clarsimp del: disjCI simp add: ccard_def minus_cset_def cinfinite_def simp flip: cinsert_code cin.rep_eq split: if_splits)
          using eSuc_enat_iff apply fastforce
          done
        subgoal
          apply (simp add: minus_cset.rep_eq)
          done
        done
      done
    done
  done

lemma set_spec_op_trace_completeness:
  "set_spec_op_trace_alt S S' ios \<Longrightarrow> set_spec_op_trace S S' ios"
  unfolding set_spec_op_trace_def
  apply (erule set_spec_op_trace_alt.cases)
  subgoal
    apply (clarsimp simp flip: cinfinite_def cin.rep_eq)
    apply (intro conjI)
    apply (metis bot.extremum bot_cset.rep_eq cDiff_cempty cinfinite.rep_eq double_cDiff finite.intros(1))
    apply (metis bot.extremum cis_empty_code(1) cis_empty_def)
    using enat_0_iff(2) apply auto
    done
  subgoal for p x Sa S'a lxs
    apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
    apply (intro conjI disjI1)
    subgoal
      apply (meson cinsertI1 set_spec_op_trace_alt_no_repeat)
    using set_spec_op_trace_alt_ldistinct apply blast
    apply (clarsimp del: disjCI simp flip: cinsert_code cin.rep_eq)
    apply (intro conjI impI)
     apply (metis cDiffI cimageI old.prod.case)
      apply (metis (no_types, opaque_lifting) cDiff_iff cin_code cinsert_code cinsert_csubset csubsetI set_spec_op_trace_alt.intros(2) set_spec_op_trace_alt_in_cDiff)
    subgoal
      using set_spec_op_trace_alt_card
      by (metis cDiffI llength_LCons set_spec_op_trace_alt.intros(2))
    done
    subgoal
    apply (intro conjI disjI1 impI)
      subgoal
        by (meson cinsertI1 set_spec_op_trace_alt_no_repeat)
      subgoal
    using set_spec_op_trace_alt_ldistinct by blast
  subgoal
    by (metis cDiff_iff cin_code csubsetI set_spec_op_trace_alt.intros(2) set_spec_op_trace_alt_in_cDiff)
    subgoal
      using set_spec_op_trace_alt_card
      by (metis cDiffI llength_LCons set_spec_op_trace_alt.intros(2))
    done
  done
  done

lemma set_spec_op_trace_eq_set_spec_op_trace_alt:
  "set_spec_op_trace S S' ios \<longleftrightarrow> set_spec_op_trace_alt S S' ios"
  using set_spec_op_trace_completeness set_spec_op_trace_soundness by blast

lemma wfinished_set_spec_op:
  "wfinished (set_spec_op S S') \<Longrightarrow> csubset_eq S S'"
  apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)
  apply (rule ccontr)
  using step_set_spec_op_intro_Out[of _ _ _S S', rotated] apply -
  apply (drule meta_spec)+
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply (rule refl)
  apply (drule meta_mp)
   apply (rule refl)
  unfolding wfinished_no_wstep
  apply auto
  apply (metis IO.simps(8) vio_of_io_inverse)
  done

lemma wtraced_set_spec_op_soundness:
  "wtraced (set_spec_op S S') ios \<Longrightarrow> set_spec_op_trace S S' ios"
  unfolding set_spec_op_trace_eq_set_spec_op_trace_alt
  apply (coinduction arbitrary: ios S S')
  subgoal for ios S S'
        apply (erule wtraced.cases)
    subgoal for op
      using wfinished_set_spec_op by auto
    subgoal for vio op op' lxs
      apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)
      apply (cases vio; simp)
      apply (elim step_set_spec_op_elim)
      apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)
      done
    done
  done

lemma wtraced_set_spec_op_completeness:
  "set_spec_op_trace S S' ios \<Longrightarrow> wtraced (set_spec_op S S') ios"
  unfolding set_spec_op_trace_eq_set_spec_op_trace_alt
  apply (coinduction arbitrary: ios S S')
  subgoal for ios S S'
        apply (erule set_spec_op_trace_alt.cases)
    subgoal for S S'
      apply simp
      unfolding wfinished_no_wstep
      apply clarsimp
      apply (elim step_set_spec_op_elim)
      apply clarsimp
      apply (meson basic_trans_rules(31) less_eq_cset.rep_eq)
      done
    subgoal for p x S S' lxs
      apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)
      apply force
      done
    done
  done

lemma wtraced_set_spec_op_correctness:
  "wtraced (set_spec_op S S') ios \<longleftrightarrow> set_spec_op_trace S S' ios"
  using wtraced_set_spec_op_completeness wtraced_set_spec_op_soundness by force

lemma set_op_wbisim_set_spec_op_wtraces_gen:
  "set_op S S' op \<approx> set_spec_op S S' \<Longrightarrow>
   wtraces (set_op S S' op) = {ios. set_spec_op_trace S S' ios}"
  unfolding wtraces_def using wbisim_sym wbisim_wtraced wtraced_set_spec_op_correctness by blast

lemma set_op_wbisim_set_spec_op_wtraces:
  "set_op {||} {||} op \<approx> set_spec_op S {||} \<Longrightarrow>
   wtraces (set_op {||} {||} op) = {ios. ldistinct ios \<and> (cset_of_llist ios \<le> cimage (\<lambda> (p, x). VOut p x) S) \<and> llength ios = eccard S}"
  by (smt (verit) Collect_cong cDiff_cempty set_spec_op_trace_def wbisim_wtraces wtraced_set_spec_op_correctness wtraces_def)

lemma
  "set_op {||} {||} op \<approx> set_spec_op S {||} \<Longrightarrow>
   wtraced op ios \<Longrightarrow>
   VOut p x \<in> lset ios \<Longrightarrow>
   (p, x) |\<in>| S"
  apply (frule wbisim_wtraces)
  apply (subst (asm) set_op_wbisim_set_spec_op_wtraces)
   apply assumption
  unfolding wtraces_def

  find_theorems wtraces wbisim

  oops

lemma
  "set_op {||} {||} op \<approx> set_spec_op S {||} \<Longrightarrow>
   (p, x) |\<in>| S \<Longrightarrow>
   \<exists> ios. wtraced op ios \<and> VOut p x \<in> lset ios"
  oops

end