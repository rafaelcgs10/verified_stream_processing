theory Set_op

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.CSet_LList_Impl
  "../Timely_Infrastructure"
begin

lemma cset_induct[consumes 1, case_names find step]:
  "x |\<in>| A \<Longrightarrow> P {|x|} \<Longrightarrow> (\<And>x' A. x |\<in>| A \<Longrightarrow> x \<noteq> x' \<Longrightarrow> P A \<Longrightarrow> P (cinsert x' A)) \<Longrightarrow> P A"
  apply (rule cset.acset_induct[of ])
  apply simp
  oops

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

lemma
  "set_op {||} {||} op \<approx> set_spec_op S {||}"
  oops

abbreviation "eccard S \<equiv> (if cinfinite S then infinity else ccard S)"

definition "set_spec_op_trace S S' ios =
  (ldistinct ios \<and> (cset_of_llist ios \<le> cimage (\<lambda> (p, x). VOut p x) (S - S')) \<and> llength ios = eccard (S - S'))"

coinductive set_spec_op_trace_alt where
  "S - S' = {||} \<Longrightarrow>set_spec_op_trace_alt S S' LNil"
|  "(p, x) |\<in>| S - S' \<Longrightarrow>
   set_spec_op_trace_alt S (cinsert (p, x) S') lxs \<Longrightarrow>
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

lemma wtraced_set_spec_op_soundness:
  "wtraced (set_spec_op S S') ios \<Longrightarrow> set_spec_op_trace S S' ios"
  unfolding set_spec_op_trace_eq_set_spec_op_trace_alt
  apply (coinduction arbitrary: ios S S')
  subgoal for ios S S'
        apply (erule wtraced.cases)
    subgoal for op
      apply simp
      apply hypsubst_thin
      unfolding wfinished_no_wstep
      apply simp
      sorry
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

definition "trace_set S S' ios ios' =
  (ldistinct ios' \<and> (\<forall> vio \<in> lset ios. \<not> is_VInp vio) \<and>
  ((cUn (cimage (\<lambda> io. case io of VOut p x \<Rightarrow> (p, x)) (cset_of_llist ios)) S) - S' =
  cimage (\<lambda> io. case io of VOut p x \<Rightarrow> (p, x)) (cset_of_llist ios')))"

lemma wstep_set_op_elim:
  assumes "wstep (Out p x) (set_op S S' op) op'"
  obtains vios op2 where
   "wsteps vios op op2" "\<forall> io \<in> set vios. \<not> is_VInp io"
   "op' = set_op (cUn S (cimage (\<lambda> io. case io of VOut p x \<Rightarrow> (p, x)) (cset_of_llist (llist_of vios)))) (cinsert (p, x) S') op2"
  oops

lemma not_step_set_op:
  "(p, x) |\<in>| S' \<Longrightarrow>
   \<not> step (Out p x) (set_op S S' op) op'"
  oops

lemma wsteps_never_produces_vio:
  "(\<forall> op' vios. wsteps vios op op' \<longrightarrow> vio \<notin> set vios) \<Longrightarrow> wtraced op vios \<Longrightarrow> vio \<notin> lset vios"
  oops


lemma
  "wtraced op ios \<Longrightarrow>
   wtraced (set_op S S' op) ios' \<Longrightarrow>
   trace_set S S' ios ios'"
   unfolding trace_set_def
    apply (intro conjI)
    subgoal
apply (coinduction arbitrary: ios ios' S S' op)
      subgoal for ios ios' S S' op
        apply (erule wtraced.cases)
        back
        subgoal
          by clarsimp
        subgoal for vio op'' op' lxs
          apply clarsimp
          apply hypsubst_thin
          apply (cases vio; simp; hypsubst_thin)
          subgoal sorry
          subgoal for p x
            apply (intro conjI)
            subgoal
              oops


(* lemma
  "wtraces (set_op op) = (wtraces op)"
  unfolding wtraces_def
  apply auto
  subgoal for vios
    oops
 *)
end