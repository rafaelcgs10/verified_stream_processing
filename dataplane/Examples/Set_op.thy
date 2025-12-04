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

definition "set_spec_op_trace S S' ios =
  (ldistinct ios \<and> (\<forall> vio \<in> lset ios. \<not> is_VInp vio) \<and>
  (cset_of_llist ios = cimage (\<lambda> (p, x). VOut p x) (S - S')))"

coinductive set_spec_op_trace_alt where
  "S - S' = {||} \<Longrightarrow> set_spec_op_trace_alt S S' LNil"
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

lemma set_spec_op_trace_soundness:
  "set_spec_op_trace S S' ios \<Longrightarrow> set_spec_op_trace_alt S S' ios"
      apply (coinduction arbitrary: S S' ios)
    subgoal for S S' ios
      unfolding set_spec_op_trace_def
      apply (cases ios)
      subgoal
      apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
        apply (metis bot_cset.rep_eq cDiffI cemptyE cimageI cset_of_llist.abs_eq cset_of_llist.rep_eq lset_LNil wit_cset_inverse)
        done
      subgoal for x lxs'
        apply (cases x; simp)
      apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
        apply (smt (verit) VIO.discI(2) VIO.disc_eq_case(2) VIO.inject(2) cDiffD2 cDiff_cinsert cDiff_cinsert2 cDiff_cinsert_absorb case_prodE2 case_prod_conv cimageE cimage_cinsert cin_code cinsertCI
            cinsert_absorb cinsert_cDiff cinsert_code)
        done
      done
    done

lemma set_spec_op_trace_completeness:
  "set_spec_op_trace_alt S S' ios \<Longrightarrow> \<exists> ios'. set_spec_op_trace S S' ios' \<and> lset ios \<subseteq> lset ios'"
    unfolding set_spec_op_trace_def
    apply (erule set_spec_op_trace_alt.cases)
      subgoal
        apply clarsimp
        apply (metis bot.extremum cDiff_cempty cempty_is_cimage cis_empty_code(1) cis_empty_def double_cDiff emptyE ldistinct_LNil_code llist.set(1))
        done
      subgoal for p x Sa S'a lxs
        apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
        oops

lemma
  "wtraced (set_spec_op S S') vios \<longleftrightarrow> set_spec_op_trace S S' vios"
  apply (rule iffI)
  subgoal
    unfolding set_spec_op_trace_def
    apply (intro conjI)
    subgoal
      apply (coinduction arbitrary: S S' vios)
      subgoal for S S'
        apply (erule wtraced.cases)
        subgoal
          by clarsimp
        subgoal for vio op op' lxs
          apply clarsimp
          apply hypsubst_thin
          apply (cases vio; simp; hypsubst_thin)
          apply (erule step_set_spec_op_elim; simp)
          apply hypsubst_thin
          subgoal for a x p
            apply (intro conjI)
            subgoal
              apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
              sorry
            subgoal
              apply (rule ldistinct_cong.intros(1))
              by blast
            done
          done
        done
      done
    subgoal
  apply (erule wtraced.cases)
        subgoal
          by clarsimp
        subgoal for vio op op' lxs
          apply clarsimp
          apply hypsubst_thin
          apply (cases vio; simp; hypsubst_thin)
          apply (erule step_set_spec_op_elim; simp)
          apply hypsubst_thin
          sorry
        done
      subgoal
  apply (erule wtraced.cases)
        subgoal
          by (metis bot_cset.rep_eq cDiff_iff cimage_cempty cset_of_llist.abs_eq cset_of_llist.rep_eq ex_cin_conv io_of_vio.simps(2) lset_LNil step_not_wfinished step_set_spec_op_intro_Out surj_pair
              wit_cset_inverse)
        subgoal for vio op op' lxs
          apply clarsimp
          apply hypsubst_thin
          apply (cases vio; simp; hypsubst_thin)
          apply (erule step_set_spec_op_elim; simp)
              apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
          oops

definition "trace_set S S' ios ios' =
  (ldistinct ios' \<and> (\<forall> vio \<in> lset ios. \<not> is_VInp vio) \<and>
  ((cUn (cimage (\<lambda> io. case io of VOut p x \<Rightarrow> (p, x)) (cset_of_llist ios)) S) - S' =
  cimage (\<lambda> io. case io of VOut p x \<Rightarrow> (p, x)) (cset_of_llist ios')))"

lemma wstep_set_op_elim:
  assumes "wstep (Out p x) (set_op S S' op) op'"
  obtains vios op2 where
   "wsteps vios op op2" "\<forall> io \<in> set vios. \<not> is_VInp io"
   "op' = set_op (cUn S (cimage (\<lambda> io. case io of VOut p x \<Rightarrow> (p, x)) (cset_of_llist (llist_of vios)))) (cinsert (p, x) S') op2"
  sorry

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


lemma
  "wtraced (set_op S S' \<oslash>) ios \<longleftrightarrow> set_op_trace S S' ios"
  apply (rule iffI)
  subgoal
    unfolding set_op_trace_def
    apply (intro conjI)
    subgoal
      apply (coinduction arbitrary: ios S S')
      subgoal for ios S S'
        apply (erule wtraced.cases)
        subgoal
          by simp
        subgoal for vio op op' lxs
          apply clarsimp
          apply hypsubst_thin
          apply (cases vio; simp; hypsubst_thin)
          subgoal sorry
          oops

lemma
  "wtraced op vios \<Longrightarrow>
   (\<forall> vio \<in> lset vios. \<not> is_VInp vio \<and> \<not> vio |\<in>| cimage (\<lambda> (p, x). VOut p x) S') \<Longrightarrow>
   cset_of_llist vios = cimage (\<lambda> (p, x). VOut p x) S' \<Longrightarrow>
   wtraced (set_op S S' op) vios"
  apply (coinduction arbitrary: vios op S S')
  subgoal for vios
    apply (erule wtraced.cases)
    subgoal for op
      apply simp
      sorry
    subgoal for vio opa op' lxs
      apply clarsimp
      apply (cases vio; simp)
      subgoal for p x
        apply hypsubst_thin
        apply (intro conjI exI)
         apply (rule wstep_Out_set_op)
           apply assumption
          apply force
         apply (rule refl)
        apply (intro conjI exI disjI1)
          apply (rule refl)
         apply simp_all
        apply (auto 0 0)
        apply (drule spec)
        apply (elim conjE)
        apply (drule mp)
        apply (rule refl)
        apply (drule mp)
         apply assumption
          apply simp_all
        
        

end
      apply (intro exI conjI)
      apply (rule wtraced.Step[rotated, of "set_op _ _ _" _ vio'])
        apply simp_all
      apply (cases vio'; simp)
      apply hypsubst_thin


(* lemma
  "wtraces (set_op op) = (wtraces op)"
  unfolding wtraces_def
  apply auto
  subgoal for vios
    oops
 *)
end