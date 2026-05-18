theory Set_op

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.CSet_LList_Impl
  "../Timely_Infrastructure"
  "../LList_Haskell_Setup"
begin

(* FIXME: move me *)
lemma wsteps_step_tau[intro]:
  "wsteps vios op2 op3 \<Longrightarrow>
   step Tau op1 op2 \<Longrightarrow>
   wsteps vios op1 op3"
  by (induct vios arbitrary: op2 op3 op1 rule: wsteps.induct) auto

lemma wfinished_step_taus[intro]:
  "wfinished op \<Longrightarrow>
   (step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   wfinished op'"
  unfolding wfinished_no_wstep
  apply (clarsimp del: disjCI simp flip: cin.rep_eq ; hypsubst_thin?)
  subgoal for vio opp
    unfolding not_def
    apply (drule spec[of _ vio])
    apply (drule spec[of _ opp])
    apply (drule mp)
     apply (metis (lifting) estep.elims io_of_vio_not_Tau(1) wstep_trans'(1,2))
    apply auto
    done
  done

lemma wsteps_append[simp]:
  "wsteps (xs @ ys) = (wsteps xs OO wsteps ys)"
  apply (rule ext)+
  apply (induct xs arbitrary: ys)
  subgoal for xs
    apply clarsimp    
    apply (smt (verit, ccfv_threshold) eq_OO estep.simps(1) relcomppI relcompp_assoc relcompp_distrib2 rtranclp_reflclp_absorb sup.idem sup_left_commute wstep_def wstep_steps_Tau wsteps.elims)
    done
  subgoal for a xs x xs'
    apply auto
     apply blast+
    done
  done

lemma step_tau_wtraced:
  "step Tau op op' \<Longrightarrow>
   \<not> wfinished op' \<Longrightarrow>
   wtraced op' ios \<Longrightarrow>
   wtraced op ios"
  apply (coinduction arbitrary: op ios)
  subgoal for op ios
    apply (erule wtraced.cases)
     apply simp_all
    apply blast
    done
  done

lemma step_taus_wtraced:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   \<not> wfinished op' \<Longrightarrow>
   wtraced op' ios \<Longrightarrow>
   wtraced op ios"
  apply (smt (verit, ccfv_threshold) append.right_neutral relcomppI relcompp_assoc wstep_def wsteps.simps(1) wsteps_append wtraced.simps)
  done

lemma wsteps_not_finished_wtraced:
  "wsteps vios op op' \<Longrightarrow>
   \<not> wfinished op' \<Longrightarrow>
   wtraced op' ios \<Longrightarrow>
   wtraced op (vios @@- ios)"
  apply (induct vios arbitrary: op op' ios rule: rev_induct)
   apply simp_all
  subgoal 
    using step_taus_wtraced by blast
  subgoal for x xs op op' ios
    apply clarsimp
    apply (metis step_taus_wtraced wfinished_no_wstep wtraced.intros(2))
    done
  done

lemma wsteps_wtraced:
  "wsteps vios op op' \<Longrightarrow>
   vios \<noteq> [] \<Longrightarrow>
   wtraced op' ios \<Longrightarrow>
   wtraced op (vios @@- ios)"
  apply (induct vios arbitrary: op op' ios rule: rev_induct)
   apply simp_all
  subgoal for x xs op op' ios
    apply clarsimp
    apply (smt (verit, ccfv_threshold) estep.cases io_of_vio_not_Tau(1) lshift_simps(1) wstep_converse_trans'(1,2) wstep_trans'(1,2) wsteps.simps(1) wtraced.intros(2)) 
    done
  done

lemma wtraced_not_LNil_not_wfinished:
  "wtraced op ios \<Longrightarrow> ios \<noteq> LNil \<Longrightarrow> \<not> wfinished op"
  apply (erule wtraced.cases)
   apply simp_all
  using wfinished_no_wstep apply blast
  done

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

lemma step_n_Taus_set_op[intro]:
  "(step Tau ^^ n) op op' \<Longrightarrow>
   op'' = set_op S S' op' \<Longrightarrow>
   (step Tau ^^ n) (set_op S S' op) op''"
  apply (induct n arbitrary: op op' S S')
   apply simp_all
  apply (metis (no_types, opaque_lifting) relcompp.cases relpowp_Suc_I2 relpowp_Suc_left relpowp_Suc_right step_set_op_intro_Tau_2)
  done

term cset_from_list

lemma step_set_op_steps_Out_intro[intro]:
  "steps (map (Out p) xs) op op'' \<Longrightarrow>
   n = length xs \<Longrightarrow>
   op' = set_op (cUn ((Pair p) |`| cset_from_list xs) S) S' op'' \<Longrightarrow>
   (step Tau ^^ n) (set_op S S' op) op'"
  apply (induct xs arbitrary: op op' op'' S S' n rule: rev_induct)
   apply simp_all
  apply force
  done

lemma set_op_not_step_Inp[simp]:
  "\<not> step (Inp p x) (set_op S S' op) op'"
  unfolding not_def
  apply (intro impI)
  apply (elim step_set_op_elim; simp)
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

lemma step_taus_set_op_elim:
  assumes "(step Tau)\<^sup>*\<^sup>* (set_op S S' op) op'"
  obtains op'' xs where "wsteps (map (\<lambda> (p, x). VOut p x) xs) op op''"
    "op' = set_op (cUn (cset_of_llist (llist_of xs)) S) S' op''"
  using assms apply -
  apply atomize_elim
  apply (induction "set_op S S' op" arbitrary: S S' op rule: converse_rtranclp_induct)
  subgoal for S S' op
    apply (rule exI[of _ "[]"])
    apply (rule exI[of _ "op"])
    apply (clarsimp simp flip: cin.rep_eq)
    apply (metis boolean_algebra_cancel.sup0 cis_empty_code(1) eq_cempty_cis_empty(1) inf_sup_aci(5))
    done
  subgoal for op'' S S' op
    apply (elim step_set_op_elim; clarsimp simp flip: cin.rep_eq)
    subgoal for op'''
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (clarsimp simp flip: cin.rep_eq)
      apply (smt (verit, best) converse_rtranclp_into_rtranclp relcompp_apply wstep_trans_tau_1 wsteps.elims)
      done
    subgoal for p x op''a
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (auto simp flip: cin.rep_eq)
      subgoal for xs op'''
        apply (rule exI[of _ "(p, x) # xs"])
        apply (intro conjI exI)
         defer
         apply (clarsimp simp flip: cin.rep_eq)
         apply (rule arg_cong3[where f=set_op])
           apply (metis cUn_cinsert_left cinsert_code)
          apply (rule refl)+
        apply auto
        done
      done
    done
  done

lemma wstep_set_op_elim:
  assumes "wstep io (set_op S S' op) op'"
  obtains op'' op''' xs ys p x where "io = Out p x"
    "wsteps (map (\<lambda> (p, x). VOut p x) xs) op op''" "(p, x) |\<in>| (cUn (cset_of_llist (llist_of xs)) S) - S'"
    "wsteps (map (\<lambda> (p, x). VOut p x) ys) op'' op'''" 
    "op' = set_op (cUn (cset_of_llist (llist_of (xs @ ys))) S) (cinsert (p, x) S') op'''"
  | op'' op''' xs ys where "io = Tau"
    "wsteps (map (\<lambda> (p, x). VOut p x) xs) op op''"
    "wsteps (map (\<lambda> (p, x). VOut p x) ys) op'' op'''" 
    "op' = set_op (cUn (cset_of_llist (llist_of (xs @ ys))) S) S' op'''"
  using assms apply -
  apply atomize_elim
  unfolding wstep_def
  apply (elim relcomppE)
  subgoal for op1 op2
    apply (erule step_taus_set_op_elim)
    apply (clarsimp del: disjCI simp flip: cin.rep_eq)
    apply (cases io; clarsimp del: disjCI simp flip: cin.rep_eq)
    subgoal for op'' xs p x
      apply (elim step_set_op_elim; clarsimp simp flip: cin.rep_eq)
      apply hypsubst_thin
      apply (erule step_taus_set_op_elim)
      apply (clarsimp simp flip: cin.rep_eq)
      subgoal for op''' ys
        apply (rule exI[of _ xs])
        apply (rule exI[of _ op''])
        apply (intro conjI)
          apply assumption+
        apply (rule exI[of _ ys])
        apply (rule exI[of _ op'''])
        apply (intro conjI)
         apply assumption+
        apply (rule arg_cong3[where f=set_op])
          apply blast
         apply auto
        done
      done
    subgoal for op'' xs
      apply (elim disjE)
      subgoal
        apply (elim step_set_op_elim; clarsimp simp flip: cin.rep_eq)
        subgoal for op'''
          apply hypsubst_thin
          apply (erule step_taus_set_op_elim)
          subgoal for op'''' ys
            apply (rule exI[of _ xs])
            apply (rule exI[of _ op''])
            apply (intro conjI)
             apply assumption+
            apply (rule exI[of _ ys])
            apply (rule exI[of _ op''''])
            apply (intro conjI)
            subgoal
              by auto
            apply hypsubst_thin
            apply (rule arg_cong3[where f=set_op])
              apply blast
             apply auto
            done
          done
        subgoal for p x op'''
          apply hypsubst_thin
          apply (erule step_taus_set_op_elim)
          subgoal for op'''' ys
            apply (rule exI[of _ "xs"])
            apply (rule exI[of _ op''])
            apply (intro conjI)
             apply assumption+
            apply hypsubst_thin
            apply (rule exI[of _ "(p, x) # ys"])
            apply (rule exI[of _ op''''])
            apply (intro conjI)
             apply simp
             apply blast
            apply (rule arg_cong3[where f=set_op])
              apply simp
            subgoal premises
              by (metis (mono_tags, lifting) boolean_algebra_cancel.sup1 boolean_algebra_cancel.sup2 cUn_cinsert_left cinsert_code)
             apply auto
            done
          done
        done
      subgoal
        apply hypsubst_thin
        apply (erule step_taus_set_op_elim)
        subgoal for op'''' ys
          apply (rule exI[of _ "xs"])
          apply (rule exI[of _ op''])
          apply (intro conjI)
           apply assumption+
          apply (rule exI[of _ "ys"])
          apply (rule exI[of _ op''''])
          apply (intro conjI)
           apply assumption+
          apply hypsubst_thin
          apply (rule arg_cong3[where f=set_op])
            apply blast
           apply auto
          done
        done
      done
    done
  done

lemma wsteps_map_VOut_step_taus_set_op:
  "wsteps (map (\<lambda>(x, y). VOut x y) xs) op op' \<Longrightarrow>
   op'' = (set_op (cUn (cset_of_llist (llist_of xs)) S) S' op') \<Longrightarrow>
   (step Tau)\<^sup>*\<^sup>* (set_op S S' op) op''"
  apply hypsubst_thin
  apply (induct "map (\<lambda>(x, y). VOut x y) xs" arbitrary: S S' op op' xs rule: wsteps.induct)
  subgoal 
    by (auto simp add: cUn_absorb1 csubset_eq_cset_of_llist step_Taus_set_op)
  subgoal for vio vios xs S S' op op'
    apply (auto del: disjCI simp add: wstep_def some_elem_def csome_elem_def simp flip: cin.rep_eq split: prod.splits; hypsubst_thin?)
    subgoal for zs ba bb bc
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule step_Taus_set_op)
         apply assumption
        apply (rule refl)+
       apply (rule step_set_op_intro_Tau_1)
         apply assumption
        apply (rule refl)+
      apply (rule rtranclp_trans)
       apply (rule step_Taus_set_op)
        apply assumption
       apply (rule refl)+
      apply (metis (no_types, lifting) cUn_cinsert_left cUn_cinsert_right cinsert_code)
      done
    done
  done

lemma wsteps_map_VOut_wstep_out_set_op:
  "wsteps (map (\<lambda>(x, y). VOut x y) xs) op op' \<Longrightarrow>
   (p, x) \<in> set xs \<Longrightarrow>
   \<not> (p, x) |\<in>| S' \<Longrightarrow>
   wstep (Out p x) (set_op S S' op) (set_op (cUn (cset_of_llist (llist_of xs)) S) (cinsert (p, x) S') op')"
  unfolding wstep_def
  apply (clarsimp del: disjCI simp add: wstep_def some_elem_def csome_elem_def simp flip: cin.rep_eq split: prod.splits; hypsubst_thin?)
  apply (intro relcomppI)
    apply (rule wsteps_map_VOut_step_taus_set_op)
     apply assumption
    apply (rule refl)+
   apply (rule step_set_op_intro_Out)
      apply (rule refl)+
     apply (meson cUnCI in_cset_of_llist_llist_of)
    apply assumption
   apply (rule refl)+
  apply force
  done

coinductive set_op_trace where
  "S - S' = {||} \<Longrightarrow> 
  (\<forall> op' xs. wsteps (map (\<lambda> (p, x). VOut p x) xs) op op' \<longrightarrow> cset_of_llist (llist_of xs) \<le> S') \<Longrightarrow>
   set_op_trace S S' op LNil"
|  "wsteps (map (\<lambda> (p, x). VOut p x) xs) op op' \<Longrightarrow>
    S2 = cUn (cset_of_llist (llist_of xs)) S1 \<Longrightarrow>
    (p, x) |\<in>| S2 - S' \<Longrightarrow>
    set_op_trace S2 (cinsert (p, x) S') op' lxs \<Longrightarrow>
    set_op_trace S1 S' op (LCons (VOut p x) lxs)"

lemma set_op_trace_intros_2':
  "wstep (Out p' x') op op' \<Longrightarrow>
   S2 = cinsert (p', x') S1 \<Longrightarrow> (p, x) |\<in>| cDiff S2 S' \<Longrightarrow> 
   set_op_trace S2 (cinsert (p, x) S') op' lxs \<Longrightarrow>
  ios = LCons (VOut p x) lxs \<Longrightarrow>
  set_op_trace S1 S' op ios"
  apply hypsubst_thin
  apply (rule set_op_trace.intros(2)[where xs="[(p', x')]", simplified])
     apply simp
     apply blast
    apply (rule refl)+
    apply (clarsimp del: disjCI simp flip: cin.rep_eq; hypsubst_thin?)+
  using cinsert_code apply fastforce
    apply (clarsimp del: disjCI simp flip: cin.rep_eq; hypsubst_thin?)
  apply (metis cinsert_code cinsert_is_cUn cis_empty_code(1) cis_empty_def)
  done

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

lemma set_op_trace_soundness:
  "VOut p x \<in> lset ios \<Longrightarrow>
   set_op_trace S S' op ios \<Longrightarrow>
   \<not> (p, x) |\<in>| (S - S') \<Longrightarrow>
   (\<exists> ios'. wtraced op ios' \<and> VOut p x \<in> lset ios')"
  apply (induct ios arbitrary: S S' op rule: lset_induct)
  subgoal for xs S S'
    apply (erule set_op_trace.cases; simp)
    apply (clarsimp del: disjCI simp flip: cin.rep_eq simp add: less_eq_cset.rep_eq subset_minus_empty cinfinite_def enat_0_iff minus_cset.rep_eq split: op.splits if_splits; hypsubst_thin?)+
    subgoal for xs op'
      using wtraced_trace_exec[of op'] apply -
      apply (intro exI conjI)
       apply (rule wsteps_wtraced)
         apply assumption
        apply force
       apply assumption
      apply auto
      done
    done
  subgoal for x' xs S S' op'
    apply (erule set_op_trace.cases; simp; hypsubst_thin?)
    subgoal for ys op op'' S2 S1 p' x'' S''
      apply (clarsimp del: disjCI simp flip: cin.rep_eq ; hypsubst_thin?)+
      apply (elim conjE disjE)
      subgoal      
        apply (cases "VOut p x \<notin> (\<lambda>(x, y). VOut x y) ` set ys")
        subgoal
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply assumption
          apply (drule meta_mp)
           apply (intro impI)
           apply (clarsimp del: disjCI simp flip: cin.rep_eq ; hypsubst_thin?)+
           apply blast
          apply (elim exE conjE)
          apply (intro conjI exI)
           apply (rule wsteps_wtraced)
             apply assumption
            apply force
           apply assumption
          apply simp
          done
        subgoal
          apply simp
          apply (intro conjI exI)
           apply (rule wsteps_wtraced)
             apply assumption
            apply force
           defer
           apply force
          apply (rule wtraced_trace_exec)
          done
        done
      subgoal
        apply (cases "VOut p x \<notin> (\<lambda>(x, y). VOut x y) ` set ys")
        subgoal
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply assumption
          apply (drule meta_mp)
           apply (intro impI)
           apply (clarsimp del: disjCI simp flip: cin.rep_eq ; hypsubst_thin?)+
           apply blast
          apply (elim exE conjE)
          subgoal for ios'
            apply (intro conjI exI)
             apply (rule wsteps_not_finished_wtraced)
               apply assumption
            subgoal 
              using wtraced_not_LNil_not_wfinished by fastforce
             apply assumption
            apply auto
            done
          done
        subgoal
          apply simp
          apply (intro conjI exI)
           apply (rule wsteps_wtraced)
             apply assumption
            apply force
           defer
           apply force
          apply (rule wtraced_trace_exec)
          done
        done
      done
    done
  done

lemma wfinished_csubset_eq[intro]:
  "wfinished (set_op S S' op) \<Longrightarrow> csubset_eq S S'"
  apply (auto simp flip: cin.rep_eq)
  apply (rule ccontr)
  subgoal for p x
    unfolding wfinished_no_wstep
    apply auto
    apply (subst (asm) not_def)
    apply (drule spec[of _ "VOut p x"])
    apply (drule spec)
    apply (drule mp)
    apply (rule step_wstep)
    apply (rule step_set_op_intro_Out)
        apply simp_all
    done
  done

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

lemma SOME_in_wsteps_exec:
  "(SOME x. x |\<in>| wsteps_exec op) = (vio, op') \<Longrightarrow>
   \<exists> vio' op''. (vio', op'') |\<in>| wsteps_exec op \<Longrightarrow>
   (vio, op') |\<in>| wsteps_exec op"
  apply (elim exE)
  apply (rule some_eq_imp[where P="\<lambda> x. x |\<in>| wsteps_exec op"])
   apply auto
  done

lemma set_op_trace_trace_exec:
  "set_op_trace S S' op (trace_exec (set_op S S' op))"
  apply (coinduction arbitrary: S S' op)
  subgoal for S S' op
    apply (clarsimp del: disjCI simp flip: cin.rep_eq)
    apply (subst (1 2) trace_exec.code)
    apply (auto del: disjCI simp add: some_elem_def csome_elem_def simp flip: cin.rep_eq split: prod.splits)
    subgoal for vio op' p x
      apply (rule ccontr)
      using wstep_exec_VOut_completeness[where p=p and x=x and op="set_op S S' op"] apply -
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule step_wstep)
       apply (rule step_set_op_intro_Out)
          apply (rule refl)+
      apply assumption+
       apply (rule refl)+    
      apply (drule SOME_in_wsteps_exec)
       apply force
      apply (simp add: cis_empty_def)
      done
    subgoal for x1 x2 op' xs p x
      apply (rule ccontr)
      unfolding cis_empty_wsteps_exec_wfinished wfinished_no_wstep
    apply (auto del: disjCI simp add: some_elem_def csome_elem_def simp flip: cin.rep_eq split: prod.splits)
      apply (drule spec[of _ "VOut p x"])
      apply (drule spec)
      apply (subst (asm) (2) not_def)
      apply (drule mp)
    apply (auto del: disjCI simp add: some_elem_def csome_elem_def simp flip: cin.rep_eq split: prod.splits)
      apply (rule wsteps_map_VOut_wstep_out_set_op)
        apply auto
      done
    subgoal for vio op''
        apply (cases vio)
      subgoal for p' x'
        apply (rule FalseE)
        apply (drule SOME_in_wsteps_exec)
        using cis_empty_wsteps_exec_wfinished eq_cempty_cis_empty(2) apply fastforce
        apply hypsubst_thin
        apply (drule wstep_exec_VInp_sound)
        apply (elim wstep_set_op_elim; clarsimp del: disjCI simp flip: cin.rep_eq; hypsubst_thin?)
        done
      subgoal for p' x'
        apply (clarsimp simp add: cis_empty_wsteps_exec_wfinished del: disjCI simp flip: cin.rep_eq)
          apply (drule SOME_in_wsteps_exec)
        using cis_empty_wsteps_exec_wfinished eq_cempty_cis_empty(2) apply fastforce
        apply (drule wstep_exec_VOut_sound)
        apply (elim wstep_set_op_elim; clarsimp del: disjCI simp flip: cin.rep_eq; hypsubst_thin?)
        subgoal for op'' op''' xs ys
        apply (rule exI[of _ "xs @ ys"])
        apply (rule exI[of _ "op'''"])
        apply (clarsimp del: disjCI simp flip: cin.rep_eq)
          apply (intro conjI relcomppI[rotated])
          apply assumption+
          apply auto
          done
        done
      done
    done
  done


lemma set_op_trace_completeness:
  "VOut p x \<in> lset ios \<Longrightarrow>
   wtraced op (ios :: ('p, 'p, 'd) VIO llist) \<Longrightarrow>
   (\<forall> vio \<in> lset ios. \<not> is_VInp vio) \<Longrightarrow>
   \<not> (p, x) |\<in>| S' \<Longrightarrow>
   (\<exists> (ios' :: ('p, 'p, 'd) VIO llist). set_op_trace S S' op ios' \<and> VOut p x \<in> lset ios')"
  apply (drule in_wtraced_in_wsteps)
   apply assumption+
  apply (elim exE conjE)
  subgoal for op' vios
    apply (intro exI conjI)
     apply (rule set_op_trace.intros(2)[where p=p and x=x])
        apply simp
    apply (rule refl)
      apply (metis cDiff_iff cUn_iff cin_code lset_llist_of)
    defer
     apply simp
    using set_op_trace_trace_exec apply fast
    done
  done

lemma wtraced_set_op_trace:
  "wtraced (set_op S S' op) = set_op_trace S S' op"
  apply (rule ext)
  subgoal for ios
   apply (rule iffI)
  subgoal 
    apply (coinduction arbitrary: S S' op ios)
    subgoal for S S' op ios
      apply (erule wtraced.cases; simp flip: cin.rep_eq; hypsubst_thin)
      subgoal
        apply (intro conjI impI allI)
        subgoal
          using wfinished_csubset_eq by auto
        subgoal for op' xs
          unfolding wfinished_no_wstep
          apply (auto simp flip: cin.rep_eq)
          subgoal for p x
          apply (rule ccontr)
            apply (subst (asm) not_def)
          apply (drule spec[of _ "VOut p x"])
          apply (drule spec)+
            apply (drule mp)
             apply simp_all
            apply (simp flip: cin.rep_eq)
            apply (rule wsteps_map_VOut_wstep_out_set_op)
            apply assumption
            apply auto
            done
          done
        done
      subgoal for vio op' op'' lxs
        apply (cases vio; simp flip: cin.rep_eq)
        subgoal for p x
          unfolding wstep_def
          apply (elim relcomppE)
          apply simp
          apply (metis set_op_not_step_Inp step_taus_set_op_elim)
          done
        subgoal for p x
          apply (elim wstep_set_op_elim; simp flip: cin.rep_eq)
          subgoal for op'' op''' xs ys p'
            apply hypsubst_thin
            apply (rule exI[of _ "xs @ ys"])
            apply (rule exI[of _ op'''])
            apply (simp flip: cin.rep_eq; hypsubst_thin?)
            apply auto
            done
          done
        done
      done
    done
    apply (coinduction arbitrary: S S' op ios)
    subgoal for S S' op'' ios
      apply (erule set_op_trace.cases; simp flip: cin.rep_eq; hypsubst_thin?)
      subgoal for S'' S''' op'
        unfolding wfinished_no_wstep
        apply (intro conjI impI notI)
        apply (elim exE)
        subgoal for vio op'''
          apply (cases vio; simp flip: cin.rep_eq; hypsubst_thin?)
          subgoal
            by (elim wstep_set_op_elim; simp flip: cin.rep_eq)
          subgoal for p x
          apply (elim wstep_set_op_elim; simp flip: cin.rep_eq ; hypsubst_thin?)
            apply (auto simp flip: cin.rep_eq; hypsubst_thin?)
            subgoal for op'''' op''''' xs ys
              apply (drule spec)
              apply (drule spec[of _ "xs @ ys"])
              apply (drule mp)
               apply force
              apply auto
              apply (meson cin.rep_eq csubsetD in_cset_of_llist_llist_of)
              done
            done
          done
        done
      subgoal for xs op''' op'''' S2' S1' p x S'' lxs
        apply (elim disjE conjE)
        subgoal
          apply (intro exI conjI)
            apply (rule wsteps_map_VOut_wstep_out_set_op)
             apply assumption
            apply auto
          done
        subgoal
          apply (intro exI conjI)
          unfolding wstep_def
          apply (intro relcomppI)
             apply (rule wsteps_map_VOut_step_taus_set_op)
              apply assumption
             apply (rule refl)+
          apply simp
            apply (rule step_set_op_intro_Out)
               apply (rule refl)
              apply auto
          done
        done
      done
    done
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

lemma wtraced_set_spec_op:
  "(p, x) |\<in>| S - S' \<Longrightarrow>
   \<exists> ios. wtraced (set_spec_op S S') ios \<and> (VOut p x) \<in> lset ios"
  apply (intro exI conjI)
   apply (rule wtraced.intros(2)[where vio="VOut p x"])
    apply (rule step_wstep)
  apply (rule step_set_spec_op_intro_Out[where S=S and p=p and x=x])
  apply (simp_all add: minus_cset.rep_eq)
  apply (rule wtraced_trace_exec)
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

lemma wtraces_set_spec_op:
  "wtraces (set_spec_op S S') = {ios. set_spec_op_trace S S' ios}"
  unfolding wtraces_def using wbisim_sym wbisim_wtraced wtraced_set_spec_op_correctness by blast


lemma set_op_soundness:
  "set_op {||} {||} op \<approx> set_spec_op S {||} \<Longrightarrow>
   wtraced op ios \<Longrightarrow>
   \<forall>vio\<in>lset ios. \<not> is_VInp vio \<Longrightarrow>
   VOut p x \<in> lset ios \<Longrightarrow>
   (p, x) |\<in>| S"
  apply (drule set_op_trace_completeness[of _ _ _ _ "{||}" "{||}"])
     apply assumption+
  apply simp
  apply (elim exE conjE)
  apply (drule wbisim_wtraces)
  unfolding wtraces_def wtraced_set_spec_op_correctness set_spec_op_trace_def wtraced_set_op_trace
  apply (clarsimp del: disjCI simp add:  simp flip: cin.rep_eq; hypsubst_thin?)
  apply (drule Collect_inj)
  subgoal for ios' 
  apply (drule fun_cong[where x=ios'])
    apply (auto simp add: csubset_eq_cset_of_llist simp flip: cin.rep_eq split: if_splits)
    done
  done

lemma set_op_completeness:
  "set_op {||} {||} op \<approx> set_spec_op S {||} \<Longrightarrow>
   (p, x) |\<in>| S \<Longrightarrow>
   \<exists> (ios :: ('p, 'p, 'd) VIO llist). wtraced op ios \<and> VOut p x \<in> lset ios"
  apply (drule wbisim_wtraces)
  unfolding wtraces_def set_spec_op_trace_def wtraced_set_op_trace
  apply (drule Collect_inj)
  apply (subgoal_tac "\<exists> (ios :: ('p, 'p, 'd) VIO llist). VOut p x \<in> lset ios \<and> set_op_trace {||} {||} op ios")
  subgoal
    apply (elim exE conjE)
    subgoal for ios
      apply (drule set_op_trace_soundness)
        apply assumption
       apply fast+
      done
    done
  subgoal
    using wtraced_set_spec_op[of p x S"{||}"] apply -
    apply (drule meta_mp)
     apply simp
    apply (elim conjE exE)
    subgoal for ios
      apply (rule exI[of _ ios])
      apply auto
      done
    done
  done

end