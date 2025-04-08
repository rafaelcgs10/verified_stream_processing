theory Wtraced_Composition

imports
  "BNA_Operators"
begin


inductive wstep_comp_op where
  \<open>comp_op wire buf' op1' op2' = comp_op wire buf op1 op2 \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1' op2 op2'\<close>
| \<open>step Tau op1 op1' \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1' op1'' op2 op2' \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1'' op2 op2'\<close>
| \<open>step Tau op2 op2' \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1' op2' op2'' \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1' op2 op2''\<close>
| \<open>wstep_comp_op Tau wire buf buf' op1 op1' op2 op2' \<Longrightarrow> step (Inp p x) op1' op1'' \<Longrightarrow> wstep_comp_op Tau wire buf' buf'' op1'' op1''' op2' op2'' \<Longrightarrow> wstep_comp_op (Inp (Inl p) x) wire buf buf'' op1 op1''' op2 op2''\<close>
| \<open>wstep_comp_op Tau wire buf buf' op1 op1' op2 op2' \<Longrightarrow> step (Out p x) op2' op2'' \<Longrightarrow> wstep_comp_op Tau wire buf' buf'' op1' op1'' op2'' op2''' \<Longrightarrow> wstep_comp_op (Out (Inr p) x) wire buf buf'' op1 op1'' op2 op2'''\<close>
| \<open>wstep_comp_op Tau wire buf buf' op1 op1' op2 op2' \<Longrightarrow> step (Out p x) op1' op1'' \<Longrightarrow> wire p = None \<Longrightarrow> wstep_comp_op Tau wire buf' buf'' op1'' op1''' op2' op2'' \<Longrightarrow> wstep_comp_op (Out (Inl p) x) wire buf buf'' op1 op1''' op2 op2''\<close>
| \<open>wstep_comp_op Tau wire buf buf' op1 op1' op2 op2' \<Longrightarrow> step (Inp p x) op2' op2'' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> wstep_comp_op Tau wire buf' buf'' op1' op1'' op2'' op2''' \<Longrightarrow> wstep_comp_op (Inp (Inr p) x) wire buf buf'' op1 op1'' op2 op2'''\<close>
| \<open>step (Out p x) op1 op1' \<Longrightarrow> wire p = Some q \<Longrightarrow> wstep_comp_op Tau wire (BENQ q x buf) buf'' op1' op1'' op2 op2' \<Longrightarrow> wstep_comp_op Tau wire buf buf'' op1 op1'' op2 op2'\<close>
| \<open>step (Inp p x) op2 op2' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> BHD p buf = x \<Longrightarrow> wstep_comp_op Tau wire (BTL p buf) buf'' op1 op1' op2' op2'' \<Longrightarrow> wstep_comp_op Tau wire buf buf'' op1 op1' op2 op2''\<close>

lemma step_Taus_comp_op:
  \<open>(step Tau)\<^sup>*\<^sup>* (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2') \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1' op2 op2'\<close>
  apply (induct "comp_op wire buf op1 op2" arbitrary: buf op1 op2 rule: converse_rtranclp_induct)
   apply (auto intro: wstep_comp_op.intros elim!: step_comp_op_elim)
  done

lemma wstep_comp_op:
  \<open>wstep io (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2') \<longleftrightarrow> wstep_comp_op io wire buf buf' op1 op1' op2 op2'\<close>
  apply (rule iffI)
  subgoal
    unfolding wstep_def
    apply (erule relcomppE)
    subgoal for op
      apply (induct "comp_op wire buf op1 op2" arbitrary: buf op1 op2  rule: converse_rtranclp_induct)
      subgoal 
        apply (cases io; simp)
        subgoal for p x
          apply (cases p)
          subgoal
            apply hypsubst_thin
            apply (erule relcomppE)
            apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
            done
          subgoal
            apply hypsubst_thin
            apply (erule relcomppE)
            apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
            done
          done
        subgoal
          apply hypsubst_thin
          apply (erule relcomppE)
          apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
          done
        subgoal
          apply hypsubst_thin
          apply (smt (verit, best) converse_rtranclp_into_rtranclp pick_middlep step_Taus_comp_op)
          done
        done
      subgoal for op buf op1 op2
        apply (cases io; simp)
        subgoal for p x
          apply (cases p)
          subgoal for p
            apply hypsubst_thin
            apply (erule relcomppE)
            subgoal for op''
              apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                 apply hypsubst_thin
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              done
            done
          subgoal for p
            apply hypsubst_thin
            apply (erule relcomppE)
            subgoal for op''
              apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                 apply hypsubst_thin
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              done
            done
          done
        subgoal for p x
          apply (cases p)
          subgoal for p
            apply hypsubst_thin
            apply (erule relcomppE)
            subgoal for op''
              apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                 apply hypsubst_thin
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              done
            done
          subgoal for p
            apply hypsubst_thin
            apply (erule relcomppE)
            subgoal for op''
              apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                 apply hypsubst_thin
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              subgoal
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 apply (rule refl)
                apply (erule wstep_comp_op.cases)
                        apply (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
                done
              done
            done
          done
        subgoal
          by (auto intro: step_Taus_comp_op wstep_comp_op.intros elim!: step_comp_op_elim)
        done
      done
    done
  subgoal
    apply (induct pred: wstep_comp_op)
            apply force
           apply blast
          apply blast
    subgoal for wire buf buf' op1 op1' op2 op2' p x op1'' buf'' op1''' op2''
      apply simp
      apply (smt (verit, ccfv_threshold) estep.simps(2) relcompp_apply step_comp_op_L_Inp wstep_def)
      done
    subgoal for wire buf buf' op1 op1' op2 op2' p x op2'' buf'' op1'' op2'''
      apply simp
      apply (smt (verit, best) estep.simps(3) relcomppI step_comp_op_R_Out wstep_def)
      done
    subgoal
      apply simp
      apply (smt (verit, ccfv_threshold) domIff estep.simps(3) relcomppI step_comp_op_L_Out wstep_def)
      done
    subgoal
      apply simp
      apply (smt (verit, best) estep.simps(2) relcompp_apply step_comp_op_R_Inp wstep_def)
      done
    subgoal
      apply simp
      apply (meson converse_rtranclp_into_rtranclp step_Tau_comp_op_L_alt)
      done
    subgoal
      by blast
    done
  done

inductive visible_cause for wire where
  "visible_cause wire buf (LCons (VInp (Inl p) x) ios) (LCons (VInp p x) ios1) ios2 buf ios ios1 ios2"
| "visible_cause wire buf (LCons (VOut (Inr p) x) ios) ios1 (LCons (VOut p x) ios2) buf ios ios1 ios2"
| "wire p = None \<Longrightarrow> visible_cause wire buf (LCons (VOut (Inl p) x) ios) (LCons (VOut p x) ios1) ios2 buf ios ios1 ios2"
| "p \<notin> ran wire \<Longrightarrow> visible_cause wire buf (LCons (VInp (Inr p) x) ios) ios1 (LCons (VInp p x) ios2) buf ios ios1 ios2"
| "visible_cause wire (BENQ q x buf) ios ios1 ios2 buf' ios ios1' ios2' \<Longrightarrow>
   wire p = Some q \<Longrightarrow> visible_cause wire buf ios (LCons (VOut p x) ios1) ios2 buf' ios ios1' ios2'"
| "visible_cause wire (BTL p buf) ios ios1 ios2 buf' ios ios1' ios2' \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> BHD p buf = x \<Longrightarrow>
   visible_cause wire buf ios ios1 (LCons (VInp p x) ios2) buf' ios ios1' ios2'"

coinductive causal for wire where
  "causal wire buf LNil LNil LNil"
| "causal wire buf' ios' ios1' ios2' \<Longrightarrow> ios \<noteq> LNil \<Longrightarrow> visible_cause wire buf ios ios1 ios2 buf' ios' ios1' ios2' \<Longrightarrow> causal wire buf ios ios1 ios2"

lemma visible_cause_VInp_Inl_LNil_False:
  "visible_cause wire buf (LCons (VInp (Inl lp) x) ios) ios1 ios2 buf' ios' ios1' ios2' \<Longrightarrow>
   ios1 = LNil \<Longrightarrow>
   False"
  apply (induct buf "LCons (VInp (Inl lp) x) ios" ios1 ios2 buf' ios' ios1' ios2' pred: visible_cause)
    apply auto
  done

lemma visible_cause_wtraced_wstep:
  "visible_cause wire buf IOS ios1 ios2 buf' ios' ios1' ios2' \<Longrightarrow>
   IOS = (LCons X ios) \<Longrightarrow>
   wtraced op1 ios1 \<Longrightarrow>
   wtraced op2 ios2 \<Longrightarrow>
   \<exists> op1' op2'. wstep (io_of_vio X) (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2') \<and> wtraced op1' ios1' \<and> wtraced op2' ios2' \<and> ios' = ios"
  apply (induct buf IOS ios1 ios2 buf' ios' ios1' ios2' arbitrary: op1 op2 pred: visible_cause)
       apply simp_all
  subgoal
    apply (erule wtraced.cases)
     apply simp_all
    subgoal for vio op op'
      apply (cases vio; simp)
      using wstep_comp_op_L_Inp apply fastforce
      done
    done
  subgoal
    apply (rotate_tac 2)
    apply (erule wtraced.cases)
     apply simp_all
    subgoal for vio op op'
      apply (cases vio; simp)
      apply (metis io_of_vio.simps(2) wstep_comp_op_R_Out)
      done
    done
  subgoal
    apply (erule wtraced.cases)
     apply simp_all
    subgoal for vio op op'
      apply (cases vio; simp)
      apply (metis domIff io_of_vio.simps(2) wstep_comp_op_L_Out)
      done
    done
  subgoal for p buf x ios1 ios2 op1 op2
    apply (rotate_tac 3)
    apply (erule wtraced.cases)
     apply simp_all
    subgoal for vio op op'
      apply (cases vio; simp)
      apply (metis io_of_vio.simps(1) wstep_comp_op_R_Inp)
      done
    done
  subgoal for q x buf iosa ios1 ios2 buf' ios1' ios2' p op1 op2
    apply (erule wtraced.cases)
     apply simp_all
    subgoal for vio op op'
      apply (cases vio; simp)
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply safe
      subgoal for p op1' op2'
        apply (rule exI[of _ op1'])
        apply (rule exI[of _ op2'])
        apply simp
        apply hypsubst_thin
        apply (subgoal_tac "(step Tau)\<^sup>*\<^sup>* (comp_op wire buf op op2) (comp_op wire (BENQ q x buf) op' op2)")
         defer
        subgoal
          by (metis wstep_Tau_comp_op_L wstep_steps_Tau)
        apply (smt (verit, ccfv_threshold) relcompp_apply rtranclp_trans wstep_def)
        done
      done
    done
  subgoal for p buf iosa ios1 ios2 buf' ios1' ios2' x op1 op2
    apply (rotate_tac 7)
    apply (erule wtraced.cases)
     apply simp_all
    subgoal for vio op op'
      apply (cases vio; simp)
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply safe
      subgoal for p' op1' op2'
        apply (rule exI[of _ op1'])
        apply (rule exI[of _ op2'])
        apply simp
        apply hypsubst_thin
        apply (subgoal_tac "(step Tau)\<^sup>*\<^sup>* (comp_op wire buf op1 op) (comp_op wire (BTL p buf) op1 op')")
         defer
        subgoal
          by (metis wstep_Tau_comp_op_R wstep_steps_Tau)
        apply (smt (verit) relcompp_apply rtranclp_trans wstep_def)
        done
      done
    done
  done

lemma wstep_comp_op_wfinished_preserve:
  "wstep io (comp_op wire buf op1 op2) op \<Longrightarrow>
   wfinished op1 \<Longrightarrow>
   wfinished op2 \<Longrightarrow>
   io \<noteq> Tau \<Longrightarrow>
   False"
  unfolding wstep_def
  apply (erule relcomppE)
  subgoal for op'
    apply (rotate_tac 3)
    apply (induct "comp_op wire buf op1 op2" arbitrary: buf op1 op2  rule: converse_rtranclp_induct)
    subgoal for buf op1 op2
      apply (cases io; simp; hypsubst_thin?)
      subgoal for p x
        apply (erule relcomppE)
        apply (elim step_comp_op_elim)
               apply auto
         apply (metis io_of_vio.simps(1) step_not_wfinished)+
        done
      subgoal for p x
        apply (erule relcomppE)
        apply (elim step_comp_op_elim)
               apply auto
         apply (metis io_of_vio.simps(2) step_not_wfinished)+
        done
      done
    subgoal for op' buf' op1' op2'
      apply simp
      apply (elim step_comp_op_elim)
             apply (auto dest: step_Tau_wfinished)
      subgoal
        by (metis io_of_vio.simps(2) step_not_wfinished)

      by (metis io_of_vio.simps(1) step_not_wfinished)
    done
  done

lemma
  "wtraced (comp_op wire buf op1 op2) ios = 
   (\<exists> ios1 ios2. wtraced op1 ios1 \<and> wtraced op2 ios2 \<and> causal wire buf ios ios1 ios2)"
  apply (rule iffI)
  subgoal
    apply (erule wtraced.cases; simp)
    subgoal
      by (intro exI[of _ LNil] conjI wtraced.intros causal.intros)
    subgoal for vio op op' lxs
      sorry
    done
  subgoal
    apply (elim exE conjE)
    subgoal for ios1 ios2
      apply (coinduction arbitrary: buf op1 op2 ios ios1 ios2 rule: wtraced.coinduct)
      subgoal for buf op1 op2 ios ios1 ios2
        apply (cases ios)
        subgoal
          by (simp add: lfilter_eq_LNil)
        subgoal for io ios
          apply (cases io)
          subgoal for p x
            apply simp
            apply hypsubst_thin
            apply (erule causal.cases)
             apply simp
            apply hypsubst_thin
            apply (drule visible_cause_wtraced_wstep)
               apply simp_all
            apply force
            done
          subgoal for p x
            apply simp
            apply hypsubst_thin
            apply (erule causal.cases)
            apply simp
            apply hypsubst_thin
            apply (drule visible_cause_wtraced_wstep)
            apply simp_all
            apply force
            done
          done
        done
      done
    done
  done


end