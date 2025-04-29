theory Wtraced_Composition

imports
  "BNA_Operators"
  Progress_Tracking.Antichain
    "HOL-Library.Finite_Map"
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

lemma wtraced_comp_op:
  "wtraced (comp_op wire buf op1 op2) ios = 
   (\<exists> ios1 ios2. wtraced op1 ios1 \<and> wtraced op2 ios2 \<and> causal wire buf ios ios1 ios2)"
  apply (rule iffI)
  subgoal
      sorry
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


lemma wtraced_map_op: 
 "inj_on f (inputs op) \<Longrightarrow>
  inj_on g (outputs op) \<Longrightarrow>
  wtraced (map_op f g op) lxs = (\<exists>lys. wtraced op lys \<and> lxs = lmap (map_VIO f g id) lys)"
  sorry


corec filter_op where
  "filter_op P buf = choice2 
   (Read (1 :: 1) (\<lambda> x. filter_op P (if P x then buf @ [x] else buf)))
   (if buf = [] then filter_op P buf else Write (filter_op P (tl buf)) (1 :: 1) (hd buf))"

coinductive production_spec for P where
  "production_spec P state LNil"
| "production_spec P state' lxs \<Longrightarrow> P state ins out state' \<Longrightarrow>
   (\<forall> x \<in> set ins. is_VInp x) \<Longrightarrow> (\<forall> x \<in> set out. \<not> is_VInp x) \<Longrightarrow>
   ins @ out \<noteq> [] \<Longrightarrow> production_spec P state (ins @@- out @@- lxs)"

lemma step_Inp_True_filter_op:
  "step io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   P x \<Longrightarrow>
   p = 1 \<and> op' = filter_op P (buf @ [x])"
  apply (induct io op op' arbitrary: buf pred: step)
     apply (subst (asm) filter_op.code, simp)    
    apply (subst (asm) filter_op.code, simp)
   apply (subst (asm) filter_op.code, simp)
  subgoal for op ops io op' buf
    apply hypsubst_thin
    apply (subst (asm) (3) filter_op.code)
    apply (auto split: op.splits list.splits if_splits ; hypsubst_thin)
    done
  done

lemma step_Inp_False_filter_op:
  "step io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   \<not> P x \<Longrightarrow>
   p = 1 \<and> op' = filter_op P buf"
  apply (induct io op op' arbitrary: buf pred: step)
     apply (subst (asm) filter_op.code, simp)    
    apply (subst (asm) filter_op.code, simp)
   apply (subst (asm) filter_op.code, simp)
  subgoal for op ops io op' buf
    apply hypsubst_thin
    apply (subst (asm) (3) filter_op.code)
    apply (auto split: op.splits list.splits if_splits ; hypsubst_thin)
    done
  done

lemma step_Tau_filter_op:
  "step io op op' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   False"
  apply (induct io op op' arbitrary: buf pred: step)
     apply (subst (asm) filter_op.code, simp)    
    apply (subst (asm) filter_op.code, simp)
   apply (subst (asm) filter_op.code, simp)
  subgoal for op ops io op' buf
    apply hypsubst_thin
    apply (subst (asm) (2) filter_op.code)
    apply (fastforce split: if_splits op.splits list.splits; hypsubst_thin)
    done
  done

lemma wstep_Inp_True_filter_op:
  "wstep io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   P x \<Longrightarrow>
   p = 1 \<and> op' = filter_op P (buf @ [x])"
  unfolding wstep_def
  apply (metis (mono_tags, lifting) converse_rtranclpE estep.simps(2) relcompp_apply step_Inp_True_filter_op step_Tau_filter_op)
  done

lemma wstep_Inp_False_filter_op:
  "wstep io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   \<not> P x \<Longrightarrow>
   p = 1 \<and> op' = filter_op P buf"
  unfolding wstep_def
  apply (metis converse_rtranclpE estep.simps(2) pick_middlep step_Inp_False_filter_op step_Tau_filter_op)
  done

lemma step_Out_filter_op:
  "step io op op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   p = 1 \<and> op' = filter_op P (tl buf) \<and> buf \<noteq> [] \<and> bhd buf = x"
  apply (induct io op op' arbitrary: buf pred: step)
     apply (subst (asm) filter_op.code, simp)    
    apply (subst (asm) filter_op.code, simp)
   apply (subst (asm) filter_op.code, simp)
  subgoal for op ops io op' buf
    apply hypsubst_thin
    apply (subst (asm) (3) filter_op.code)
    apply simp
    apply hypsubst_thin
    apply (elim disjE)
     apply hypsubst_thin
     apply force
    apply hypsubst_thin
    apply (cases buf; simp)
     apply blast
    apply (auto split: if_splits)
    done
  done

lemma step_Inp_True_filter_op_intro:
  "buf' = bulk_benq [x] buf \<Longrightarrow>
   P x \<Longrightarrow>
   step (Inp 1 x) (filter_op P buf) (filter_op P buf')"
  apply (subst filter_op.code)
  apply (simp split: if_splits)
  apply (intro conjI impI)
   apply (rule SC)
    apply (rule cinsertI1)
   apply (smt (verit, del_insts) SR self_append_conv2)
  apply (rule SC)
   apply (rule cinsertI1)
  apply (smt (verit, del_insts) SR self_append_conv2)
  done  

lemma step_Inp_False_filter_op_intro:
  "\<not> P x \<Longrightarrow>
   step (Inp 1 x) (filter_op P buf) (filter_op P buf)"
  apply (subst filter_op.code)
  apply (simp split: if_splits)
  apply (intro conjI impI)
   apply (rule SC)
    apply (rule cinsertI1)
   apply (smt (verit, del_insts) SR self_append_conv2)
  apply (rule SC)
   apply (rule cinsertI1)
  apply (smt (verit, del_insts) SR self_append_conv2)
  done  

lemma step_Out_filter_op_intro:
  "buf' = tl buf \<Longrightarrow>
   buf \<noteq> [] \<Longrightarrow>
   hd buf = x \<Longrightarrow>
   step (Out 1 x) (filter_op P buf) (filter_op P buf')"
  apply (subst filter_op.code)
  apply (simp split: if_splits)
  apply (rule SC)
   apply (rule cinsertI2)
   apply (rule cinsertI1)
  apply blast
  done

lemma wstep_Out_filter_op:
  "wstep io op op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   p = 1 \<and> op' = filter_op P (tl buf)\<and> buf \<noteq> [] \<and> bhd buf = x"
  unfolding wstep_def by (metis (no_types, lifting) converse_rtranclpE estep.simps(3) pick_middlep step_Out_filter_op step_Tau_filter_op)

term replicate

lemma wtraced_production_spec_soundness:
  "\<forall> x \<in> set buf. P x \<Longrightarrow>
   wtraced (filter_op P buf) lxs \<Longrightarrow>
   production_spec (\<lambda> buf inps outs buf'. (length outs = 1 \<and> inps = [] \<or> length inps = 1 \<and> outs = []) \<and> map (VOut 1) buf @ map (case_VIO VOut VOut) (filter (case_VIO (\<lambda> _ x. P x) \<top>) inps) = outs @ map (VOut 1) buf') buf lxs"
  apply (coinduction arbitrary: buf lxs rule: production_spec.coinduct)
  subgoal for buf lxs
    apply (erule wtraced.cases)
    subgoal for op
      by (cases buf; simp)
    subgoal for vio op op' lxs'
      apply hypsubst_thin
      apply (cases vio; simp; hypsubst_thin?)
      subgoal for p x
        apply (cases "P x")
        subgoal
          apply (rule exI[of _ "buf @ [x]"])
          apply (rule exI[of _ "lxs'"])
          apply (rule exI[of _ "[VInp p x]"])
          apply (rule exI[of _ "[]"])
          apply simp
          apply (intro disjI1 conjI)
          using wstep_Inp_True_filter_op apply force
          done
        subgoal
          apply (rule exI[of _ "buf"])
          apply (rule exI[of _ "lxs'"])
          apply (rule exI[of _ "[VInp p x]"])
          apply (rule exI[of _ "[]"])
          apply simp
          apply (intro disjI1 conjI)
          using wstep_Inp_False_filter_op apply force
          done
        done
      subgoal for p x
        apply (drule wstep_Out_filter_op)
          apply (rule refl)+
        apply safe
        apply (rule exI[of _ "btl buf"])
        apply (rule exI[of _ "lxs'"])
        apply (rule exI[of _ "[]"])
        apply (rule exI[of _ "[VOut p x]"])
        apply simp
        apply (intro disjI1 conjI)
         apply (metis list.set_sel(2))
        apply (metis (full_types) list.exhaust_sel list.simps(9) num1_eq1)
        done
      done
    done
  done  


lemma wtraced_production_spec_completeness:
  "\<forall> x \<in> set buf. P x \<Longrightarrow>
   production_spec (\<lambda> buf inps outs buf'. (length outs = 1 \<and> inps = [] \<or> length inps = 1 \<and> outs = []) \<and> map (VOut 1) buf @ map (case_VIO VOut VOut) (filter (case_VIO (\<lambda> _ x. P x) \<top>) inps) = outs @ map (VOut 1) buf') buf lxs \<Longrightarrow>
   wtraced (filter_op P buf) lxs"
  apply (coinduction arbitrary: buf lxs rule: wtraced.coinduct)
  subgoal for buf lxs
    apply (erule production_spec.cases)
    subgoal
      by blast
    subgoal for buf' lxs buf ins out
      apply hypsubst_thin
      apply (cases out; cases ins;  simp split: if_splits VIO.splits)
      subgoal for i p x
        apply (rule exI[of _ "filter_op P (buf @ [x])"])
        apply (intro conjI)
        subgoal
          apply hypsubst_thin
          using step_Inp_True_filter_op_intro apply (metis (full_types) num1_eq1 step_wstep)
          done
        apply (rule disjI1)
        apply (rule exI[of _ "buf @ [x]"])
        apply simp
         apply (smt (verit, best) Cons_eq_map_conv VIO.inject(2) list.inj_map_strong map_eq_append_conv map_is_Nil_conv)
        done
      subgoal for ins' p x
        apply hypsubst_thin
        apply (rule exI[of _ "filter_op P buf"])
        apply (intro conjI)
        subgoal
          using step_Inp_False_filter_op_intro apply (metis (full_types) num1_eq1 step_wstep)
          done
        apply (rule disjI1)
        apply (rule exI[of _ "buf"])
        apply simp
         apply (smt (verit, best) Cons_eq_map_conv VIO.inject(2) list.inj_map_strong map_eq_append_conv map_is_Nil_conv)
        done
      subgoal for oo 
        apply hypsubst_thin
        apply (cases oo; simp; hypsubst_thin)
        subgoal for p x
          apply (rule exI[of _ "filter_op P (tl buf)"])
          apply (intro conjI)
          subgoal
            using step_Out_filter_op_intro apply force
            done
          apply (rule disjI1)
          apply (rule exI[of _ "tl buf"])
          apply simp
          apply (intro conjI)
           apply force
           apply (smt (verit, ccfv_SIG) VIO.inject(2) list.inj_map_strong list.sel(3) map_tl)
          done
        done
      done
    done
  done

lemma filter_op_correctness:
  "\<forall>x\<in>set buf. P x \<Longrightarrow>
   wtraced (filter_op P buf) lxs = production_spec (\<lambda>buf inps outs buf'. (length outs = 1 \<and> inps = [] \<or> length inps = 1 \<and> outs = []) \<and> bulk_benq (map (case_VIO VOut VOut) (filter (case_VIO (\<lambda>_. P) \<top>) inps)) (map (VOut 1) buf) = bulk_benq (map (VOut 1) buf') outs) buf lxs"
  using wtraced_production_spec_completeness wtraced_production_spec_soundness by blast

simproc_setup num1_eq (\<open>x :: 1\<close>) =
  \<open>K (K (fn ct =>
    if Thm.term_of ct aconv @{term \<open>1 :: 1\<close>} then NONE
    else SOME (mk_meta_eq @{thm num1_eq1})))\<close>

lemma production_spec_coinduct:
  "X x1 x2 \<Longrightarrow>
(\<And>x1 x2.
    X x1 x2 \<Longrightarrow>
    (\<exists>state. x1 = state \<and> x2 = LNil) \<or>
    (\<exists>state' lxs state ins out.
        x1 = state \<and>
        x2 = ins @@- out @@- lxs \<and>
        (X state' lxs) \<and>
        P state ins out state' \<and> Ball (set ins) is_VInp \<and> (\<forall>x\<in>set out. \<not> is_VInp x) \<and> bulk_benq out ins \<noteq> [])) \<Longrightarrow>
  production_spec P x1 x2"
  apply (erule production_spec.coinduct)
  apply blast
  done


corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"

lemma foo[friend_of_corec_simps]:
  "(if snd (snd x) = [] then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x)))) else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x))))))) =
         (if snd (snd x) = []
         then if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
              else if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> \<not> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                   else if \<not> isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                        else ctor_op
                              (Abs_op_pre_op
                                (Inr (Inr (if isl (Rep_op_pre_op (dtor_op (fst x))) then undefined
                                           else if isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then undefined else projr (projr (Rep_op_pre_op (dtor_op (fst x))))))))
         else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x)))))))"
  by (auto split: if_splits)

friend_of_corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"
   apply (rule writes.code)
  apply transfer_prover
  done

lemma
  "\<forall>x\<in>set buf1. P x \<Longrightarrow>
   \<forall>x\<in>set buf2. P x \<Longrightarrow>
   \<forall>x\<in>set buf3. P x \<and> Q x \<Longrightarrow>
   wtraced (map_op projl projr (comp_op Some (\<lambda>_. buf2) (filter_op P buf1) (filter_op Q buf3))) lxs =
   production_spec (\<lambda>buf inps outs buf'. (length outs = 1 \<and> inps = [] \<or> length inps = 1 \<and> outs = []) \<and> bulk_benq (map (case_VIO VOut VOut) (filter (case_VIO (\<lambda>p x. P x \<and> Q x) \<top>) inps)) (map (VOut 1) buf) = bulk_benq (map (VOut 1) buf') outs) (buf3 @ filter Q (buf2 @ buf1)) lxs"
  unfolding scomp_op_def
  apply (subst wtraced_map_op)
  subgoal
    apply (rule inj_onI)
    apply auto
    done
  subgoal
    apply (rule inj_onI)
    apply auto
    done
  apply (subst wtraced_comp_op)
  apply (rule iffI)
  subgoal
    apply (elim conjE exE)
    apply hypsubst_thin
    subgoal for lys ios1 ios2
      apply (coinduction arbitrary: buf1 buf2 buf3 ios1 ios2 lys rule: production_spec_coinduct)
      subgoal for buf1 buf2 buf3 ios1 ios2 lys
        apply simp
        apply (erule causal.cases)
        subgoal
          by simp
        subgoal for buf' ios' ios1' ios2' ios buf ios1 ios2
          apply hypsubst_thin
          apply simp
          apply (rule disjI2)
          subgoal premises prems
            using prems(8,1-7) apply -
            apply (induct "\<lambda> _ :: 1. buf2" ios ios1 ios2 buf' ios' ios1' ios2' arbitrary: buf1 buf2 buf3 rule: visible_cause.induct)
                 apply simp_all
            subgoal for x iosa ios1 ios2 buf2 buf1 buf3
              apply (cases "P x"; cases "Q x")
              subgoal
                apply (rule exI)
                apply (rule exI[of _ "lmap (map_VIO projl projr id) iosa"])
                apply (rule exI[of _ "[VInp 1 x]"])
                apply (rule exI[of _ "[]"])
                apply simp
                apply (intro conjI)
                 apply (rule exI[of _ "buf1 @ [x]"])
                 apply (intro exI)
                 apply (intro conjI)
                  apply (rule refl)
                 apply (intro conjI exI)
                       apply (rule refl)+
                      apply simp_all
                apply (subst filter_op_correctness)
                 apply simp
                apply (subst (asm) filter_op_correctness)
                 apply simp
                apply (erule production_spec.cases)
                 apply auto
                 apply (metis (no_types, lifting) VIO.discI(1) list.set_intros(1) llist.inject lshift.elims)
                subgoal for state' lxs ins
                  apply (cases ins; simp; hypsubst_thin)
                  apply (smt (z3) VIO.inject(2) length_0_conv length_map list.inj_map_strong map_eq_Cons_D map_eq_append_conv)
                  done
                done
              subgoal
                apply (rule exI)
                apply (rule exI[of _ "lmap (map_VIO projl projr id) iosa"])
                apply (rule exI[of _ "[VInp 1 x]"])
                apply (rule exI[of _ "[]"])
                apply simp
                apply (intro conjI)
                 apply (rule exI[of _ "buf1 @ [x]"])
                 apply (intro exI)
                 apply (intro conjI)
                  apply (rule refl)
                 apply (intro conjI exI)
                       apply (rule refl)+
                      apply simp_all
                apply (subst filter_op_correctness)
                 apply simp
                apply (subst (asm) filter_op_correctness)
                 apply simp
                apply (erule production_spec.cases)
                 apply auto
                 apply (metis (no_types, lifting) VIO.discI(1) list.set_intros(1) llist.inject lshift.elims)
                subgoal for state' lxs ins
                  apply (cases ins; simp; hypsubst_thin)
                  apply (smt (z3) VIO.inject(2) length_0_conv length_map list.inj_map_strong map_eq_Cons_D map_eq_append_conv)
                  done
                done
              subgoal
                apply (rule exI)
                apply (rule exI[of _ "lmap (map_VIO projl projr id) iosa"])
                apply (rule exI[of _ "[VInp 1 x]"])
                apply (rule exI[of _ "[]"])
                apply simp
                apply (intro conjI)
                 apply (rule exI[of _ "buf1"])
                 apply (intro exI)
                 apply (intro conjI)
                  apply (rule refl)
                 apply (intro conjI exI)
                       apply (rule refl)+
                      apply simp_all
                apply (subst filter_op_correctness)
                 apply simp
                apply (subst (asm) filter_op_correctness)
                 apply simp
                apply (erule production_spec.cases)
                 apply auto
                 apply (metis (no_types, lifting) VIO.discI(1) list.set_intros(1) llist.inject lshift.elims)
                subgoal for state' lxs ins
                  apply (cases ins; simp; hypsubst_thin)
                  apply (smt (z3) VIO.inject(2) length_0_conv length_map list.inj_map_strong map_eq_Cons_D map_eq_append_conv)
                  done
                done
              subgoal
                apply (rule exI)
                apply (rule exI[of _ "lmap (map_VIO projl projr id) iosa"])
                apply (rule exI[of _ "[VInp 1 x]"])
                apply (rule exI[of _ "[]"])
                apply simp
                apply (intro conjI)
                 apply (rule exI[of _ "buf1"])
                 apply (intro exI)
                 apply (intro conjI)
                  apply (rule refl)
                 apply (intro conjI exI)
                       apply (rule refl)+
                      apply simp_all
                apply (subst filter_op_correctness)
                 apply simp
                apply (subst (asm) filter_op_correctness)
                 apply simp
                apply (erule production_spec.cases)
                 apply auto
                 apply (metis (no_types, lifting) VIO.discI(1) list.set_intros(1) llist.inject lshift.elims)
                subgoal for state' lxs ins
                  apply (cases ins; simp; hypsubst_thin)
                  apply (smt (z3) VIO.inject(2) length_0_conv length_map list.inj_map_strong map_eq_Cons_D map_eq_append_conv)
                  done
                done
              done
            subgoal for x iosa ios1 ios2 buf2 buf1 buf3
              apply (rule exI)
              apply (rule exI[of _ "lmap (map_VIO projl projr id) iosa"])
              apply (rule exI[of _ "[]"])
              apply (rule exI[of _ "[VOut 1 x]"])
              apply simp
              apply (intro conjI)
               apply (rule exI[of _ "buf1"])
               apply (rule exI[of _ "buf2"])
               apply (rule exI[of _ "tl buf3"])
               apply (intro conjI)
                apply (rule refl)
               apply (intro conjI exI)
                     apply (rule refl)+
                    apply simp_all
                apply (metis list.sel(2) list.set_sel(2))
               apply (metis io_of_vio.simps(2) wstep_Out_filter_op wtraced_StepE)
              apply (metis io_of_vio.simps(2) list.exhaust_sel list.simps(9) wstep_Out_filter_op wtraced_StepE)
              done
            subgoal premises prems for x ios ios1 ios2 buf' ios1' ios2' buf2 buf1 buf3
              using prems(1,3-) prems(2)[where ?buf2.0="buf2 @ [x]" and ?buf1.0="tl buf1" and ?buf3.0=buf3] apply (auto simp: fun_eq_iff)
              apply (drule meta_mp)
               apply (metis list.sel(2) list.set_sel(2))
              apply (drule meta_mp)
               apply (metis list.collapse list.set_intros(1) wstep_Out_filter_op)
              apply (drule meta_mp)
               apply (metis wstep_Out_filter_op)
              apply (elim exE conjE)
              subgoal for op' state' lxs ins out buf1 buf2 buf3 ios1 ios2 lys
                apply (rule exI[of _ state'])
                apply (rule exI[of _ "lmap (map_VIO projl projr id) lys"])
                apply (rule exI[of _ ins])
                apply (rule exI[of _ out])
                apply simp
                apply (intro conjI)
                subgoal
                  apply (rule exI[of _ buf1])
                  apply (rule exI[of _ buf2])
                  apply (rule exI[of _ buf3])
                  apply auto
                  done
                apply (simp split: if_splits)
                 apply (smt (verit, best) append_Cons filter.simps(2) list.collapse list.simps(9) wstep_Out_filter_op)+
                done
              done
            subgoal premises prems for ios ios1 ios2 buf' ios1' ios2' x buf2 buf1 buf3
              apply (cases "Q x")
              subgoal
                using prems(1,3-) prems(2)[where ?buf2.0="tl buf2" and ?buf3.0="buf3 @ [x]" and ?buf1.0=buf1] apply (auto simp: fun_eq_iff)
                apply (drule meta_mp)
                 apply (meson BTL_access)
                apply (drule meta_mp)
                 apply (meson list.set_sel(2))
                apply (drule meta_mp)
                 apply (metis BHD_def list.set_sel(1))
                apply (drule meta_mp)
                 apply (metis wstep_Inp_True_filter_op)
                apply (elim exE conjE)
                subgoal for op' state' lxs ins out buf1 buf2 buf3 ios1 ios2 lys
                  apply hypsubst
                  apply (rule exI[of _ state'])
                  apply (rule exI[of _ "lmap (map_VIO projl projr id) lys"])
                  apply (rule exI[of _ ins])
                  apply (rule exI[of _ out])
                  apply simp
                  apply (intro conjI)
                  subgoal
                    apply (rule exI[of _ buf1])
                    apply (rule exI[of _ buf2])
                    apply (rule exI[of _ buf3])
                    apply auto
                    done
                  subgoal
                    by (smt (verit, best) BHD_def append_Cons filter.simps(2) list.exhaust_sel list.simps(9))
                  done
                done
              subgoal
                using prems(1,3-) prems(2)[where ?buf2.0="tl buf2" and ?buf3.0="buf3" and ?buf1.0=buf1] apply (auto simp: fun_eq_iff)
                apply (drule meta_mp)
                 apply (meson BTL_access)
                apply (drule meta_mp)
                 apply (meson list.set_sel(2))
                apply (drule meta_mp)
                 apply (metis wstep_Inp_False_filter_op)
                apply (elim exE conjE)
                subgoal for op' state' lxs ins out buf1 buf2 buf3 ios1 ios2 lys
                  apply hypsubst
                  apply (rule exI[of _ state'])
                  apply (rule exI[of _ "lmap (map_VIO projl projr id) lys"])
                  apply (rule exI[of _ ins])
                  apply (rule exI[of _ out])
                  apply simp
                  apply (intro conjI)
                  subgoal
                    apply (rule exI[of _ buf1])
                    apply (rule exI[of _ buf2])
                    apply (rule exI[of _ buf3])
                    apply auto
                    done
                  apply hypsubst_thin
                  apply (smt (verit) BHD_def filter.simps(2) list.collapse)
                  done
                done
              done
            done
          done
        done
      done
    done
  subgoal
    sorry
  done
         
definition
  map_merge :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "map_merge f m1 m2 = (\<lambda>x. case m2 x of None \<Rightarrow> m1 x | Some y \<Rightarrow> (case m1 x of None \<Rightarrow> Some y | Some y' \<Rightarrow> Some (f y' y)))"

lemma map_merge_empty[simp]: "map_merge f m Map.empty = m"
  by(simp add: map_merge_def)

lemma empty_map_merge[simp]: "map_merge f Map.empty m = m"
  by (rule ext) (simp add: map_merge_def split: option.split)

datatype 'p channel = Time 'p | Data 'p
            
term restrict_map

term map_upds

find_consts "(_, _) fmap" "_ list"

corec max_op where
  "max_op impli stash = 
   choice2
   (Read (Time 1 :: 1 channel) (\<lambda> t. max_op (add_zmset (fst t) impli) stash))
   (pull (Data 1 :: 1 channel)(\<lambda> x. let
      impl_frontier = frontier impli ;
      stash = case x of Some x \<Rightarrow> x # stash | None \<Rightarrow> stash  
    in max_op impli stash))"




end