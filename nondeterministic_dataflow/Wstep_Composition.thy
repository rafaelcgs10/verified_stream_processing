theory Wstep_Composition

imports
  "BNA_Operators"
begin


inductive wstep_comp_op where
  \<open>comp_op wire buf' op1' op2' = comp_op wire buf op1 op2 \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1' op2 op2'\<close>
| \<open>step Tau op1 op1' \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1' op1'' op2 op2' \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1'' op2 op2'\<close>
| \<open>step Tau op2 op2' \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1' op2' op2'' \<Longrightarrow> wstep_comp_op Tau wire buf buf' op1 op1' op2 op2''\<close>
| \<open>wstep_comp_op Tau wire buf buf' op1 op1' op2 op2' \<Longrightarrow> step (Inp p x) op1' op1'' \<Longrightarrow> wstep_comp_op Tau wire buf' buf'' op1'' op1''' op2' op2'' \<Longrightarrow> wstep_comp_op (Inp (Inl p) x) wire buf buf'' op1 op1''' op2 op2''\<close>
| \<open>wstep_comp_op Tau wire buf buf' op1 op1' op2 op2' \<Longrightarrow>step (Out p x) op2' op2'' \<Longrightarrow> wstep_comp_op Tau wire buf' buf'' op1' op1'' op2'' op2''' \<Longrightarrow> wstep_comp_op (Out (Inr p) x) wire buf buf'' op1 op1'' op2 op2'''\<close>
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

inductive wstep_comp_op_L where
  \<open>io = Tau \<Longrightarrow> buf = (\<lambda>_. []) \<Longrightarrow> op' = op \<Longrightarrow> wstep_comp_op_L io wire buf op op'\<close>
| \<open>io = Inp (Inl p) x \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> wstep_comp_op_L Tau wire buf op' op'' \<Longrightarrow>
  wstep_comp_op_L io wire buf op op''\<close>
| \<open>io = Out (Inl p) x \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> p \<notin> dom wire \<Longrightarrow>
  wstep_comp_op_L Tau wire buf op' op'' \<Longrightarrow> wstep_comp_op_L io wire buf op op''\<close>
| \<open>step (Out p x) op op' \<Longrightarrow> p \<in> dom wire \<Longrightarrow> wstep_comp_op_L io wire buf op' op'' \<Longrightarrow>
  buf' = BENQ p x buf \<Longrightarrow> wstep_comp_op_L io wire buf' op op''\<close>
| \<open>step Tau op op' \<Longrightarrow> wstep_comp_op_L io wire buf op' op'' \<Longrightarrow> wstep_comp_op_L io wire buf op op''\<close>

inductive wstep_comp_op_R where
  \<open>io = Tau \<Longrightarrow> op' = op \<Longrightarrow> wstep_comp_op_R io wire buf op op'\<close>
| \<open>io = Inp (Inr p) x \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow>
  wstep_comp_op_R Tau wire buf op' op'' \<Longrightarrow> wstep_comp_op_R io wire buf op op''\<close>
| \<open>step (Inp p x) op op' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> wstep_comp_op_R io wire buf op' op'' \<Longrightarrow>
  buf p \<noteq> [] \<Longrightarrow> x = BHD p buf \<Longrightarrow> buf' = BTL p buf \<Longrightarrow> wstep_comp_op_R io wire buf' op op''\<close>
| \<open>io = Out (Inr p) x \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> wstep_comp_op_R Tau wire buf op' op'' \<Longrightarrow>
  wstep_comp_op_R io wire buf op op''\<close>
| \<open>step Tau op op' \<Longrightarrow> wstep_comp_op_R io wire buf op' op'' \<Longrightarrow> wstep_comp_op_R io wire buf op op''\<close>

lemma
  \<open>wstep io (comp_op wire buf op\<^sub>1 op\<^sub>2) op' \<longleftrightarrow>
  (\<exists>buf' buf'' buf''' op\<^sub>1' op\<^sub>2'. op' = comp_op wire buf' op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L io wire buf'' op\<^sub>1 op\<^sub>1' \<and> wstep_comp_op_R io wire buf''' op\<^sub>2 op\<^sub>2'
  \<and> (\<forall>p. \<exists>n \<le> length (buf p @ buf'' p). buf' p = drop n (buf p @ buf'' p) \<and> buf''' p = take n (buf p @ buf'' p)))\<close>
  oops

lemma
  \<open>wstep io (comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1 op\<^sub>2) op' \<longleftrightarrow>
  (\<exists>op\<^sub>1' op\<^sub>2'. op' = comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L io (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1 op\<^sub>1' \<and> wstep_comp_op_R io (\<lambda>_. None) (\<lambda>_. []) op\<^sub>2 op\<^sub>2')\<close>
  apply (intro iffI)
  subgoal
    sorry
  subgoal
    sorry
  oops

end