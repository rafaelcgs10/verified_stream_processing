theory T3A1

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Branching bisimulation\<close>

definition \<open>brsim R op\<^sub>1 op\<^sub>2 =
  (\<forall>io op\<^sub>1'. step io op\<^sub>1 op\<^sub>1' \<longrightarrow>
    (\<exists>op\<^sub>2' op\<^sub>2'' op\<^sub>2'''. (step Tau)\<^sup>*\<^sup>* op\<^sub>2 op\<^sub>2' \<and> estep io op\<^sub>2' op\<^sub>2'' \<and> (step Tau)\<^sup>*\<^sup>* op\<^sub>2'' op\<^sub>2''' \<and>
    R op\<^sub>1 op\<^sub>2' \<and> R op\<^sub>1' op\<^sub>2'' \<and> R op\<^sub>1' op\<^sub>2'''))\<close>

lemma brsim_mono[mono]: \<open>R \<le> S \<Longrightarrow> brsim R \<le> brsim S\<close>
  by (force simp: brsim_def le_fun_def)

coinductive brbisim (infix \<open>\<approx>\<^sub>b\<close> 40) where
  \<open>brsim (\<approx>\<^sub>b) op\<^sub>1 op\<^sub>2 \<Longrightarrow> brsim (\<approx>\<^sub>b) op\<^sub>2 op\<^sub>1 \<Longrightarrow> op\<^sub>1 \<approx>\<^sub>b op\<^sub>2\<close>

lemma brsim_wsim:
  \<open>brsim R op\<^sub>1 op\<^sub>2 \<Longrightarrow> wsim R op\<^sub>1 op\<^sub>2\<close>
  unfolding brsim_def wsim_def wstep_def
  by (meson relcomppI)

lemma brbisim_wbisim:
  \<open>op\<^sub>1 \<approx>\<^sub>b op\<^sub>2 \<Longrightarrow> op\<^sub>1 \<approx> op\<^sub>2\<close>
  by (smt (verit, ccfv_threshold) brbisim.cases brsim_def brsim_wsim wbisim.coinduct)

section \<open>Proof against weak bisimulation\<close>

lemma wstep_Inp_Inl_Inl:
  assumes \<open>wstep (Inp (Inl (Inl 1)) (Suc 0)) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) \<V>))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)
  subgoal
    apply hypsubst_thin
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin; simp; hypsubst_thin)
    apply (erule converse_rtranclpE)
     apply (metis (full_types) num1_eq1)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin; simp; hypsubst_thin)
    apply (erule converse_rtranclpE)
    subgoal for p _ _ p'
      apply (rule disjI2)
      apply (rule disjI1)
      apply (cases \<open>p = p'\<close>, cases \<open>p = 1\<close>)
      sorry
    subgoal
      sorry
    done
  subgoal by (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
  done

lemma wstep_Inp_Inl_Inr1:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 (Suc 0) (\<lambda>_. []))) (\<V> :: (1 + 1, 1, nat) op)) \<V>))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) (merge_op (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))))))\<close>
  sorry

lemma wstep_Inp_Inl_Inr2:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 (Suc 0) (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) \<V>))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))))))\<close>
  sorry

lemma wstep_Inp_Inl_Inr3:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) (merge_op (case_sum (BENQ 1 (Suc 0) (\<lambda>_. [])) (\<lambda>_. [])))))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))))))\<close>
  sorry

lemma wstep_trans':
  \<open>step (Out p x) op op' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* op' op'' \<Longrightarrow> wstep (Out p x) op op''\<close>
  \<open>step (Inp p' x') op op' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* op' op'' \<Longrightarrow> wstep (Inp p' x') op op''\<close>
  unfolding wstep_def
  by blast+

lemma
  \<open>(\<V> \<parallel> (\<I> :: (1, 1, nat) op)) \<bullet> \<V> \<approx> map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>) \<Longrightarrow> False\<close>
  unfolding scomp_op_def pcomp_op_def
  apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inl 1)) 1\<close>])
   apply (rule wstep_trans'(2))
    apply (rule step_map_op)
     apply (rule step_comp_op_L_Inp)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_merge_op_Read_L[of 1])
          apply (simp_all add: defaults_num1_def flip: case_sum_BENQ_L)
   apply (rule rtranclp.intros(2))
    apply (rule rtranclp.intros(2))
     apply (rule rtranclp.intros(1))
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_L)
        apply (rule step_comp_op_L_Out)
           apply (rule step_merge_op_Write_L[of 1])
              apply (simp_all add: defaults_num1_def)
   apply (rule step_map_op)
    apply (rule step_Tau_comp_op_R)
         apply (rule step_merge_op_Read_L[of 1])
          apply (simp_all add: defaults_num1_def)
  apply (erule wstep_Inp_Inl_Inl; clarsimp)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
     apply (rule wstep_trans'(2))
      apply (rule step_map_op)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_merge_op_Read_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply (rule rtranclp.intros(2))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(1))
      apply (rule step_map_op)
       apply (rule step_Tau_comp_op_L)
          apply (rule step_comp_op_L_Out)
             apply (rule step_merge_op_Write_R[of 1])
                apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Tau_comp_op_R)
           apply (rule step_merge_op_Read_L[of 1])
            apply (simp_all add: defaults_num1_def)
    apply (erule wstep_Inp_Inl_Inr1; clarsimp; drule wbisim_sym)
            apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
             apply (rule wstep_trans(1))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(1))
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_L)
                    apply (rule step_comp_op_R_Out)
                      apply (rule step_merge_op_Write_L[of 1])
                      apply (simp_all add: defaults_num1_def)
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_merge_op_Read_R[of 1])
                      apply (simp_all add: defaults_num1_def)
             apply (rule step_map_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_R[of 1])
                    apply (simp_all add: defaults_num1_def)
             apply simp
            apply (unfold wstep_def)
            apply (erule relcomppE)+
            apply (erule converse_rtranclpE)
             apply (hypsubst_thin; simp)
             apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
             apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
            apply (simp add: BENQ_diff_access)
           apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
            apply (rule wstep_trans(1))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(1))
             apply (rule step_map_op)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_R)
                    apply (rule step_merge_op_Read_R[of 1])
                     apply (simp_all add: defaults_num1_def)
            apply (rule step_map_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Out)
                apply (rule step_merge_op_Write_R[of 1])
                   apply (simp_all add: defaults_num1_def)
            apply simp
           apply (unfold wstep_def)
           apply (erule relcomppE)+
           apply (erule converse_rtranclpE)
            apply (hypsubst_thin; simp)
            apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
            apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
           apply (simp add: BENQ_diff_access)
          apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
           apply (rule step_wstep)
           apply (rule step_map_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Out)
               apply (rule step_merge_op_Write_R[of 1])
                  apply (simp_all add: defaults_num1_def)
           apply simp
          apply (unfold wstep_def)
          apply (erule relcomppE)+
          apply (erule converse_rtranclpE)
           apply (hypsubst_thin; simp)
           apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
           apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
          apply (simp add: BENQ_diff_access)
         apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
          apply (rule wstep_trans(1))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(1))
            apply (rule step_map_op)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_L)
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_merge_op_Write_L[of 1])
                      apply (simp_all add: defaults_num1_def)
           apply (rule step_map_op)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_R)
                  apply (rule step_merge_op_Read_R[of 1])
                   apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_merge_op_Write_R[of 1])
                 apply (simp_all add: defaults_num1_def)
          apply simp
         apply (unfold wstep_def)
         apply (erule relcomppE)+
         apply (erule converse_rtranclpE)
          apply (hypsubst_thin; simp)
          apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
          apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
         apply (simp add: BENQ_diff_access)
        apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
         apply (rule wstep_trans(1))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_merge_op_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Out)
             apply (rule step_merge_op_Write_R[of 1])
                apply (simp_all add: defaults_num1_def)
         apply simp
        apply (unfold wstep_def)
        apply (erule relcomppE)+
        apply (erule converse_rtranclpE)
         apply (hypsubst_thin; simp)
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
         apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
        apply (simp add: BENQ_diff_access)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
            apply (rule step_merge_op_Write_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply simp
       apply (unfold wstep_def)
       apply (erule relcomppE)+
       apply (erule converse_rtranclpE)
        apply (hypsubst_thin; simp)
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
        apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
       apply (simp add: BENQ_diff_access)
      apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
       apply (rule wstep_trans(1))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_R_Out)
                apply (rule step_merge_op_Write_L[of 1])
                   apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_R)
               apply (rule step_merge_op_Read_R[of 1])
                apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op_Write_R[of 1])
              apply (simp_all add: defaults_num1_def)
       apply simp
      apply (unfold wstep_def)
      apply (erule relcomppE)+
      apply (erule converse_rtranclpE)
       apply (hypsubst_thin; simp)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
       apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
      apply (simp add: BENQ_diff_access)
     apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
      apply (rule wstep_trans(1))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_merge_op_Read_R[of 1])
               apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_map_op)
        apply (rule step_comp_op_R_Out)
          apply (rule step_merge_op_Write_R[of 1])
             apply (simp_all add: defaults_num1_def)
      apply simp
     apply (unfold wstep_def)
     apply (erule relcomppE)+
     apply (erule converse_rtranclpE)
      apply (hypsubst_thin; simp)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
      apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
     apply (simp add: BENQ_diff_access)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
     apply (rule step_wstep)
     apply (rule step_map_op)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Out)
         apply (rule step_merge_op_Write_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply simp
    apply (unfold wstep_def)
    apply (erule relcomppE)+
    apply (erule converse_rtranclpE)
     apply (hypsubst_thin; simp)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
     apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
    apply (simp add: BENQ_diff_access)
   apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
    apply (rule wstep_trans'(2))
     apply (rule step_map_op)
      apply (rule step_comp_op_L_Inp)
        apply (rule step_comp_op_L_Inp)
          apply (rule step_merge_op_Read_R[of 1])
           apply (simp_all add: defaults_num1_def)
    apply (rule rtranclp.intros(2))
     apply (rule rtranclp.intros(2))
      apply (rule rtranclp.intros(1))
     apply (rule step_map_op)
      apply (rule step_Tau_comp_op_L)
         apply (rule step_comp_op_L_Out)
            apply (rule step_merge_op_Write_R[of 1])
               apply (simp_all add: defaults_num1_def)
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_R)
          apply (rule step_merge_op_Read_L[of 1])
           apply (simp_all add: defaults_num1_def)
   apply (erule wstep_Inp_Inl_Inr2; clarsimp; drule wbisim_sym)
        apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
         apply (rule wstep_trans(1))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_L)
                apply (rule step_comp_op_R_Out)
                  apply (rule step_merge_op_Write_L[of 1])
                     apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_merge_op_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Out)
             apply (rule step_merge_op_Write_R[of 1])
                apply (simp_all add: defaults_num1_def)
         apply simp
        apply (unfold wstep_def)
        apply (erule relcomppE)+
        apply (erule converse_rtranclpE)
         apply (hypsubst_thin; simp)
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
         apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
        apply (simp add: BENQ_diff_access)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op_Read_R[of 1])
                 apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
            apply (rule step_merge_op_Write_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply simp
       apply (unfold wstep_def)
       apply (erule relcomppE)+
       apply (erule converse_rtranclpE)
        apply (hypsubst_thin; simp)
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
        apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
       apply (simp add: BENQ_diff_access)
      apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
       apply (rule step_wstep)
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op_Write_R[of 1])
              apply (simp_all add: defaults_num1_def)
       apply simp
      apply (unfold wstep_def)
      apply (erule relcomppE)+
      apply (erule converse_rtranclpE)
       apply (hypsubst_thin; simp)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
       apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
      apply (simp add: BENQ_diff_access)
     apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
      apply (rule wstep_trans(1))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_comp_op_R_Out)
               apply (rule step_merge_op_Write_L[of 1])
                  apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_merge_op_Read_R[of 1])
               apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_map_op)
        apply (rule step_comp_op_R_Out)
          apply (rule step_merge_op_Write_R[of 1])
             apply (simp_all add: defaults_num1_def)
      apply simp
     apply (unfold wstep_def)
     apply (erule relcomppE)+
     apply (erule converse_rtranclpE)
      apply (hypsubst_thin; simp)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
      apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
     apply (simp add: BENQ_diff_access)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(1))
      apply (rule step_map_op)
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_R)
             apply (rule step_merge_op_Read_R[of 1])
              apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Out)
         apply (rule step_merge_op_Write_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply simp
    apply (unfold wstep_def)
    apply (erule relcomppE)+
    apply (erule converse_rtranclpE)
     apply (hypsubst_thin; simp)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
     apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
    apply (simp add: BENQ_diff_access)
   apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
    apply (rule step_wstep)
    apply (rule step_map_op)
     apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
        apply (rule step_merge_op_Write_R[of 1])
           apply (simp_all add: defaults_num1_def)
    apply simp
   apply (unfold wstep_def)
   apply (erule relcomppE)+
   apply (erule converse_rtranclpE)
    apply (hypsubst_thin; simp)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
    apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
   apply (simp add: BENQ_diff_access)
  apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
   apply (rule wstep_trans'(2))
    apply (rule step_map_op)
     apply (rule step_comp_op_L_Inp)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_merge_op_Read_R[of 1])
          apply (simp_all add: defaults_num1_def)
   apply (rule rtranclp.intros(2))
    apply (rule rtranclp.intros(2))
     apply (rule rtranclp.intros(1))
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_L)
        apply (rule step_comp_op_L_Out)
           apply (rule step_merge_op_Write_R[of 1])
              apply (simp_all add: defaults_num1_def)
   apply (rule step_map_op)
    apply (rule step_Tau_comp_op_R)
         apply (rule step_merge_op_Read_L[of 1])
          apply (simp_all add: defaults_num1_def)
  apply (erule wstep_Inp_Inl_Inr3; clarsimp; drule wbisim_sym)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_comp_op_R_Out)
              apply (rule step_merge_op_Write_L[of 1])
                 apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_R)
             apply (rule step_merge_op_Read_R[of 1])
              apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Out)
         apply (rule step_merge_op_Write_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply simp
    apply (unfold wstep_def)
    apply (erule relcomppE)+
    apply (erule converse_rtranclpE)
     apply (hypsubst_thin; simp)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
     apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
  apply (simp add: BENQ_diff_access)
   apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
    apply (rule wstep_trans(1))
     apply (rule rtranclp.intros(2))
      apply (rule rtranclp.intros(1))
     apply (rule step_map_op)
      apply (rule step_map_op)
       apply (rule step_Tau_comp_op_R)
            apply (rule step_merge_op_Read_R[of 1])
             apply (simp_all add: defaults_num1_def)
    apply (rule step_map_op)
     apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
        apply (rule step_merge_op_Write_R[of 1])
           apply (simp_all add: defaults_num1_def)
    apply simp
   apply (unfold wstep_def)
   apply (erule relcomppE)+
   apply (erule converse_rtranclpE)
    apply (hypsubst_thin; simp)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
    apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
  apply (simp add: BENQ_diff_access)
  apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
   apply (rule step_wstep)
   apply (rule step_map_op)
    apply (rule step_map_op)
     apply (rule step_comp_op_R_Out)
       apply (rule step_merge_op_Write_R[of 1])
          apply (simp_all add: defaults_num1_def)
   apply simp
  apply (unfold wstep_def)
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)
   apply (hypsubst_thin; simp)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
   apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
  apply (simp add: BENQ_diff_access)
  done