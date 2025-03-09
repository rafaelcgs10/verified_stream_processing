theory B6

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B6: Parallel composition of identities\<close>

lemma pcomp_op_id_id_bufs:
  \<open>id_op buf1 \<parallel> id_op buf2 ~ id_op (case_sum buf1 buf2)\<close>
  apply (coinduction arbitrary: buf1 buf2 rule: bisim_coinduct_upto)
  subgoal for buf1 buf2
    unfolding pcomp_op_def sim_def
    apply auto
    subgoal for io op
      apply (drule step_comp_op_cases)
      apply auto
      subgoal
        apply (drule step_id_op_Inp)
         apply auto
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply blast
        apply (metis Inr_Inl_False PlusE Plus_def case_sum_BENQ_L defaults_sum_def step_id_op_Read sum.sel(1))
        done
      subgoal 
        apply (drule step_id_op_Out)
         apply auto
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal 
        apply (drule step_id_op_Out)
         apply auto
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal
        apply (drule step_id_op_Inp)
         apply auto
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply blast
        apply (metis Inr_Inl_False Inr_inject PlusE Plus_def case_sum_BENQ_R defaults_sum_def step_id_op_Read)
        done
      done
    subgoal for io op
      apply (cases io)
      subgoal for p x
        apply (cases p)
        subgoal for lp
          apply (drule step_id_op_Inp)
           apply auto
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (auto simp add: defaults_sum_def step_comp_op_L_Inp step_id_op_Read)
          done
        subgoal for p
          apply (drule step_id_op_Inp)
           apply auto
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (rule step_comp_op_R_Inp)
             apply auto
          done
        done
      subgoal for p x
        apply (cases p)
        subgoal
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (simp add: defaults_sum_def image_iff step_comp_op_L_Out step_id_op_Write)
          done
        subgoal
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (simp add: defaults_sum_def image_iff step_comp_op_R_Out step_id_op_Write)
          done
        done
      subgoal
        by force
      done
    done
  done


lemma B6:
  \<open>\<I> \<parallel> \<I> ~ \<I>\<close>
  using pcomp_op_id_id_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end