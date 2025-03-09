theory B2

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)



section \<open>Axiom B2: Neutral element of parallel composition\<close>
lemma B2_1:
  \<open>map_op projl projl (op \<parallel> \<oslash>) ~ op\<close>
  apply (coinduction arbitrary: op rule: bisim_coinduct_upto)
  subgoal for op
    unfolding pcomp_op_def sim_def
    apply auto
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply (auto simp: bc_base)
      done
    subgoal for io op'
      apply (rule exI[of _ \<open>map_op projl projl (comp_op (\<lambda>_. None) (\<lambda>_. []) op' \<oslash>)\<close>])
      apply (cases io)
        apply auto
      subgoal for p x
        apply (drule step_comp_op_L_Inp)
          apply (simp_all add: bc_base bc_sym)
        done
      subgoal for p x
        apply (drule step_comp_op_L_Out[of _ _ _ _ \<open>\<lambda>_. None\<close>])
           apply (simp_all add: bc_base bc_sym)
        done
      subgoal
        apply (drule step_comp_op_L_Tau)
          apply (simp_all add: bc_base bc_sym)
        done
      done
    done
  done

lemma B2_2:
  \<open>map_op projr projr (\<oslash> \<parallel> op) ~ op\<close>
  apply (coinduction arbitrary: op rule: bisim_coinduct_upto)
  subgoal for op
    unfolding pcomp_op_def sim_def
    apply auto
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply (auto simp: bc_base)
      done
    subgoal for io op'   
      apply (cases io)
      subgoal
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_sym)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_sym)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_sym)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      done
    done
  done

end