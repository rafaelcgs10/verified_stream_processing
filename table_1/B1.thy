theory B1

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B1: Associativity of parallel composition\<close>
lemma B1:
  \<open>op1 \<parallel> (op2 \<parallel> op3) ~ map_op reassoc reassoc ((op1 \<parallel> op2) \<parallel> op3)\<close>
  apply (coinduction arbitrary: op1 op2 op3 rule: bisim_coinduct_upto)
  unfolding pcomp_op_def sim_def
  subgoal for op1 op2 op3
    apply auto
    subgoal for io
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x op1'
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_base)
         apply auto
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for pr op3'
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply auto
          done
        subgoal
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply auto
          done
        done
      subgoal 
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_base)
         apply auto
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
           apply (rule step_comp_op_L_Inp)
             apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      subgoal
        apply hypsubst_thin
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal
        apply hypsubst_thin
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      done
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for pl op1'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        subgoal for pr op2'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2' op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal for p x op3'
        apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3')\<close>])
        apply auto
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for pr op2'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2' op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        subgoal for pl op1'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal for p x op3'
        apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3')\<close>])
        apply (rule conjI)
         apply fastforce
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      subgoal
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op1'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        subgoal for op2'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2' op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal for op3'
        apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3')\<close>])
        apply (rule conjI)
         apply auto
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      done
    done
  done

end