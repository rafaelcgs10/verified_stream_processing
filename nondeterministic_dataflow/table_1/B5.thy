theory B5

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B5: Parallel and sequential distributes\<close>

lemma pcomp_op_scomp_distributes_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf1 buf2) (op1 \<parallel> op2) (op3 \<parallel> op4))
  ~ (map_op projl projr (comp_op Some buf1 op1 op3)) \<parallel> (map_op projl projr (comp_op Some buf2 op2 op4))\<close>
  apply (coinduction arbitrary: buf1 buf2 op1 op2 op3 op4 rule: bisim_coinduct_upto)
  subgoal for buf1 buf2 op1 op2 op3 op4
    unfolding sim_def pcomp_op_def
    apply auto
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal 
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal 
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p' op4'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1 op1 op3))
             (map_op projl projr (comp_op Some buf2 op2 op4'))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply fast
          done
        subgoal for p' op3'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1 op1 op3'))
             (map_op projl projr (comp_op Some buf2 op2 op4))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done     
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done     
        done
      subgoal for p op2'
        apply hypsubst_thin
        apply (cases p)
         apply simp_all
        subgoal
          apply (drule step_comp_op_cases)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply (rule step_comp_op_L_Tau)
            apply auto
          done
        subgoal
          apply (drule step_comp_op_cases)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply (rule step_comp_op_R_Tau)
            apply auto
          done
        done
      subgoal
        apply hypsubst_thin
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      subgoal
        apply hypsubst_thin
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      done
    subgoal for io
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op1'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf1 buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2)
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) op3 op4))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op4'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf1 buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2)
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) op3 op4'))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op3'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf1 buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2)
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) op3' op4))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op2'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf1 buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2')
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) op3 op4))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
           apply hypsubst_thin
        subgoal
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_comp_op_R_Inp)
                   apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      done
    done
  done

lemma B5:
  \<open>(op1 \<parallel> op2) \<bullet> (op3 \<parallel> op4) ~ (op1 \<bullet> op3) \<parallel> (op2 \<bullet> op4)\<close>
  unfolding scomp_op_def
  using pcomp_op_scomp_distributes_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by auto

end