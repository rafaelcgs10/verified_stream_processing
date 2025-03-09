theory B10

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B10: Transpose commutes with sequential composition of parallel operators\<close>
lemma B10_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf1''' buf2''')
    (map_op projl projr (comp_op Some buf1' (id_op buf1) op1) \<parallel> map_op projl projr (comp_op Some buf2' (id_op buf2) op2))
    (transp_op (case_sum buf1'' buf2'')))
  \<approx> map_op projl projr (comp_op Some (case_sum buf2' buf1')
    (transp_op (case_sum buf1 buf2))
    (map_op projl projr (comp_op Some buf2''' op2 (id_op buf2'')) \<parallel> map_op projl projr (comp_op Some buf1''' op1 (id_op buf1''))))\<close>
  apply (coinduction arbitrary: op1 op2 buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' rule: wbisim_coinduct_upto)
  subgoal for op1 op2 buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2'''
    unfolding wsim_def pcomp_op_def
    apply auto
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Inp)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          apply auto
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Inp)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          apply auto
          done
        done
      subgoal for p x
        apply (erule step_transp_op_Out)
          apply (auto split: sum.splits)
        subgoal for p'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          apply auto
          done
        subgoal for p'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          apply auto
          done
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op2'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force
            apply auto
            done
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op1'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          done
        done
      subgoal for p
        apply (erule step_transp_op_Inp)
         apply (auto split: sum.splits)
        subgoal for p'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force+
          done
        subgoal for p'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force+
          done
        done
      subgoal
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x
            apply (drule step_id_op_Out)
             apply auto
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          subgoal for p op1'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          subgoal
            using no_step_id_op_Tau
            apply blast
            done
          done
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x
            apply (drule step_id_op_Out)
             apply auto
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          subgoal for p op2'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          subgoal for op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply blast
            apply blast
            done
          done
        done
      subgoal
        using no_step_transp_op_Tau
        apply blast
        done
      done
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (erule step_transp_op_Inp)
         apply auto
        apply (cases p)
        subgoal for p'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply fastforce+
          done
        subgoal for p'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply fastforce+
          done
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force+
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
          apply blast
          apply (force del: step_wstep intro!: step_wstep)
          done
        done
      subgoal for p x
        apply (drule step_transp_op_Out)
           apply (auto split: sum.splits)
        subgoal for p'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply fast+
          done
        subgoal for p'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply fast+
          done
        done
      subgoal for p
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          done
        done
      subgoal
        using no_step_transp_op_Tau
        apply blast
        done
      subgoal
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          subgoal for p
            apply (drule step_id_op_Inp)
             apply simp
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          subgoal for op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          done
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          subgoal for p
            apply (drule step_id_op_Inp)
             apply simp
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          subgoal for op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          done
        done
      done
    done
  done

lemma transp_op_commutes_scomp_op_pcomp_op:
  \<open>(\<stileturn>op1 \<parallel> \<stileturn>op2) \<bullet> \<X> \<approx> \<X> \<bullet> (op2\<turnstile> \<parallel> op1\<turnstile>)\<close>
  using B10_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> _ \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> _  \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  unfolding scomp_op_def
  by auto

end