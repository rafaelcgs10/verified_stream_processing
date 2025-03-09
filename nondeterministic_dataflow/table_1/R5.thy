theory R5

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom R5\<close>
lemma R5:
  fixes op :: "('a :: {countable, defaults} + 0, 'b :: {countable, defaults} + 0, 'c) op"
  assumes "Inr -` inputs op = {}"
    and "Inr -` outputs op = {}"
  shows "op\<up> \<approx> map_op projl projl op"
  unfolding feedback_op_def using assms
  apply simp
  apply (coinduction arbitrary: op  rule: wbisim_coinduct_upto)
  unfolding wsim_def
  apply safe
  subgoal for op io op1'
    apply (drule step_map_op_inv)
    apply safe
    apply hypsubst_thin
    subgoal for io' op'
      apply (drule step_loop_op[where io=io', simplified])
      apply (elim disjE conjE exE)
      subgoal
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply (rule exI conjI refl)+
          apply (metis step_inputs_outputs subset_empty vimage_mono)
         apply (metis step_inputs_outputs subset_empty vimage_mono)
        apply blast
        done
      subgoal
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply (rule exI conjI refl)+
          apply (metis step_inputs_outputs subset_empty vimage_mono)
         apply (metis step_inputs_outputs subset_empty vimage_mono)
        apply blast
        done
      subgoal
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply (rule exI conjI refl)+
          apply (metis step_inputs_outputs subset_empty vimage_mono)
         apply (metis step_inputs_outputs subset_empty vimage_mono)
        apply blast
        done
      subgoal
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply (rule exI conjI refl)+
          apply (metis step_inputs_outputs subset_empty vimage_mono)
         apply (metis step_inputs_outputs subset_empty vimage_mono)
        apply blast
        done
      subgoal
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply (rule exI conjI refl)+
          apply (metis step_inputs_outputs subset_empty vimage_mono)
         apply (metis step_inputs_outputs subset_empty vimage_mono)
        apply blast
        done
      done
    done
  subgoal for op io op1'
    apply (drule step_map_op_inv)
    apply safe
    apply hypsubst_thin
    subgoal for io' op'
      apply (cases io')
      subgoal for p x
        apply (cases p)
        subgoal for lp
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (rule exI conjI refl)+
            apply (metis step_inputs_outputs subset_empty vimage_mono)
           apply (metis step_inputs_outputs subset_empty vimage_mono)
          apply fastforce
          done
        apply (rule FalseE)
        apply hypsubst_thin
        apply (erule step_choicesE; blast dest: Read_choices_inputs)
        done
        subgoal for rp
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (rule exI conjI refl)+
            apply (metis step_inputs_outputs subset_empty vimage_mono)
           apply (metis step_inputs_outputs subset_empty vimage_mono)
          apply blast
          done
        subgoal
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (rule exI conjI refl)+
            apply (metis step_inputs_outputs subset_empty vimage_mono)
           apply (metis step_inputs_outputs subset_empty vimage_mono)
          apply force
          done
        done
      done
    done

end