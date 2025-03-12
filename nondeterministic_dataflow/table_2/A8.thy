theory A8

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A8: Acopy dummy source\<close>

lemma A8:
  \<open>(\<exclamdown> \<bullet> \<C>) ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply (coinduction rule: bisim_coinduct)
  subgoal
    unfolding scomp_op_def pcomp_op_def
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_id_op_cases)
    done
  subgoal
    apply (metis cempty_iff choices_pcomp_op_dummy_source step_choicesE)
    done
  done

end