theory A9

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

lemma A9:
  \<open>\<exclamdown> \<bullet> ! ~ \<oslash>\<close>
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def scomp_op_def
  apply auto
  apply (drule step_map_op_inv)
  apply auto
  apply (drule step_comp_op_cases)
  apply auto
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    done
  subgoal
    using no_step_sink_op_Out
    apply fastforce
    done
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    apply (drule step_id_op_Out)
     apply auto
    done
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    done
  subgoal
    using no_step_id_op_Tau no_step_sink_op_Tau
     apply blast+
    done
  done


end