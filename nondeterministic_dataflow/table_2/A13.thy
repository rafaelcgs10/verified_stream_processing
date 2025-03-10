theory A13

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A13: Parallel dummy source\<close>

lemma A13:
  \<open>map_op Inl id \<exclamdown> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  unfolding scomp_op_def pcomp_op_def
  by (coinduction rule: bisim_coinduct_upto'')
    (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases)

end