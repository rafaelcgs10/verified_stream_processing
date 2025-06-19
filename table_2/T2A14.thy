theory T2A14

imports
  "../BNA_Operators"
begin

section \<open>Axiom A14: Equality test with 0 ports\<close>

lemma A14:
  \<open>map_op id Inl (\<Q> :: (0 + 0, 0, 'd option) op) ~ \<I>\<close>
  by (coinduction rule: bisim_coinduct)
    (auto elim!: step_map_op_elim step_aeq_op_elim step_id_op_cases)

end