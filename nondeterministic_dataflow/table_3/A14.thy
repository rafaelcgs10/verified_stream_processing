theory A14

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A14: Merge with 0 ports\<close>

lemma A14:
  \<open>map_op id Inl (\<V> :: (0 + 0, 0, 'd) op) ~ \<I>\<close>
  by (coinduction rule: bisim_coinduct)
    (auto elim!: step_map_op_elim step_merge_op_elim step_id_op_cases)

end