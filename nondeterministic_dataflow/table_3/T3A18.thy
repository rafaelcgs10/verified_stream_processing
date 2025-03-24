theory T3A18

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A18: Split with 0 ports\<close>

lemma A18:
  \<open>map_op Inl id (\<Lambda> :: (0, 0 + 0, 'd) op) ~ \<I>\<close>
  by (coinduction rule: bisim_coinduct)
    (auto elim!: step_map_op_elim step_split_op_cases step_id_op_cases)

end