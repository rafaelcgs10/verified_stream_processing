theory A18

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A18: Acopy with 0 ports\<close>

(*
lemma A18:
  \<open>(\<C> :: (0, 0 + 0, 'd) op) ~ \<oslash>\<close>
  by (rule choices_Choice_bisim) auto
*)

lemma A18:
  \<open>map_op Inl id (\<C> :: (0, 0 + 0, 'd) op) ~ \<I>\<close>
  by (coinduction rule: bisim_coinduct)
    (auto elim!: step_map_op_elim step_acopy_op_elim step_id_op_cases)

end