theory A14

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A14: Merge with 0 ports\<close>

lemma A14:
  \<open>(\<V> :: (0 + 0, 0, 'd) op) ~ \<oslash>\<close>
  by (rule choices_Choice_bisim) auto

end