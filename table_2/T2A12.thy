theory T2A12

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A12: Dummy source with 0 ports is end_op\<close>

lemma A12:
  \<open>(\<exclamdown> :: ('a :: {all_defaults}, 'b :: {countable, all_defaults}, 'd) op) ~ \<oslash>\<close>
  by (rule choices_Choice_bisim) simp

end