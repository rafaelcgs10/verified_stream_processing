theory T3A13

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A13: Parallel dummy source\<close>

lemma A13:
  \<open>\<exclamdown> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  by (rule choices_Choice_bisim) (simp add: choices_pcomp_op_dummy_source)

end