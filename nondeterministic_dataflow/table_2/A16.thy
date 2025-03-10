theory A16

imports
  "../BNA_Operators"
begin

section \<open>Axiom A16: Sink with 0 ports is end_op\<close>

lemma A16:
  \<open>(! :: (0, 0, 'd) op) ~ \<oslash>\<close>
  by (rule choices_Choice_bisim) auto

end