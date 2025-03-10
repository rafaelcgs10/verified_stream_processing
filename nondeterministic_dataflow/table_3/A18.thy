theory A18

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A18: Split with 0 ports\<close>

lemma A18:
  \<open>(\<Lambda> :: (0, 0 + 0, 'd) op) ~ \<oslash>\<close>
  by (rule choices_Choice_bisim) auto

lemma A18':
  \<open>(\<Lambda>' :: (0, 0 + 0, 'd) op) ~ map_op id Inr \<I>\<close>
  unfolding scomp_op_def
proof (coinduction rule: bisim_coinduct_upto'')
  case SIM1
  then show ?case
    by (auto elim!:  step_comp_op_elim step_id_op_cases step_map_op_elim step_split_op_cases)
next
  case SIM2
  then show ?case
    by (auto elim!: step_map_op_elim step_id_op_cases)
qed

end