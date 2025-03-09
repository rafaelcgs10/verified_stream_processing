theory F4

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom F4: Loop acopy\<close>

lemma F4:
  \<open>map_op Inr id \<C>\<up> ~ \<exclamdown>\<close>
proof (coinduction rule: bisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding sim_def feedback_op_def scomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<C>))) op1'"
    show "\<exists>op2'. step io (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op2' \<and> bisim_cong (\<lambda>s t. s = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<C>)) \<and> t = map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1' op2'"
      using H by (auto elim!: step_map_op_elim step_loop_op_elim step_acopy_op_elim)
  next
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<C>))) op2' \<and> bisim_cong (\<lambda>s t. s = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<C>)) \<and> t = map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1' op2'"
      using H by (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases)
  qed
qed

end