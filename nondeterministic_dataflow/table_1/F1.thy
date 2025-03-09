theory F1

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)
section \<open>Axiom F1\<close>
lemma F1:
  \<open>\<I>\<up> ~ (\<I> :: (0, 0, 'd) op)\<close>
  unfolding feedback_op_def 
proof (coinduction rule: bisim_coinduct_upto)
  case BISIM
  then show ?case 
    unfolding sim_def
  proof (intro conjI impI allI)
    fix io :: "(0, 0, 'd) IO"
      and op1' :: "(0, 0, 'd) op"
    assume "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'a) \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) \<I>)) op1'"
    then have False
      apply (elim step_map_op_inv[elim_format] exE conjE; hypsubst)
      apply (auto elim!: step_loop_op_elim step_id_op_cases)
      apply (metis default_0 sum.collapse(2) sum_in_defaults)
      done
    then show "\<exists>op2'. step io \<I> op2' \<and> bisim_cong (\<lambda>sxx txx. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'a) \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) \<I>) \<and> txx = \<I>) op1' op2'"
      by blast
  next
    fix io :: "(0, 0, 'd) IO"
      and op1' :: "(0, 0, 'd) op"
    assume H: "step io \<I> op1'"
    then have False
      by (auto elim!: step_id_op_cases)
    then show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'a) \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) \<I>)) op2' \<and> bisim_cong (\<lambda>sxx txx. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'a) \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) \<I>) \<and> txx = \<I>) op1' op2'"
      by blast
  qed
qed

end