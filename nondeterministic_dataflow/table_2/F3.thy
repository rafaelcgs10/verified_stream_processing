theory F3

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom F3: Loop equality test\<close>

lemma F3_gen:
  \<open>map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))
    (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1'))))
  \<approx> !\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1'))))) op1'"
    show "\<exists>op2'. wstep io sink_op op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1')))) \<and> op2 = sink_op) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_loop_op_elim step_aeq_op_elim) blast+
  next
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io sink_op op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1')))) \<and> op2 = sink_op) op1' op2'"
      using H by (elim step_sink_op) (force  del: wstep_loop_Inp intro!: wstep_loop_Inp)
  qed
qed

lemma F3:
  \<open>map_op id Inr \<Q>\<up> \<approx> !\<close>
  unfolding feedback_op_def
  using F3_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp


end