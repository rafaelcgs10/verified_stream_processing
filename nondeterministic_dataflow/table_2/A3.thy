theory A3

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A3: Equality test dummy source and identity\<close>

lemma A3_gen:
  \<open>map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
    (map_op projr id (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>) \<parallel> id_op buf1))
    (aeq_op (case_sum (\<lambda>_. []) buf3)))
  \<approx> map_op projl projr (comp_op Some (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))\<close>
proof (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_aeq_op_elim) blast+
  next
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_sink_op step_id_op_cases) (fastforce intro: wbc_sym[OF wbc_base])
  qed
qed

lemma A3:
  \<open>map_op projr id (\<exclamdown> \<parallel> \<I>) \<bullet> \<Q> \<approx> ! \<bullet> \<exclamdown>\<close>
  unfolding scomp_op_def
  using A3_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end