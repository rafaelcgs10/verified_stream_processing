theory A4

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A4: Equality test to sink\<close>

lemma A4_gen:
  \<open>map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) !) \<approx> ! \<parallel> !\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a + 'a, 'b + 'c, 'd) IO"
      and op1' :: "('a + 'a, 'b + 'c, 'd) op"
    assume H: "step io (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) !)) op1'"
    show "\<exists>op2'. wstep io (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_sink_op) (fastforce del: wbc_base intro: wbc_base)+
  next
    fix io :: "('a + 'a, 'b + 'c, 'd) IO"
      and op1' :: "('a + 'a, 'b + 'c, 'd) op"
    assume H: "step io (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1' op2'"
      using H by (auto elim !: step_comp_op_elim step_sink_op) (fastforce intro: wbc_sym[OF wbc_base])+
  qed
qed

lemma A4:
  \<open>\<Q> \<bullet> ! \<approx> ! \<parallel> !\<close>
  unfolding scomp_op_def
  using A4_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>  \<open>\<lambda>_. []\<close>]
  by simp

end