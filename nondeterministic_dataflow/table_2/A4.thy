theory A4

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A4: Equality test to sink\<close>

lemma A4_gen:
  \<open>map_op id Inl (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) !)) \<approx> ! \<parallel> !\<close>
  unfolding pcomp_op_def
proof (coinduction arbitrary: buf1 buf1' buf2 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    by (auto elim !: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_sink_op)
      (fastforce del: wbc_base intro: wbc_base)+
next
  case SIM2
  then show ?case
    by (auto elim !: step_comp_op_elim step_sink_op) (fastforce del: wbc_base intro: wbc_base)+
qed

lemma A4:
  \<open>map_op id Inl (\<Q> \<bullet> !) \<approx> ! \<parallel> !\<close>
  unfolding scomp_op_def
  using A4_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>  \<open>\<lambda>_. []\<close>]
  by simp

end