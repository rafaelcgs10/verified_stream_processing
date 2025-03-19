theory A3

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)
no_notation nth (infixl "!" 100)

section \<open>Axiom A3: Equality test dummy source and identity\<close>

lemma A3_gen:
  \<open>map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
    ((map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>) :: (0, 'a :: {countable, defaults}, 'd option) op)
      \<parallel> id_op buf1)
    (aeq_op (case_sum (\<lambda>_. []) buf3)))
  \<approx> map_op projl projr (comp_op Some (\<lambda>_. [])
      (! :: (0 + 'a :: {countable, defaults}, 0, 'd option) op)
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))\<close>
  unfolding pcomp_op_def
proof (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_aeq_op_elim)
      (fastforce del: wbc_base intro!: wbc_base)+
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2 = map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' (map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>))))"
      if "pa \<notin> defaults"
      for pa :: "0 + 'a"
        and xa :: "'d option"
    proof (cases pa)
      case (Inl a)
      from this that show ?thesis by auto
    next
      case (Inr b)
      from this that show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    then show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_sink_op step_id_op_cases)
  qed
qed

lemma A3:
  \<open>((\<exclamdown> :: (0, 'a :: {countable, defaults}, 'd option) op) \<parallel> \<I>) \<bullet> \<Q>
  \<approx> (! :: (0 + 'a :: {countable, defaults}, 0, 'd option) op) \<bullet> \<exclamdown>\<close>
 unfolding scomp_op_def
  using A3_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end