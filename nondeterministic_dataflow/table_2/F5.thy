theory F5

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom F5\<close>

lemma F5_gen:
  \<open>map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))
    (case_sum undefined (\<lambda>_. []))
      (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (case_sum buf4 (\<lambda> _. [])))
        (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
          (id_op buf1 \<parallel> \<C>)
          (map_op reassoc reassoc (transp_op (case_sum buf3 (\<lambda>_. [])) \<parallel> \<I>))))
        (\<I> \<parallel> aeq_op (case_sum buf5 (\<lambda>_. []))))))
  \<approx> map_op projl projr (comp_op Some (\<lambda>_. [])
      sink_op
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))\<close>
  unfolding pcomp_op_def
  by (coinduction arbitrary: buf1 buf2 buf3 buf4 buf5 rule: wbisim_coinduct_upto''; auto 0 0 elim !: step_map_op_elim step_loop_op_elim step_comp_op_elim step_id_op_cases step_acopy_op_elim step_transp_op_cases step_aeq_op_elim step_sink_op split: sum.splits)
    (fastforce del: wbc_base intro!: wbc_base)+

lemma F5:
  \<open>((\<I> \<parallel> \<C>) \<bullet> map_op reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Q>)) \<up> \<approx> ! \<bullet> \<exclamdown>\<close>
  unfolding feedback_op_def scomp_op_def
  using F5_gen[of \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close>]
  by simp

lemma F5'_gen:
  \<open>map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))
    (case_sum undefined (\<lambda>_. []))
      (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (case_sum buf4 (\<lambda> _. [])))
        (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
          (id_op buf1 \<parallel> \<C>)
          (map_op reassoc reassoc (transp_op (case_sum buf3 (\<lambda>_. [])) \<parallel> \<I>))))
        (\<I> \<parallel> map_op projl projr (comp_op Some (\<lambda>_. []) (aeq_op (case_sum buf5 (\<lambda>_. []))) \<I>)))))
  \<approx> map_op projl projr (comp_op Some (\<lambda>_. [])
      sink_op
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))\<close>
  unfolding pcomp_op_def
  by (coinduction arbitrary: buf1 buf2 buf3 buf4 buf5 rule: wbisim_coinduct_upto''; auto 0 0 elim !: step_map_op_elim step_loop_op_elim step_comp_op_elim step_id_op_cases step_acopy_op_elim step_transp_op_cases step_aeq_op_elim step_sink_op split: sum.splits)
    (fastforce del: wbc_base intro!: wbc_base)+

lemma F5':
  \<open>((\<I> \<parallel> \<C>) \<bullet> map_op reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Q> \<turnstile>)) \<up> \<approx> ! \<bullet> \<exclamdown>\<close>
  unfolding feedback_op_def scomp_op_def
  using F5'_gen[of \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close>]
  by simp

end