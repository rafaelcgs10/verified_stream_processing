theory Lifted_Table_3

imports
  "table_3/A1"
  "table_3/A2"
  "table_3/A3"
  "table_3/A4"
  "table_3/A5"
  "table_3/A6"
  "table_3/A8"
  "table_3/A9"
  "table_3/A12"
  "table_3/A13"
  "table_3/A14"
  "table_3/A15"
  "table_3/A16"
  "table_3/A17"
  "table_3/A18"
  "table_3/A19"
  "table_3/F3"
  "table_3/F4"
  "Lifted"
begin

no_notation Sublist.parallel (infixl "\<parallel>" 50)
no_notation nth (infixl "!" 100)

lemma split'_id_absorb_right:
  \<open>\<Lambda>' \<approx> \<Lambda>'\<turnstile>\<close>
  using split_id_absorb_right bisim_wbisim scomp_op_assoc wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

lemma split'_id_absorb:
  \<open>\<Lambda>' \<approx> (\<stileturn>\<Lambda>')\<turnstile>\<close>
  using split'_id_absorb_right scomp_op_id_op_left_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

lemma A5_split':
  \<open>\<Lambda>' \<bullet> (\<Lambda>' \<parallel> \<I>) \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> (\<I> \<parallel> \<Lambda>'))\<close>
proof -
  have \<open>\<Lambda>' \<bullet> (\<Lambda>' \<parallel> \<I>) \<approx> \<Lambda>' \<bullet> (\<Lambda>' \<parallel> (\<I> \<bullet> \<I>))\<close>
    by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have \<open>\<dots> \<approx> \<Lambda>' \<bullet> ((\<I> \<parallel> \<I>) \<bullet> (\<Lambda> \<parallel> \<I>))\<close>
    using bisim_wbisim pcomp_op_scomp_distributes wbisim_refl wbisim_scomp_op_cong wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<Lambda>' \<bullet> (\<I> \<bullet> (\<Lambda> \<parallel> \<I>))\<close>
    by (simp add: bisim_wbisim pcomp_op_id_id wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> \<Lambda>' \<bullet> \<I> \<bullet> (\<Lambda> \<parallel> \<I>)\<close>
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<Lambda>' \<bullet> (\<Lambda> \<parallel> \<I>)\<close>
    using split'_id_absorb_right wbisim_refl wbisim_scomp_op_cong wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<I> \<bullet> (\<Lambda> \<bullet> (\<Lambda> \<parallel> \<I>))\<close>
    by (simp add: bisim_wbisim scomp_op_assoc)
  also have \<open>\<dots> \<approx> \<I> \<bullet> (map_op id (case_sum Inr Inl) (\<Lambda> \<bullet> (\<I> \<parallel> \<Lambda>)))\<close>
    by (simp add: Asynchronous_Dataflow_Axioms.A5 bisim_wbisim wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<I> \<bullet> (\<Lambda> \<bullet> (\<I> \<parallel> \<Lambda>)))\<close>
    using map_op_id_f_left_absorb by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> (\<I> \<parallel> \<Lambda>))\<close>
    using bisim_wbisim scomp_op_assoc wbisim_map_op wbisim_sym by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> \<I> \<bullet> (\<I> \<parallel> \<Lambda>))\<close>
    using split'_id_absorb_right wbisim_map_op wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> (\<I> \<bullet> (\<I> \<parallel> \<Lambda>)))\<close>
  using bisim_wbisim scomp_op_assoc wbisim_map_op by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> ((\<I> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Lambda>)))\<close>
    by (metis pcomp_op_id_id bisim_wbisim wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> ((\<I> \<bullet> \<I>) \<parallel> \<Lambda>'))\<close>
    by (meson bisim_refl bisim_scomp_op_cong bisim_wbisim pcomp_op_scomp_distributes wbisim_map_op)
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> (\<I> \<parallel> \<Lambda>'))\<close>
    by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  finally show ?thesis.
qed

lemma A6_split':
  \<open>\<Lambda>' \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<Lambda>'\<close>
proof -
  have \<open>\<Lambda>' \<bullet> \<X> \<approx> \<I> \<bullet> (\<Lambda> \<bullet> \<X>)\<close>
    using bisim_wbisim scomp_op_assoc by blast
  also have \<open>\<dots> \<approx> \<I> \<bullet> (map_op id (case_sum Inr Inl) \<Lambda>)\<close>
    using Asynchronous_Dataflow_Axioms.A6 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) \<Lambda>'\<close>
    by (simp add: map_op_id_f_left_absorb)
  finally show ?thesis.
qed

lemma A8_split':
  \<open>\<exclamdown> \<bullet> \<Lambda>' \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close>
proof -
  have \<open>\<exclamdown> \<bullet> \<Lambda>' \<approx> \<exclamdown> \<bullet> \<Lambda>\<close>
    by (smt (verit, ccfv_SIG) bisim_wbisim scomp_op_assoc scomp_op_id_op_right_neutral split_id_absorb_right wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  also have \<open>\<dots> \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close> using Asynchronous_Dataflow_Axioms.A8 bisim_wbisim by blast
  finally show ?thesis.
qed

lemma A18_split':
  \<open>(\<Lambda>' :: (0, 0 + 0, 'd) op) ~ \<oslash>\<close>
  by (smt (z3) Asynchronous_Dataflow_Axioms.A12 Asynchronous_Dataflow_Axioms.A9 Asynchronous_Dataflow_Axioms.A18 bisim_refl bisim_scomp_op_cong bisim_sym bisim_trans id_op_0_end_op scomp_op_assoc)

lemma A19_split':
  \<open>\<Lambda>' \<approx> (\<Lambda>' \<parallel> \<Lambda>') \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
proof -
  have H1: \<open>\<Lambda>' \<parallel> \<Lambda>' \<approx> (\<I> \<parallel> \<I>) \<bullet> (\<Lambda> \<parallel> \<Lambda>)\<close>
    using bisim_wbisim pcomp_op_scomp_distributes wbisim_sym by blast
  have H2: \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
    using wbisim_refl by blast
  have \<open>(\<Lambda>' \<parallel> \<Lambda>') \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)
    \<approx> (\<I> \<parallel> \<I>) \<bullet> (\<Lambda> \<parallel> \<Lambda>) \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
    using H1 H2 wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> \<I> \<bullet> (\<Lambda> \<parallel> \<Lambda>) \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
    by (simp add: bisim_wbisim pcomp_op_id_id wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> \<I> \<bullet> ((\<Lambda> \<parallel> \<Lambda>) \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>))\<close>
    using bisim_wbisim scomp_op_assoc by blast
  also have \<open>\<dots> \<approx> \<Lambda>'\<close>
    by (smt (verit) Asynchronous_Dataflow_Axioms.A19 scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  finally show ?thesis by (rule wbisim_sym)
qed

lemma F4_split':
  \<open>map_op Inr id (\<Lambda>'::('b :: {countable, defaults}, 'b + 'b, 'c) op) \<up> \<approx> (\<exclamdown>::(0, 'b, 'c) op)\<close>
proof -
  have \<open>map_op Inr id \<Lambda>' \<up> \<approx> (((\<exclamdown>::(0, 'b, 'c) op) \<parallel> \<I>) \<bullet> map_op Inr id \<Lambda>) \<up>\<close>
    using map_op_Inr_id_left_identity wbisim_loop_op_cong by blast
  also have \<open>\<dots> \<approx> (\<exclamdown>::(0, 'b, 'c) op) \<bullet> (map_op Inr id \<Lambda> \<up>)\<close>
    apply (rule wbisim_trans)
    apply (rule wbisim_sym)
     apply (rule loop_op_scomp_commute)
      apply (smt (verit, ccfv_SIG) Inr_in_defaults \<UU>_E \<UU>_def disjoint_iff id_apply image_id inputs_split_op op.set_map(1) subsetD vimageE image_iff le_iff_inf)
     apply (smt (verit) Inr_in_defaults \<UU>_E \<UU>_def id_apply Inr_inject disjoint_iff imageE op.set_map(2) outputs_split_op subsetD vimageE)
    by (rule wbisim_refl)
  also have \<open>\<dots> \<approx> (\<exclamdown>::(0, 'b, 'c) op) \<bullet> (\<exclamdown>::('b, 'a :: {countable, defaults}, 'c) op)\<close>
    using Asynchronous_Dataflow_Axioms.F4 bisim_refl bisim_scomp_op_cong bisim_wbisim by blast
  also have \<open>\<dots> \<approx> (\<exclamdown>::(0, 'b, 'c) op)\<close>
    using scomp_op_dummy_source by blast
  finally show ?thesis.
qed

section \<open>Axioms for merge_op surrounded by identities\<close>

lemma merge'_id_absorb_left:
  \<open>\<V>' \<approx> \<stileturn>\<V>'\<close>
  using merge_id_absorb_left bisim_wbisim scomp_op_assoc wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma merge'_id_absorb:
  \<open>\<V>' \<approx> (\<stileturn>\<V>')\<turnstile>\<close>
  using merge'_id_absorb_left scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

lemma A1_merge':
  \<open>(\<V>' \<parallel> \<I>) \<bullet> \<V>' \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>') \<bullet> \<V>')\<close>
proof -
  have \<open>(\<V>' \<parallel> \<I>) \<bullet> \<V>' \<approx> (\<V>' \<parallel> \<I> \<bullet> \<I>) \<bullet> \<V>'\<close>
    by (smt (verit, del_insts) merge'_id_absorb_left pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  also have \<open>\<dots> \<approx> (\<V> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<V>'\<close>
    by (meson bisim_sym bisim_wbisim pcomp_op_scomp_distributes wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> (\<V> \<parallel> \<I>) \<bullet> \<I> \<bullet> \<V>'\<close>
    by (simp add: bisim_wbisim pcomp_op_id_id wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> (\<V> \<parallel> \<I>) \<bullet> \<V>'\<close>
    using bisim_wbisim merge'_id_absorb_left scomp_op_assoc wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast
  also have \<open>\<dots> \<approx> ((\<V> \<parallel> \<I>) \<bullet> \<V>) \<bullet> \<I>\<close>
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> (map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> \<V>)) \<bullet> \<I>\<close>
    using Asynchronous_Dataflow_Axioms.A1 bisim_wbisim wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> \<V>')\<close>
    using bisim_map_op bisim_wbisim map_op_out_id_vdash scomp_op_assoc wbisim_sym wbisim_trans by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> (\<I> \<bullet> \<V>'))\<close>
    using merge'_id_absorb_left wbisim_map_op wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> \<I> \<bullet> \<V>')\<close>
    using bisim_map_op bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<V>')\<close>
    by (metis bisim_wbisim pcomp_op_id_id wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id (((\<I> \<bullet> \<I>) \<parallel> \<V>') \<bullet> \<V>')\<close>
    by (simp add: bisim_map_op bisim_scomp_op_cong bisim_wbisim choices_Choice_bisim pcomp_op_scomp_distributes)
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>') \<bullet> \<V>')\<close>
    by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  finally show ?thesis.
qed

lemma A2_merge':
  \<open>\<X> \<bullet> \<V>' \<approx> map_op (case_sum Inr Inl) id \<V>'\<close>
proof -
  have \<open>\<X> \<bullet> \<V>' \<approx> \<X> \<bullet> \<V> \<bullet> \<I>\<close>
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> (map_op (case_sum Inr Inl) id \<V>) \<bullet> \<I>\<close>
    using Asynchronous_Dataflow_Axioms.A2 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id \<V>'\<close>
    using map_op_out_id_vdash wbisim_sym by blast
  finally show ?thesis.
qed

lemma A3_merge':
  \<open>map_op projr id ((\<exclamdown>::(0, 'a :: {countable, defaults}, 'b) op) \<parallel> \<I>) \<bullet> \<V>' \<approx> \<I>\<close>
proof -
  have \<open>map_op projr id ((\<exclamdown>::(0, 'a, 'b) op) \<parallel> \<I>) \<bullet> \<V>'
    \<approx> map_op projr id ((\<exclamdown>::(0, 'a, 'b) op) \<parallel> \<I>) \<bullet> \<V> \<bullet> \<I>\<close>
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<I> \<bullet> \<I>\<close>
    using Asynchronous_Dataflow_Axioms.A3 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> \<I>\<close>
    using scomp_op_id_id by blast
  finally show ?thesis.
qed

lemma A4_merge':
  \<open>\<V>' \<bullet> ! \<approx> ! \<parallel> !\<close>
proof -
  have \<open>\<V>' \<bullet> ! \<approx> \<V> \<bullet> (\<I> \<bullet> !)\<close>
    using bisim_wbisim scomp_op_assoc by blast
  also have \<open>\<dots> \<approx> \<V> \<bullet> !\<close>
    by (metis id_sink_op_sink_op scomp_op_def wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> ! \<parallel> !\<close>
    using Asynchronous_Dataflow_Axioms.A4 by auto
  finally show ?thesis.
qed

lemma A14_merge':
  \<open>(\<V>' :: (0 + 0, 0, 'd) op) ~ \<oslash>\<close>
  by (smt (z3) A12 A16 A9 Asynchronous_Dataflow_Axioms.A14 bisim_scomp_op_cong bisim_sym bisim_trans id_op_0_end_op scomp_op_assoc)

lemma A15_merge':
  \<open>\<V>' \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<V>' \<parallel> \<V>')\<close>
proof -
  have H1: \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close> by (rule wbisim_refl)
  have H2: \<open>\<V>' \<parallel> \<V>' \<approx> (\<V> \<parallel> \<V>) \<bullet> (\<I> \<parallel> \<I>)\<close>
    using bisim_wbisim pcomp_op_scomp_distributes wbisim_sym by blast
  have \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<V>' \<parallel> \<V>')
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> ((\<V> \<parallel> \<V>) \<bullet> (\<I> \<parallel> \<I>))\<close>
    using wbisim_scomp_op_cong H1 H2 by blast
  also have \<open>\<dots> \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> ((\<V> \<parallel> \<V>) \<bullet> \<I>)\<close>
    by (simp add: bisim_scomp_op_cong bisim_wbisim choices_Choice_bisim pcomp_op_id_id)
  also have \<open>\<dots> \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<V> \<parallel> \<V>) \<bullet> \<I>\<close>
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<V>'\<close> using Asynchronous_Dataflow_Axioms.A15
    by (smt (verit) scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  finally show ?thesis by (rule wbisim_sym)
qed

lemma F3_merge':
  \<open>map_op id Inr (\<V>' :: ('a :: {countable, defaults} + 'a, 'a, 'c) op)\<up> \<approx> (!::('a, 'a, 'c) op)\<close>
proof -
  have \<open>map_op id Inr \<V>' \<up> \<approx> (map_op id Inr \<V> \<bullet> ((!::('a, 'a, 'c) op) \<parallel> \<I>)) \<up>\<close> 
    using map_op_id_Inr_move_vdash wbisim_loop_op_cong by blast
  also have \<open>\<dots> \<approx> map_op id Inr \<V>\<up> \<bullet> (!::('a, 'a, 'c) op)\<close>
    apply (rule wbisim_trans)
     apply (rule wbisim_sym)
     apply (rule loop_op_distribute_scomp_op)
     apply (metis (no_types, lifting) Inr_in_defaults \<UU>_E \<UU>_def disjoint_iff id_apply image_id inputs_merge_op op.set_map(1) subsetD vimageE)
    apply (smt (verit, del_insts) Diff_disjoint Inr_inject disjoint_iff imageE op.set_map(2) outputs_merge_op subsetD vimageE)
    by (rule wbisim_refl)
  also have \<open>\<dots> \<approx> (!::('a, 'a, 'c) op)\<close>
    using sink_sink Asynchronous_Dataflow_Axioms.F3 wbisim_refl wbisim_scomp_op_cong wbisim_trans by fast
  finally show ?thesis.
qed

section \<open>Axioms for aeq_op surrounded by identities\<close>

lemma aeq_vdash_absorb:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'))"
  using aeq_id_absorb using bisim_wbisim scomp_op_assoc wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma aeq_double_vdash_absorb:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'\<turnstile>))"
  using aeq_vdash_absorb using scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

lemma A1':
  \<open>(\<Q>' \<parallel> \<I>) \<bullet> \<Q>' \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>') \<bullet> \<Q>')\<close>
proof -
  have "(\<Q>' \<parallel> \<I>) \<bullet> \<Q>' \<approx> (\<Q>' \<parallel> \<I>\<turnstile>) \<bullet> \<Q>'" 
    by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<Q>'"
    by (simp add: bisim_scomp_op_cong bisim_wbisim choices_Choice_bisim pcomp_op_scomp_distributes wbisim_sym)  
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> \<I> \<bullet> \<Q>'"
    by (simp add: bisim_wbisim pcomp_op_id_id wbisim_refl wbisim_scomp_op_cong)
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> \<Q>'" using scomp_op_id_left_absorb by (smt (verit, ccfv_SIG) aeq_double_vdash_absorb bisim_wbisim scomp_op_assoc scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> \<Q> \<bullet> \<I>"
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast 
  also have "\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>) \<bullet> \<I>" using wbisim_refl wbisim_scomp_op_cong using Synchronous_Operators_Axioms.A1 bisim_wbisim by blast
  also have "\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>')" using map_op_out_id_vdash bisim_wbisim scomp_op_assoc wbisim_map_op wbisim_sym wbisim_trans by blast
  also have "\<dots>  \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>)\<turnstile> \<bullet> \<Q>')" using scomp_op_id_left_absorb wbisim_map_op wbisim_sym by (smt (verit, best) aeq_double_vdash_absorb bisim_wbisim scomp_op_assoc scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_trans)
  also have "\<dots>  \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<Q>')" by (metis bisim_wbisim pcomp_op_id_id wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have "\<dots>  \<approx> map_op (case_sum Inr Inl) id ((\<I>\<turnstile> \<parallel> \<Q>') \<bullet> \<Q>')" by (simp add: bisim_wbisim pcomp_op_scomp_distributes wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  also have "\<dots>  \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>') \<bullet> \<Q>')" by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  finally show ?thesis.
qed

lemma A2':
  \<open>\<X> \<bullet> \<Q>' \<approx> map_op (case_sum Inr Inl) id \<Q>'\<close>
proof -
  have \<open>\<X> \<bullet> \<Q>' \<approx> \<X> \<bullet> \<Q> \<bullet> \<I>\<close> using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> (map_op (case_sum Inr Inl) id \<Q>) \<bullet> \<I>\<close>
    using Synchronous_Operators_Axioms.A2 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id \<Q>'\<close> using map_op_out_id_vdash wbisim_sym by blast
  finally show ?thesis.
qed

lemma A3':
  \<open>map_op projr id ((\<exclamdown>::(0, 'a :: {countable, defaults}, 'b) op) \<parallel> \<I>) \<bullet> \<Q>'
  \<approx> (!::('a, 0, 'b) op) \<bullet> (\<exclamdown>::(0, 'a, 'b) op)\<close>
proof -
  have \<open>map_op projr id ((\<exclamdown>::(0, 'a, 'b) op) \<parallel> \<I>) \<bullet> \<Q>'
    \<approx> map_op projr id ((\<exclamdown>::(0, 'a, 'b) op) \<parallel> \<I>) \<bullet> \<Q> \<bullet> \<I>\<close>
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> ((!::('a, 0, 'b) op) \<bullet> (\<exclamdown>::(0, 'a, 'b) op)) \<bullet> \<I>\<close>
    using Synchronous_Operators_Axioms.A3 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> (!::('a, 0, 'b) op) \<bullet> (\<exclamdown>::(0, 'a, 'b) op)\<close>
    using bisim_wbisim scomp_op_assoc scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast
  finally show ?thesis.
qed

lemma A4':
  \<open>\<Q>' \<bullet> ! \<approx> ! \<parallel> !\<close>
proof -
  have \<open>\<Q>' \<bullet> ! \<approx> \<Q> \<bullet> \<stileturn>!\<close> using bisim_wbisim scomp_op_assoc by blast
  also have \<open>\<dots> \<approx> \<Q> \<bullet> !\<close> using scomp_op_id_left_absorb calculation wbisim_sym wbisim_trans by (metis id_sink_op_sink_op scomp_op_def wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> ! \<parallel> !\<close> by (rule Synchronous_Operators_Axioms.A4)
  finally show ?thesis.
qed

lemma A10':
  "\<Q>' \<bullet> \<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q>' \<parallel> \<Q>')"
  apply (rule wbisim_trans[OF scomp_op_id_left_absorb A10])
  using inputs_acopy_op apply fastforce
  done

lemma A11':
  \<open>\<C> \<bullet> \<Q>' \<approx> \<I>\<close>
proof -
  have \<open>\<C> \<bullet> \<Q>' \<approx> (\<C> \<bullet> \<Q>)\<turnstile>\<close> using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<I>\<turnstile>\<close>
    using Synchronous_Operators_Axioms.A11 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> \<I>\<close> using scomp_op_id_id by blast
  finally show ?thesis.
qed

lemma A14':
  \<open>(\<Q>' :: (0 + 0, 0, 'd) op) ~ \<oslash>\<close>
  by (smt (verit) Synchronous_Operators_Axioms.A14 bisim_scomp_op_cong bisim_trans choices_Choice_bisim choices_dummy_source choices_spin_op spin_op_end_op)

lemma A15':
  \<open>\<Q>' \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<Q>' \<parallel> \<Q>')\<close>
proof -
  have H1: \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close> by (rule wbisim_refl)
  have H2: \<open>\<Q>' \<parallel> \<Q>' \<approx> (\<Q> \<parallel> \<Q>) \<bullet> (\<I> \<parallel> \<I>)\<close>
    using bisim_wbisim pcomp_op_scomp_distributes wbisim_sym by blast
  have \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<Q>' \<parallel> \<Q>')
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> ((\<Q> \<parallel> \<Q>) \<bullet> (\<I> \<parallel> \<I>))\<close>
    using wbisim_scomp_op_cong H1 H2 by blast
  also have \<open>\<dots> \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> ((\<Q> \<parallel> \<Q>) \<bullet> \<I>)\<close>
    by (simp add: bisim_scomp_op_cong bisim_wbisim choices_Choice_bisim pcomp_op_id_id)
  also have \<open>\<dots> \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<Q> \<parallel> \<Q>) \<bullet> \<I>\<close>
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<Q>'\<close> using Synchronous_Operators_Axioms.A15
    by (smt (verit) scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  finally show ?thesis by (rule wbisim_sym)
qed

lemma F3':
  assumes \<open>(S :: ('a :: {countable,defaults}, 'a, 'c) op) = !\<close>
    and "(Q' :: ('a :: {countable,defaults} + 'a, 'a, 'c) op) = \<Q>'"
    and "(Q :: ('a :: {countable,defaults} + 'a, 'a, 'c) op) = \<Q>"
    and "(I :: ('a :: {countable,defaults}, 'a, 'c) op) = \<I>"
  shows  \<open>map_op id Inr Q' \<up> \<approx> S\<close>
proof -
  have "map_op id Inr Q' \<up> \<approx> (map_op id Inr Q \<bullet> (S \<parallel> I)) \<up>"  using assms map_op_id_Inr_move_vdash wbisim_loop_op_cong by blast
  also have \<open>\<dots> \<approx> map_op id Inr Q\<up> \<bullet> S\<close>
    using assms apply -
    apply (rule wbisim_trans)
     apply (rule wbisim_sym)
     apply hypsubst_thin
     apply (rule loop_op_distribute_scomp_op)
      prefer 3
      apply hypsubst_thin
    using wbisim_refl apply blast
     apply (metis (no_types, lifting) Inr_in_defaults \<UU>_E \<UU>_def disjoint_iff id_apply image_id inputs_aeq_op op.set_map(1) subsetD vimageE)
    apply (smt (verit, del_insts) Diff_disjoint Inr_inject disjoint_iff imageE op.set_map(2) outputs_aeq_op subsetD vimageE)
    done
  also have \<open>\<dots> \<approx> S\<close> using assms sink_sink Synchronous_Operators_Axioms.F3 wbisim_refl wbisim_scomp_op_cong wbisim_trans by fast
  finally show ?thesis.
qed

lemma F5'_gen:
  \<open>map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. []))
    (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. [])))
      (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
        (comp_op (\<lambda>_. None) (\<lambda>_. [])
          ((id_op buf1) :: ('a :: {countable,defaults}, 'a, 'b) op) \<C>)
        (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
          (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>))))
      (comp_op (\<lambda>_. None) (\<lambda>_. [])
        \<I>
        (map_op projl projr (comp_op Some (\<lambda>_. []) (aeq_op (case_sum buf5 (\<lambda>_. []))) \<I>))))))
  \<approx> map_op projl projr (comp_op Some (\<lambda>_. []) (!::('a, 0, 'b) op)
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)::(0, 'a, 'b) op))\<close>
proof (coinduction arbitrary: buf1 buf2 buf3 buf4 buf5 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    using SIM1 by (auto 0 0 elim!: step_map_op_elim step_loop_op_elim step_comp_op_elim step_id_op_cases step_acopy_op_elim step_transp_op_cases step_aeq_op_elim split: sum.splits if_splits)
    (force del: wbc_base intro!: wbc_base)+
next
  case SIM2
  then show ?case
    using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_sink_op step_id_op_cases split: if_splits sum.splits)
      (intro exI conjI[rotated, OF wbc_base], force, force del: step_wstep intro!: step_wstep)
qed

lemma F5':
  \<open>((\<I> \<parallel> \<C>) \<bullet> map_op reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Q>')) \<up>
  \<approx> (!::('a :: {countable, defaults}, 0, 'b) op) \<bullet> (\<exclamdown>::(0, 'a, 'b) op)\<close>
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using F5'_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end