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
no_notation wbisim_operator (infix "\<approx>"40)
no_notation id_empty_operator ("\<I>")
no_notation scomp_operator (infixl "\<bullet>" 65)
no_notation pcomp_operator (infixl "\<parallel>" 64)
no_notation feedback_operator ( "_ \<up>" [66] 65)
no_notation transp_empty_operator ("\<X>")
no_notation sink_op_0_operator ("!")
no_notation dummy_source_operator ("\<exclamdown>")
no_notation merge_empty_operator ("\<V>")


lemma A5_split':
  \<open>\<Lambda>' \<bullet> (\<Lambda>' \<parallel> \<I>) \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> (\<I> \<parallel> \<Lambda>'))\<close>
proof -
  have \<open>\<Lambda>' \<bullet> (\<Lambda>' \<parallel> \<I>) \<approx> \<Lambda>' \<bullet> (\<Lambda>' \<parallel> (\<I> \<bullet> \<I>))\<close>
    by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have \<open>\<dots> \<approx> \<Lambda>' \<bullet> ((\<I> \<parallel> \<I>) \<bullet> (\<Lambda> \<parallel> \<I>))\<close>
    using bisim_wbisim B5 wbisim_refl wbisim_scomp_op_cong wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<Lambda>' \<bullet> (\<I> \<bullet> (\<Lambda> \<parallel> \<I>))\<close>
    by (simp add: bisim_wbisim B6 wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> \<Lambda>' \<bullet> \<I> \<bullet> (\<Lambda> \<parallel> \<I>)\<close>
    using bisim_wbisim B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<Lambda>' \<bullet> (\<Lambda> \<parallel> \<I>)\<close>
    using split'_id_absorb_right wbisim_refl wbisim_scomp_op_cong wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<I> \<bullet> (\<Lambda> \<bullet> (\<Lambda> \<parallel> \<I>))\<close>
    by (simp add: bisim_wbisim B3)
  also have \<open>\<dots> \<approx> \<I> \<bullet> (map_op id (case_sum Inr Inl) (\<Lambda> \<bullet> (\<I> \<parallel> \<Lambda>)))\<close>
    by (simp add: A5 bisim_wbisim wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<I> \<bullet> (\<Lambda> \<bullet> (\<I> \<parallel> \<Lambda>)))\<close>
    using map_op_id_f_left_absorb by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> (\<I> \<parallel> \<Lambda>))\<close>
    using bisim_wbisim B3 wbisim_map_op wbisim_sym by metis
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> \<I> \<bullet> (\<I> \<parallel> \<Lambda>))\<close>
    using split'_id_absorb_right wbisim_map_op wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> (\<I> \<bullet> (\<I> \<parallel> \<Lambda>)))\<close>
  using bisim_wbisim B3 wbisim_map_op by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> ((\<I> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Lambda>)))\<close>
    by (metis B6 bisim_wbisim wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> ((\<I> \<bullet> \<I>) \<parallel> \<Lambda>'))\<close>
    by (meson bisim_refl bisim_scomp_op_cong bisim_wbisim B5 wbisim_map_op)
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) (\<Lambda>' \<bullet> (\<I> \<parallel> \<Lambda>'))\<close>
    by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  finally show ?thesis.
qed

lemma A6_split':
  \<open>\<Lambda>' \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<Lambda>'\<close>
proof -
  have \<open>\<Lambda>' \<bullet> \<X> \<approx> \<I> \<bullet> (\<Lambda> \<bullet> \<X>)\<close>
    using bisim_wbisim B3 by blast
  also have \<open>\<dots> \<approx> \<I> \<bullet> (map_op id (case_sum Inr Inl) \<Lambda>)\<close>
    using A6 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op id (case_sum Inr Inl) \<Lambda>'\<close>
    by (simp add: map_op_id_f_left_absorb)
  finally show ?thesis.
qed

lemma A8_split':
  \<open>\<exclamdown> \<bullet> \<Lambda>' \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close>
proof -
  have \<open>\<exclamdown> \<bullet> \<Lambda>' \<approx> \<exclamdown> \<bullet> \<Lambda>\<close>
    by (smt (verit, ccfv_SIG) bisim_wbisim B3 B4_1 split_id_absorb_right wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  also have \<open>\<dots> \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close> using A8 bisim_wbisim by blast
  finally show ?thesis.
qed

lemma A18_split':
  \<open>(\<Lambda>' :: (0, 0 + 0, 'd) op) ~ \<oslash>\<close>
  by (smt (z3) A12 A9 A18 bisim_refl bisim_scomp_op_cong bisim_sym bisim_trans id_op_0_end_op B3)

lemma A19_split':
  \<open>\<Lambda>' \<approx> (\<Lambda>' \<parallel> \<Lambda>') \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
proof -
  have H1: \<open>\<Lambda>' \<parallel> \<Lambda>' \<approx> (\<I> \<parallel> \<I>) \<bullet> (\<Lambda> \<parallel> \<Lambda>)\<close>
    using bisim_wbisim B5 wbisim_sym by blast
  have H2: \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
    using wbisim_refl by blast
  have \<open>(\<Lambda>' \<parallel> \<Lambda>') \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)
    \<approx> (\<I> \<parallel> \<I>) \<bullet> (\<Lambda> \<parallel> \<Lambda>) \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
    using H1 H2 wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> \<I> \<bullet> (\<Lambda> \<parallel> \<Lambda>) \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
    by (simp add: bisim_wbisim B6 wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> \<I> \<bullet> ((\<Lambda> \<parallel> \<Lambda>) \<bullet> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>))\<close>
    using bisim_wbisim B3 by blast
  also have \<open>\<dots> \<approx> \<Lambda>'\<close>
    by (smt (verit) A19 scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)
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
     apply (rule R1)
      apply (smt (verit, ccfv_SIG) Inr_in_defaults \<UU>_E \<UU>_def disjoint_iff id_apply image_id inputs_split_op op.set_map(1) subsetD vimageE image_iff le_iff_inf)
     apply (smt (verit) Inr_in_defaults \<UU>_E \<UU>_def id_apply Inr_inject disjoint_iff imageE op.set_map(2) outputs_split_op subsetD vimageE)
    by (rule wbisim_refl)
  also have \<open>\<dots> \<approx> (\<exclamdown>::(0, 'b, 'c) op) \<bullet> (\<exclamdown>::('b, 'a :: {countable, defaults}, 'c) op)\<close>
    using F4 bisim_refl bisim_scomp_op_cong bisim_wbisim by blast
  also have \<open>\<dots> \<approx> (\<exclamdown>::(0, 'b, 'c) op)\<close>
    using scomp_op_dummy_source by blast
  finally show ?thesis.
qed

lemma A1_merge':
  \<open>(\<V>' \<parallel> \<I>) \<bullet> \<V>' \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>') \<bullet> \<V>')\<close>
proof -
  have \<open>(\<V>' \<parallel> \<I>) \<bullet> \<V>' \<approx> (\<V>' \<parallel> \<I> \<bullet> \<I>) \<bullet> \<V>'\<close>
    by (smt (verit, del_insts) merge'_id_absorb_left pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  also have \<open>\<dots> \<approx> (\<V> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<V>'\<close>
    by (meson bisim_sym bisim_wbisim B5 wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> (\<V> \<parallel> \<I>) \<bullet> \<I> \<bullet> \<V>'\<close>
    by (simp add: bisim_wbisim B6 wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> (\<V> \<parallel> \<I>) \<bullet> \<V>'\<close>
    using bisim_wbisim merge'_id_absorb_left B3 wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by (smt (verit, ccfv_SIG))
  also have \<open>\<dots> \<approx> ((\<V> \<parallel> \<I>) \<bullet> \<V>) \<bullet> \<I>\<close>
    using bisim_wbisim B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> (map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> \<V>)) \<bullet> \<I>\<close>
    using A1 bisim_wbisim wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> \<V>')\<close>
    using bisim_map_op bisim_wbisim map_op_out_id_vdash B3 wbisim_sym wbisim_trans by (smt (verit, ccfv_SIG))
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> (\<I> \<bullet> \<V>'))\<close>
    using merge'_id_absorb_left wbisim_map_op wbisim_refl wbisim_scomp_op_cong by (smt (verit, ccfv_SIG))
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> \<I> \<bullet> \<V>')\<close>
    using bisim_map_op bisim_wbisim B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<V>')\<close>
    by (metis bisim_wbisim B6 wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id (((\<I> \<bullet> \<I>) \<parallel> \<V>') \<bullet> \<V>')\<close>
    by (simp add: bisim_map_op bisim_scomp_op_cong bisim_wbisim choices_Choice_bisim B5)
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>') \<bullet> \<V>')\<close>
    by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  finally show ?thesis.
qed

lemma A2_merge':
  \<open>\<X> \<bullet> \<V>' \<approx> map_op (case_sum Inr Inl) id \<V>'\<close>
proof -
  have \<open>\<X> \<bullet> \<V>' \<approx> \<X> \<bullet> \<V> \<bullet> \<I>\<close>
    using bisim_wbisim B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> (map_op (case_sum Inr Inl) id \<V>) \<bullet> \<I>\<close>
    using A2 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op (case_sum Inr Inl) id \<V>'\<close>
    using map_op_out_id_vdash wbisim_sym by blast
  finally show ?thesis.
qed

lemma A3_merge':
  \<open>map_op projr id ((\<exclamdown>::(0, 'a :: {countable, defaults}, 'b) op) \<parallel> \<I>) \<bullet> \<V>' \<approx> \<I>\<close>
proof -
  have \<open>map_op projr id ((\<exclamdown>::(0, 'a, 'b) op) \<parallel> \<I>) \<bullet> \<V>'
    \<approx> map_op projr id ((\<exclamdown>::(0, 'a, 'b) op) \<parallel> \<I>) \<bullet> \<V> \<bullet> \<I>\<close>
    using bisim_wbisim B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<I> \<bullet> \<I>\<close>
    using A3 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> \<I>\<close>
    using scomp_op_id_id by blast
  finally show ?thesis.
qed

lemma A4_merge':
  \<open>\<V>' \<bullet> ! \<approx> ! \<parallel> !\<close>
proof -
  have \<open>\<V>' \<bullet> ! \<approx> \<V> \<bullet> (\<I> \<bullet> !)\<close>
    using bisim_wbisim B3 by blast
  also have \<open>\<dots> \<approx> \<V> \<bullet> !\<close>
    by (metis id_sink_op_sink_op scomp_op_def wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> ! \<parallel> !\<close>
    using A4 by auto
  finally show ?thesis.
qed

lemma A14_merge':
  \<open>(\<V>' :: (0 + 0, 0, 'd) op) ~ \<oslash>\<close>
  by (smt (z3) A12 A16 A9 A14 bisim_scomp_op_cong bisim_sym bisim_trans id_op_0_end_op B3)

lemma A15_merge':
  \<open>\<V>' \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<V>' \<parallel> \<V>')\<close>
proof -
  have H1: \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close> by (rule wbisim_refl)
  have H2: \<open>\<V>' \<parallel> \<V>' \<approx> (\<V> \<parallel> \<V>) \<bullet> (\<I> \<parallel> \<I>)\<close>
    using bisim_wbisim B5 wbisim_sym by blast
  have \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<V>' \<parallel> \<V>')
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> ((\<V> \<parallel> \<V>) \<bullet> (\<I> \<parallel> \<I>))\<close>
    using wbisim_scomp_op_cong H1 H2 by blast
  also have \<open>\<dots> \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> ((\<V> \<parallel> \<V>) \<bullet> \<I>)\<close>
    by (simp add: bisim_scomp_op_cong bisim_wbisim choices_Choice_bisim B6)
  also have \<open>\<dots> \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<V> \<parallel> \<V>) \<bullet> \<I>\<close>
    using bisim_wbisim B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<V>'\<close> using A15
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
    apply (rule R2)
     apply (metis (no_types, lifting) Inr_in_defaults \<UU>_E \<UU>_def disjoint_iff id_apply image_id inputs_merge_op op.set_map(1) subsetD vimageE)
    apply (smt (verit, del_insts) Diff_disjoint Inr_inject disjoint_iff imageE op.set_map(2) outputs_merge_op subsetD vimageE)
    by (rule wbisim_refl)
  also have \<open>\<dots> \<approx> (!::('a, 'a, 'c) op)\<close>
    using sink_sink F3 wbisim_refl wbisim_scomp_op_cong wbisim_trans  by blast
  finally show ?thesis.
qed




end