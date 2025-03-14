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
no_notation split_empty_operator ("\<Lambda>")

lemma A1':
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

lemma A2':
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

lemma A3':
  \<open>((\<exclamdown>::(0, 'a :: {countable, defaults}, 'b) op) \<parallel> \<I>) \<bullet> \<V>' \<approx> map_op Inr id \<I>\<close>
proof -
  have \<open>((\<exclamdown>::(0, 'a, 'b) op) \<parallel> \<I>) \<bullet> \<V>' \<approx> ((\<exclamdown>::(0, 'a, 'b) op) \<parallel> \<I>) \<bullet> \<V> \<bullet> \<I>\<close>
    using bisim_wbisim B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> (map_op Inr id \<I>) \<bullet> \<I>\<close>
    using A3 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> map_op Inr id \<I>\<close>
    using map_op_out_id_vdash scomp_op_id_id wbisim_map_op wbisim_sym wbisim_trans by blast
  finally show ?thesis.
qed

lemma A4':
  \<open>\<V>' \<bullet> ! \<approx> ! \<parallel> !\<close>
proof -
  have \<open>\<V>' \<bullet> ! \<approx> \<V> \<bullet> (\<I> \<bullet> !)\<close>
    by (simp add: B3 bisim_map_op bisim_wbisim)
  also have \<open>\<dots> \<approx> \<V> \<bullet> !\<close>
    by (metis bisim_refl bisim_wbisim id_sink_op_sink_op scomp_op_def wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> ! \<parallel> !\<close> by (rule A4)
  finally show ?thesis.
qed

lemma A5':
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

lemma A6':
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

lemma A8':
  \<open>\<exclamdown> \<bullet> \<Lambda>' \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close>
proof -
  have \<open>\<exclamdown> \<bullet> \<Lambda>' \<approx> \<exclamdown> \<bullet> \<Lambda>\<close>
    by (smt (verit, best) B3 B4_1 bisim_sym bisim_wbisim wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_trans)
  also have \<open>\<dots> \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close>
    using A8 bisim_wbisim by blast
  finally show ?thesis.
qed

lemma A14':
  \<open>map_op id Inl (\<V>' :: (0 + 0, 0, 'd) op) \<approx> \<I>\<close>
  unfolding scomp_op_def
  by (coinduction rule: wbisim_coinduct_upto'')
    (auto elim!: step_map_op_elim step_comp_op_elim step_merge_op_elim step_id_op_cases)

lemma A15':
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

lemma A19':
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

lemma F3':
  \<open>map_op id Inr (\<V>' :: ('a :: {countable, defaults} + 'a, 'a, 'c) op)\<up> \<approx> (!::('a, 'd :: all_defaults, 'c) op)\<close>
proof -
  have \<open>map_op id Inr \<V>' \<up> \<approx> (map_op id Inr \<V> \<bullet> ((!::('a, 'd :: all_defaults, 'c) op) \<parallel> \<I>)) \<up>\<close> 
    using map_op_id_Inr_move_vdash wbisim_feedback_op_cong by blast
  also have \<open>\<dots> \<approx> map_op id Inr \<V>\<up> \<bullet> (!::('a, 'd :: all_defaults, 'c) op)\<close>
    apply (rule wbisim_trans)
     apply (rule wbisim_sym)
    apply (rule R2)
     apply (metis (no_types, lifting) Inr_in_defaults \<UU>_E \<UU>_def disjoint_iff id_apply image_id inputs_merge_op op.set_map(1) subsetD vimageE)
    apply (smt (verit, del_insts) Diff_disjoint Inr_inject disjoint_iff imageE op.set_map(2) outputs_merge_op subsetD vimageE)
    by (rule wbisim_refl)
  also have \<open>\<dots> \<approx> (!::('a, 'd :: all_defaults, 'c) op)\<close>
    using sink_sink F3 wbisim_refl wbisim_scomp_op_cong wbisim_trans  by blast
  finally show ?thesis.
qed

lemma F4':
  \<open>map_op Inr id (\<Lambda>'::('b :: {countable, defaults}, 'b + 'b, 'c) op) \<up> \<approx> (\<exclamdown>::('d :: all_defaults, 'b, 'c) op)\<close>
proof -
  have \<open>map_op Inr id \<Lambda>' \<up> \<approx> (((\<exclamdown>::('d :: all_defaults, 'b, 'c) op) \<parallel> \<I>) \<bullet> map_op Inr id \<Lambda>) \<up>\<close>
    using map_op_Inr_id_left_identity wbisim_feedback_op_cong by blast
  also have \<open>\<dots> \<approx> (\<exclamdown>::('d :: all_defaults, 'b, 'c) op) \<bullet> (map_op Inr id \<Lambda> \<up>)\<close>
    apply (rule wbisim_trans)
     apply (rule wbisim_sym)
     apply (rule R1)
      apply (smt (verit, ccfv_SIG) Inr_in_defaults \<UU>_E \<UU>_def disjoint_iff id_apply image_id inputs_split_op op.set_map(1) subsetD vimageE image_iff le_iff_inf)
     apply (smt (verit) Inr_in_defaults \<UU>_E \<UU>_def id_apply Inr_inject disjoint_iff imageE op.set_map(2) outputs_split_op subsetD vimageE)
    by (rule wbisim_refl)
  also have \<open>\<dots> \<approx> (\<exclamdown>::('d :: all_defaults, 'b, 'c) op) \<bullet> (\<exclamdown>::('b, 'a :: {countable, defaults}, 'c) op)\<close>
   using F4 bisim_refl bisim_scomp_op_cong bisim_wbisim by blast
  also have \<open>\<dots> \<approx> (\<exclamdown>::('d :: all_defaults, 'b, 'c) op)\<close>
    using scomp_op_dummy_source by blast
  finally show ?thesis.
qed

no_notation wbisim (infix "\<approx>"40)
no_notation id_empty_op ("\<I>")
no_notation scomp_op (infixl "\<bullet>" 65)
no_notation pcomp_op (infixl "\<parallel>" 64)
no_notation feedback_op ( "_ \<up>" [66] 65)
no_notation transp_empty_op ("\<X>")
no_notation sink_op ("!")
no_notation dummy_source_op ("\<exclamdown>")
no_notation merge_empty_op ("\<V>")
no_notation split_empty_op ("\<Lambda>")

notation wbisim_operator (infix "\<approx>"40)
notation id_empty_operator ("\<I>")
notation scomp_operator (infixl "\<bullet>" 65)
notation pcomp_operator (infixl "\<parallel>" 64)
notation feedback_operator ( "_ \<up>" [66] 65)
notation transp_empty_operator ("\<X>")
notation sink_op_0_operator ("!")
notation dummy_source_operator ("\<exclamdown>")
notation merge_empty_operator ("\<V>")
notation split_empty_operator ("\<Lambda>")

lemma A1:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V> \<approx> map_operator (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> \<V>)\<close>
  apply transfer
  apply (auto split: if_splits split: sum.splits)
  apply (rule A1')
  done

lemma A2:
  \<open>\<X> \<bullet> \<V> \<approx> map_operator (case_sum Inr Inl) id \<V>\<close>
  apply transfer
  using A2' by (auto split: sum.splits)

lemma A3:
  \<open>((\<exclamdown>::(0, 'a :: {countable, defaults}, 'b) operator) \<parallel> \<I>) \<bullet> \<V> \<approx> map_operator Inr id \<I>\<close>
  apply transfer
  using A3' by auto

lemma A4:
  \<open>\<V> \<bullet> ! \<approx> ! \<parallel> !\<close>
  apply transfer
  using A4' by auto

lemma A5:
  \<open>\<Lambda> \<bullet> (\<Lambda> \<parallel> \<I>) \<approx> map_operator id (case_sum Inr Inl) (\<Lambda> \<bullet> (\<I> \<parallel> \<Lambda>))\<close>
  apply transfer
  using A5' by (auto split: sum.splits)

lemma A6:
  \<open>\<Lambda> \<bullet> \<X> \<approx> map_operator id (case_sum Inr Inl) \<Lambda>\<close>
  apply transfer
  using A6' by (auto split: sum.splits)

lemma A8:
  \<open>(\<exclamdown> \<bullet> \<Lambda>) \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply transfer
  using A8' by auto

lemma A9:
  \<open>\<exclamdown> \<bullet> ! \<approx> \<I>\<close>
  apply transfer
  using A9 bisim_wbisim id_op_0_end_op wbisim_sym wbisim_trans by blast

lemma A12:
  \<open>\<exclamdown> \<approx> (\<I> :: (0, 0, 'd) operator)\<close>
  apply transfer
  using A12 bisim_sym bisim_trans bisim_wbisim id_op_0_end_op by blast

lemma A13:
  \<open>\<exclamdown> \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply transfer
  using A13 bisim_wbisim by auto

lemma A14:
  \<open>map_operator id Inl (\<V> :: (0 + 0, 0, 'd) operator) \<approx> \<I>\<close>
  apply transfer
  using A14' by auto

lemma A15:
  \<open>\<V> \<approx> map_operator reassoc reassoc (map_operator assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<V> \<parallel> \<V>)\<close>
  apply transfer
  using A15' by auto

lemma A16:
  \<open>! \<approx> (\<I> :: (0, 0, 'd) operator)\<close>
  apply transfer
  using A16 bisim_wbisim bisim_sym bisim_trans id_op_0_end_op by blast

lemma A17:
  \<open>! \<approx> ! \<parallel> !\<close>
  apply transfer
  apply (rule bisim_wbisim)
  apply (rule A17)
  done

lemma A18:
  \<open>(\<Lambda> :: (0, 0 + 0, 'd) operator) \<approx> map_operator id Inr \<I>\<close>
  apply transfer
  apply (auto split: if_splits split: sum.splits)
  apply (rule bisim_wbisim)
  apply (rule A18')
  done

lemma A19:
 "\<Lambda> \<approx> (\<Lambda> \<parallel> \<Lambda>) \<bullet> map_operator reassoc reassoc (map_operator assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)"
  apply transfer
  using A19' by auto

lemma F3:
 \<open>map_operator id Inr \<V>\<up> \<approx> !\<close>
  apply transfer
  apply (auto split: if_splits split: sum.splits intro: F3')
  done

lemma F4:
  \<open>map_operator Inr id \<Lambda>\<up> \<approx> \<exclamdown>\<close>
  apply transfer
  apply (auto split: if_splits split: sum.splits)
  apply (rule F4')
  done

end
