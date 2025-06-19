theory Lifted_Table_2

imports
  "table_2/T2A1"
  "table_2/T2A2"
  "table_2/T2A3"
  "table_2/T2A4"
  "table_2/T2A5"
  "table_2/T2A6"
  "table_2/T2A7"
  "table_2/T2A8"
  "table_2/T2A9"
  "table_2/T2A10"
  "table_2/T2A11"
  "table_2/T2A12"
  "table_2/T2A13"
  "table_2/T2A14"
  "table_2/T2A15"
  "table_2/T2A16"
  "table_2/T2A17"
  "table_2/T2A18"
  "table_2/T2A19"
  "table_2/T2F3"
  "table_2/T2F4"
  "table_2/T2F5"
  "table_1/B4"
  "table_1/B5"
  "table_1/B3"
  "Lifted"
begin

no_notation wbisim_operator (infix "\<approx>"40)
no_notation id_empty_operator ("\<I>")
no_notation scomp_operator (infixl "\<bullet>" 65)
no_notation pcomp_operator (infixl "\<parallel>" 64)
no_notation feedback_operator ( "_ \<up>" [66] 65)
no_notation transp_empty_operator ("\<X>")
no_notation acopy_empty_operator ("\<C>")
no_notation aeq_empty_operator ("\<Q>")
no_notation sink_op_0_operator ("!")
no_notation dummy_source_operator ("\<exclamdown>")

lemma A1':
  \<open>(\<Q>' \<parallel> \<I>) \<bullet> \<Q>' \<approx> map_op assoc id ((\<I> \<parallel> \<Q>') \<bullet> \<Q>')\<close>
proof -
  have "(\<Q>' \<parallel> \<I>) \<bullet> \<Q>' \<approx> (\<Q>' \<parallel> \<I>\<turnstile>) \<bullet> \<Q>'" 
    by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<Q>'"
    using B5 bisim_wbisim wbisim_refl wbisim_scomp_op_cong wbisim_sym by blast 
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> \<I> \<bullet> \<Q>'"
    by (simp add: B6 bisim_wbisim wbisim_refl wbisim_scomp_op_cong)
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> \<Q>'" using scomp_op_id_left_absorb by (smt (verit, ccfv_SIG) aeq_double_vdash_absorb bisim_wbisim B3.B3 B4.B4_1 wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> \<Q> \<bullet> \<I>"
    using bisim_wbisim B3.B3 wbisim_sym by blast 
  also have "\<dots> \<approx> map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>) \<bullet> \<I>" using wbisim_refl wbisim_scomp_op_cong using A1 by blast
  also have "\<dots> \<approx> map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>')" using map_op_out_id_vdash bisim_wbisim B3.B3 wbisim_map_op wbisim_sym wbisim_trans by (smt (verit, best))
  also have "\<dots>  \<approx> map_op assoc id ((\<I> \<parallel> \<Q>)\<turnstile> \<bullet> \<Q>')" using scomp_op_id_left_absorb wbisim_map_op wbisim_sym by (smt (verit, best) aeq_double_vdash_absorb bisim_wbisim B3.B3 B4.B4_1 wbisim_refl wbisim_scomp_op_cong wbisim_trans)
  also have "\<dots>  \<approx> map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<Q>')" by (metis bisim_wbisim B6 wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have "\<dots>  \<approx> map_op assoc id ((\<I>\<turnstile> \<parallel> \<Q>') \<bullet> \<Q>')" by (simp add: bisim_wbisim B5 wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  also have "\<dots>  \<approx> map_op assoc id ((\<I> \<parallel> \<Q>') \<bullet> \<Q>')" by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  finally show ?thesis.
qed

lemma A2':
  \<open>\<X> \<bullet> \<Q>' \<approx> \<Q>'\<close>
proof -
  have \<open>\<X> \<bullet> \<Q>' \<approx> \<X> \<bullet> \<Q> \<bullet> \<I>\<close> using bisim_wbisim B3.B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<Q>'\<close>
    using A2 wbisim_refl wbisim_scomp_op_cong by blast
  finally show ?thesis.
qed

lemma A3':
  assumes "D = (\<exclamdown> :: (0, 'a :: {countable,defaults}, 'd option) op)"
    and "S = (! :: (0 + 'a :: {countable,defaults}, 0, 'd option) op)"
  shows  \<open>(D \<parallel> \<I>) \<bullet> \<Q>' \<approx> S \<bullet> \<exclamdown>\<close>
proof -
  have \<open>(D \<parallel> \<I>) \<bullet> \<Q>' \<approx> (D \<parallel> \<I>) \<bullet> \<Q> \<bullet> \<I>\<close>
    using bisim_wbisim B3.B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> (S \<bullet> \<exclamdown>) \<bullet> \<I>\<close>
    using A3 assms wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> S \<bullet> \<exclamdown>\<close>
    using bisim_wbisim B3.B3 B4.B4_1 wbisim_refl wbisim_scomp_op_cong wbisim_trans by (smt (verit, best))
  finally show ?thesis.
qed

lemma A4':
  \<open>\<Q>' \<bullet> ! \<approx> ! \<parallel> !\<close>
proof -
  have \<open>\<Q>' \<bullet> ! \<approx> \<Q> \<bullet> (\<I> \<bullet> !)\<close>
  using B3 bisim_wbisim by blast
  also have \<open>\<dots> \<approx> \<Q> \<bullet> !\<close>
    by (metis id_sink_op_sink_op scomp_op_def wbisim_refl wbisim_scomp_op_cong)
  also have \<open>\<dots> \<approx> ! \<parallel> !\<close> by (rule A4)
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
  have \<open>\<C> \<bullet> \<Q>' \<approx> (\<C> \<bullet> \<Q>)\<turnstile>\<close> using bisim_wbisim B3.B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<I>\<turnstile>\<close>
    using A11 wbisim_refl wbisim_scomp_op_cong by blast
  also have \<open>\<dots> \<approx> \<I>\<close> using scomp_op_id_id by blast
  finally show ?thesis.
qed

lemma A14':
  \<open>map_op id Inl (\<Q>' :: (0 + 0, 0, 'd option) op) \<approx> \<I>\<close>
  unfolding scomp_op_def
  by (coinduction rule: wbisim_coinduct_upto'')
    (auto elim!: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_id_op_cases)

lemma A15':
  \<open>\<Q>' \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<Q>' \<parallel> \<Q>')\<close>
proof -
  have H1: \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close> by (rule wbisim_refl)
  have H2: \<open>\<Q>' \<parallel> \<Q>' \<approx> (\<Q> \<parallel> \<Q>) \<bullet> (\<I> \<parallel> \<I>)\<close>
    using bisim_wbisim B5 wbisim_sym by blast
  have \<open>map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<Q>' \<parallel> \<Q>')
    \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> ((\<Q> \<parallel> \<Q>) \<bullet> (\<I> \<parallel> \<I>))\<close>
    using wbisim_scomp_op_cong H1 H2 by blast
  also have \<open>\<dots> \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> ((\<Q> \<parallel> \<Q>) \<bullet> \<I>)\<close>
    by (simp add: bisim_scomp_op_cong bisim_wbisim choices_Choice_bisim B6)
  also have \<open>\<dots> \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<Q> \<parallel> \<Q>) \<bullet> \<I>\<close>
    using bisim_wbisim B3.B3 wbisim_sym by blast
  also have \<open>\<dots> \<approx> \<Q>'\<close> using A15
    by (smt (verit) scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  finally show ?thesis by (rule wbisim_sym)
qed

lemma F3':
  assumes \<open>(S :: ('a :: {countable,defaults}, 0, 'c option) op) = !\<close>
    and "(Q' :: ('a :: {countable,defaults} + 'a, 'a, 'c option) op) = \<Q>'"
    and "(Q :: ('a :: {countable,defaults} + 'a, 'a, 'c option) op) = \<Q>"
    and "(I :: ('a :: {countable,defaults}, 'a, 'c option) op) = \<I>"
  shows  \<open>map_op id Inr Q' \<up> \<approx> S\<close>
proof -
  have "map_op id Inr Q' \<up> \<approx> (map_op id Inr Q \<bullet> (S \<parallel> I)) \<up>"  using assms map_op_id_Inr_move_vdash wbisim_feedback_op_cong by blast
  also have \<open>\<dots> \<approx> map_op id Inr Q\<up> \<bullet> S\<close>
    using assms apply -
    apply (rule wbisim_trans)
     apply (rule wbisim_sym)
     apply hypsubst_thin
     apply (rule R2)
      prefer 3
      apply hypsubst_thin
    using wbisim_refl apply blast
     apply (metis (no_types, lifting) Inr_in_defaults \<UU>_E \<UU>_def disjoint_iff id_apply image_id inputs_aeq_op op.set_map(1) subsetD vimageE)
    apply (smt (verit, del_insts) Diff_disjoint Inr_inject disjoint_iff imageE op.set_map(2) outputs_aeq_op subsetD vimageE)
    done
  also have \<open>\<dots> \<approx> S\<close> using assms sink_sink F3 wbisim_refl wbisim_scomp_op_cong wbisim_trans by (smt (verit, best))
  finally show ?thesis.
qed

no_notation wbisim (infix "\<approx>"40)
no_notation id_empty_op ("\<I>")
no_notation scomp_op (infixl "\<bullet>" 65)
no_notation pcomp_op (infixl "\<parallel>" 64)
no_notation feedback_op ( "_ \<up>" [66] 65)
no_notation transp_empty_op ("\<X>")
no_notation acopy_empty_op ("\<C>")
no_notation aeq_empty_op ("\<Q>")
no_notation sink_op ("!")
no_notation dummy_source_op ("\<exclamdown>")

notation wbisim_operator (infix "\<approx>"40)
notation id_empty_operator ("\<I>")
notation scomp_operator (infixl "\<bullet>" 65)
notation pcomp_operator (infixl "\<parallel>" 64)
notation feedback_operator ( "_ \<up>" [66] 65)
notation transp_empty_operator ("\<X>")
notation acopy_empty_operator ("\<C>")
notation aeq_empty_operator ("\<Q>")
notation sink_op_0_operator ("!")
notation dummy_source_operator ("\<exclamdown>")


lemma A1:
  \<open>(\<Q> \<parallel> \<I>) \<bullet> \<Q> \<approx> map_operator assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>)\<close>
  apply transfer
  using A1' by (auto split: sum.splits)

lemma A2:
  \<open>\<X> \<bullet> \<Q> \<approx> \<Q>\<close>
  apply transfer
  using A2' by simp

lemma A3:
  assumes "D = (\<exclamdown> :: (0, 'a :: {countable,defaults}, 'd option) operator)"
    and "S = (! :: (0 + 'a :: {countable,defaults}, 0 , 'd option) operator)"
  shows  \<open>(D \<parallel> \<I>) \<bullet> \<Q> \<approx> S \<bullet> \<exclamdown>\<close>
  using assms apply -
  apply transfer
  using A3' by blast

lemma A4:
  \<open>\<Q> \<bullet> ! \<approx> ! \<parallel> !\<close>
  apply transfer
  using A4' by simp

lemma A5:
  \<open>\<C> \<bullet> (\<C> \<parallel> \<I>) \<approx> map_operator id assoc (\<C> \<bullet> (\<I> \<parallel> \<C>))\<close>
  apply transfer
  using A5 by simp

lemma A6:
  \<open>\<C> \<bullet> \<X> \<approx> \<C>\<close>
  apply transfer
  using A6 by simp

lemma A7:
  \<open>\<C> \<bullet> (! \<parallel> \<I>) \<approx> map_operator id Inr \<I>\<close>
  apply transfer
  using A7 by auto

lemma A8:
  \<open>\<exclamdown> \<bullet> \<C> \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply transfer
  using A8 bisim_wbisim by blast

lemma A9:
  \<open>\<exclamdown> \<bullet> ! \<approx> \<I>\<close>
  apply transfer
  using A9 bisim_wbisim id_op_0_end_op wbisim_sym wbisim_trans by blast

lemma A10:
  \<open>\<Q> \<bullet> \<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> (map_operator reassoc reassoc (map_operator assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q> \<parallel> \<Q>)\<close>
  by transfer (simp add: A10')

lemma A11:
  \<open>\<C> \<bullet> \<Q> \<approx> \<I>\<close>
  by transfer (rule A11')

lemma A12:
  \<open>\<exclamdown> \<approx> (\<I> :: (0, 0, 'd) operator)\<close>
  apply transfer
  using A12 bisim_sym bisim_trans bisim_wbisim id_op_0_end_op by blast

lemma A13:
  \<open>\<exclamdown> \<approx> \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply transfer
  using A13 bisim_wbisim by blast

lemma A14:
  \<open>map_operator id Inl (\<Q> :: (0 + 0, 0, 'd option) operator) \<approx> \<I>\<close>
  apply transfer
  using A14' by simp

lemma A15:
  \<open>\<Q> \<approx> map_operator reassoc reassoc (map_operator assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<Q> \<parallel> \<Q>)\<close>
  apply transfer
  using A15' by simp

lemma A16:
  \<open>! \<approx> (\<I> :: (0, 0, 'd) operator)\<close>
  apply transfer
  using A16 bisim_wbisim bisim_sym bisim_trans id_op_0_end_op by blast

lemma A17:
  \<open>! \<approx> ! \<parallel> !\<close>
  apply transfer
  using A17 bisim_wbisim by blast

lemma A18:
  \<open>map_operator Inl id (\<C> :: (0, 0 + 0, 'd) operator) \<approx> \<I>\<close>
  apply transfer
  using A18 bisim_wbisim by auto

lemma A19:
  \<open>\<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> map_operator reassoc reassoc (map_operator assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)\<close>
  apply transfer
  using A19 by fastforce

lemma F3:
  assumes \<open>(S :: ('a :: {countable,defaults}, 0, 'c option) operator) = !\<close>
    and \<open>(Q' :: ('a :: {countable,defaults} + 'a, 'a, 'c option) operator) = \<Q>\<close>
    and \<open>(Q :: ('a :: {countable,defaults} + 'a, 'a, 'c option) operator) = \<Q>\<close>
    and \<open>(I :: ('a :: {countable,defaults}, 'a, 'c option) operator) = \<I>\<close>
  shows  \<open>map_operator id Inr Q' \<up> \<approx> S\<close>
  using assms
  apply -
  apply transfer
  using F3' by auto

lemma F4:
  \<open>map_operator Inr id \<C> \<up> \<approx> \<exclamdown>\<close>
  apply transfer
  using F4 bisim_wbisim by auto

lemma F5:
  \<open>((\<I> \<parallel> \<C>) \<bullet> map_operator reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Q>)) \<up>
  \<approx> (!::('a :: {countable, defaults}, 0, 'b option) operator) \<bullet> (\<exclamdown>::(0, 'a, 'b option) operator)\<close>
  apply transfer
  using F5' by simp

end