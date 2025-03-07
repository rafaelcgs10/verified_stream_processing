\<comment> \<open>Axioms from Table 1 for BNA operators\<close>
theory Lifted

imports
  BNA_Operators
  BNA_Axioms
  Synchronous_Operators_Axioms
  Asynchronous_Dataflow_Axioms
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)
no_notation nth (infixl "!" 100)

section \<open>Axioms for split_op surrounded by identities\<close>

lemma split'_id_absorb_right:
  \<open>\<Lambda>' \<approx> \<Lambda>'\<turnstile>\<close>
  using split_id_absorb_right bisim_wbisim scomp_op_assoc wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

lemma split'_id_absorb:
  \<open>\<Lambda>' \<approx> (\<stileturn>\<Lambda>')\<turnstile>\<close>
  using split'_id_absorb_right scomp_op_id_op_left_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

section \<open>Axioms for merge_op surrounded by identities\<close>

lemma merge'_id_absorb_left:
  \<open>\<V>' \<approx> \<stileturn>\<V>'\<close>
  using merge_id_absorb_left bisim_wbisim scomp_op_assoc wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma merge'_id_absorb:
  \<open>\<V>' \<approx> (\<stileturn>\<V>')\<turnstile>\<close>
  using merge'_id_absorb_left scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

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

section \<open>Properties of compositions and feedback surrounded by identities\<close>

lemma scomp_op_move_vdash:
  "\<stileturn>((op1 \<bullet> op2)\<turnstile>) \<approx> \<stileturn>op1 \<bullet> op2\<turnstile>"
  by (smt (verit, del_insts) bisim_wbisim scomp_op_assoc scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)

lemma pcomp_op_move_vdash_left:
  "\<stileturn>(op1 \<parallel> op2) \<approx> \<stileturn>op1 \<parallel> \<stileturn>op2"
    by (smt (verit, del_insts) bisim_comp_op_cong bisim_scomp_op_cong bisim_trans bisim_wbisim choices_Choice_bisim pcomp_op_def pcomp_op_id_id pcomp_op_scomp_distributes wbisim_sym wbisim_trans)

lemma pcomp_op_move_vdash_right:
 "(op1 \<parallel> op2)\<turnstile> \<approx> op1\<turnstile> \<parallel> op2\<turnstile>"
    by (smt (verit, del_insts) bisim_comp_op_cong bisim_scomp_op_cong bisim_trans bisim_wbisim choices_Choice_bisim pcomp_op_def pcomp_op_id_id pcomp_op_scomp_distributes wbisim_sym wbisim_trans)

lemma pcomp_op_move_vdash:
  "\<stileturn>((op1 \<parallel> op2)\<turnstile>) \<approx> \<stileturn>(op1\<turnstile>) \<parallel> \<stileturn>(op2\<turnstile>)"
proof -
  have "(\<stileturn>(op1 \<parallel> op2))\<turnstile> \<approx> (\<stileturn>op1 \<parallel> \<stileturn>op2)\<turnstile>" (is "?a \<approx> ?b")
    using pcomp_op_move_vdash_left wbisim_refl wbisim_scomp_op_cong by blast
  moreover have "?b \<approx> \<stileturn>(op1\<turnstile>) \<parallel> \<stileturn>(op2\<turnstile>)" 
    using pcomp_op_move_vdash_right wbisim_refl wbisim_scomp_op_cong 
    by (smt (verit, best) bisim_wbisim pcomp_op_def scomp_op_assoc wbisim_comp_op_cong wbisim_trans)
  ultimately show ?thesis
    by (meson bisim_wbisim scomp_op_assoc wbisim_sym wbisim_trans)
qed

lemma feedback_op_move_left_vdash:
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
  shows  "\<stileturn>(op\<up>) \<approx> \<stileturn>op\<up>"
  using assms apply -
  apply (rule wbisim_trans[OF loop_op_scomp_commute])
  apply (simp_all add: bisim_wbisim pcomp_op_id_id wbisim_loop_op_cong wbisim_refl wbisim_scomp_op_cong)
  done

lemma feedback_op_move_right_vdash:
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
  shows  "(op\<up>)\<turnstile> \<approx> op\<turnstile>\<up>"
  using assms apply -
  apply (rule wbisim_trans[OF loop_op_distribute_scomp_op])
  apply (simp_all add: bisim_wbisim pcomp_op_id_id wbisim_loop_op_cong wbisim_refl wbisim_scomp_op_cong)
  done

lemma feedback_op_move_vdash:
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
  shows  "(\<stileturn>(op\<up>))\<turnstile> \<approx> (\<stileturn>op)\<turnstile>\<up>"
  using assms apply -
  apply (rule wbisim_trans[OF wbisim_scomp_op_cong])
    apply (rule feedback_op_move_left_vdash)
     apply assumption+
   apply (rule wbisim_refl)
  apply (rule feedback_op_move_right_vdash)
   apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def)
  done

section \<open>Typedef and lifting\<close>

context notes [[typedef_overloaded]] begin
typedef ('ip, 'op, 'd) operator = 
  "{op :: ('ip :: {countable,defaults}, 'op :: {countable,defaults}, 'd) op.
     \<exists> op' :: ('ip, 'op, 'd) op. op \<approx> \<stileturn>(op'\<turnstile>) \<and> inputs op' \<inter> defaults = {} \<and> outputs op' \<inter> defaults = {}}" morphisms from_operator top_operator
  apply (rule exI[of _ "\<stileturn>(\<oslash>\<turnstile>)"])
  apply simp
  apply (rule exI[of _ "\<stileturn>\<oslash>"])
  apply (auto intro: wbisim_refl)
  apply (smt (verit, ccfv_SIG) bisim_wbisim scomp_op_assoc scomp_op_id_op_left_neutral scomp_op_move_vdash wbisim_sym wbisim_trans)
   apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def)
  done

setup_lifting type_definition_operator

lemma intersect_empty_iff:
  "A \<inter> B = {} \<longleftrightarrow> (\<forall> x \<in> A. x \<notin> B \<and> (\<forall> x \<in> B. x \<notin> A))"
  by blast

lemma step_taus_inputs_outputs:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   inputs op' \<subseteq> inputs op \<and> outputs op' \<subseteq> outputs op"
  apply (induct op arbitrary:  rule: converse_rtranclp_induct)
  subgoal
    by simp
  subgoal
    by (meson dual_order.trans step_inputs_outputs)
  done

lemma wstep_inputs_outputs:
  "wstep io op op' \<Longrightarrow>
   inputs op' \<subseteq> inputs op \<and> outputs op' \<subseteq> outputs op"
  unfolding wstep_def by (smt (verit, ccfv_SIG) estep.elims pick_middlep rtranclp.rtrancl_into_rtrancl rtranclp_less_eq step_inputs_outputs step_taus_inputs_outputs wstep_def wstep_steps_Tau)

lemma sub_op_trans:
 "sub_op op1 op2 n \<Longrightarrow> sub_op op2 op3 m \<Longrightarrow> sub_op op1 op3 (n + m)"
  oops

lemma
  "sub_op (Read p f) op1 n \<Longrightarrow> op1 \<approx> op2 \<Longrightarrow> p \<in> inputs op2"
proof (induct p op1 arbitrary: op2 f rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case 
    apply -
    apply (erule wbisim.cases)
    unfolding wsim_def
    apply safe
    apply (metis Read_not_finished finished_no_step stepReadE wstep_Inp_inputs)
    done
next
  case (Read2 p p' f' x n f op2)
  then show ?case 
    apply -
      apply (drule meta_spec[of _ n])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
    using wbisim_refl apply auto[1]
    apply (erule wbisim.cases)
    unfolding wsim_def
    apply safe
    apply (drule spec2, drule mp, rule SR[where x=x])
    apply safe
      apply (meson Read2.hyps(2) less_Suc_eq subset_eq wstep_inputs_outputs)
      done
next
  case (Write p p' op' x d g)
  then show ?case 
    apply -
    apply (erule wbisim.cases)
    unfolding wsim_def
    apply safe
    apply (meson SW lessI subsetD wstep_inputs_outputs)
    done
next
  case (Silent p op' d)
  then show ?case 
    apply -
    apply (erule wbisim.cases)
    unfolding wsim_def
    apply safe
    apply (metis lessI step.simps subsetD wstep_inputs_outputs)
    done
next
  case (Choice p ops n g op2)
  then show ?case 
    apply -
    apply safe
    subgoal for op'
      oops

      
lemma scomp_op_id_right_absorb:
  assumes "outputs op1 \<inter> defaults = {}"
  shows  "op1 \<bullet> \<stileturn>op2 \<approx> op1 \<bullet> op2"
  sorry


lift_definition 
  scomp_operator :: "('ip1 :: {countable,defaults}, 'op1  :: {countable,defaults}, 'd) operator \<Rightarrow> ('op1, 'op2  :: {countable,defaults}, 'd) operator \<Rightarrow>
  ('ip1, 'op2, 'd) operator" is "scomp_op"
  apply (clarsimp simp add: intersect_empty_iff)
  subgoal for op1 op2 op1' op2'
    apply (intro exI[of _ "scomp_op op1' op2'"])
    apply (intro allI conjI ballI)
    subgoal
      apply (rule wbisim_trans)
       apply (rule wbisim_scomp_op_cong)
        apply assumption+
      apply (rule wbisim_trans[rotated])
       apply (rule wbisim_sym)
       apply (rule scomp_op_move_vdash)
      apply (rule wbisim_trans[rotated])
       apply (rule scomp_op_id_left_absorb)
       apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_inputs)[1]
      apply (rule wbisim_trans[rotated])
       apply (rule scomp_op_id_right_absorb)
       apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_outputs)[1]
      apply (meson bisim_sym bisim_wbisim scomp_op_assoc wbisim_refl wbisim_scomp_op_cong)
      done
       apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_inputs)
    done
  done

(* lift_definition 
  comp_operator :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) operator \<Rightarrow> ('ip2, 'op2, 'd) operator \<Rightarrow>
  ('ip1  :: {countable,defaults} + 'ip2 :: {countable,defaults}, 'op1 :: {countable,defaults} + 'op2 :: {countable,defaults}, 'd) operator" is "comp_op"
  apply (clarsimp simp add: intersect_empty_iff)
  subgoal for fun1 fun2 op1 op2 op' op'a
  apply (intro exI[of _ "comp_op fun1 fun2 op1 op2"])
    apply (intro allI conjI ballI)
    subgoal
      apply (rule wbisim_trans)
 *)



(* lift_definition
  loop_operator ::  "('op \<rightharpoonup> 'ip) \<Rightarrow> ('ip \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip, 'op, 'd) operator \<Rightarrow> ('ip :: defaults, 'op :: defaults, 'd) operator" is loop_op
  by (smt (verit, del_insts) Diff_Diff_Int Diff_Int_distrib Int_Diff diff_shunt inputs_loop_op_le le_iff_inf outputs_loop_op_le)
 *)

lemma map_op_out_id_left_vdash:
  "map_op id f (\<stileturn>op) \<approx> \<stileturn>(map_op id f op)"
  oops

lemma aux:
  "map_op f g (\<stileturn>(op\<turnstile>)) \<approx> \<stileturn>((map_op f g op)\<turnstile>)"
  apply (rule wbisim_trans)
  sorry

lemma aux2:
  "p \<in> inputs op \<Longrightarrow> p \<in> inputs (\<stileturn>op)"
       apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_inputs)[1]

  find_theorems inputs id_op 

  oops

lift_definition
  map_operator :: "('a :: {countable,defaults} \<Rightarrow> 'b :: {countable,defaults}) \<Rightarrow> ('c :: {countable,defaults} \<Rightarrow> 'd :: {countable,defaults}) \<Rightarrow> ('a, 'c, 'e) operator \<Rightarrow> ('b, 'd, 'e) operator" is 
  "\<lambda> f g op. (if f ` inputs op \<inter> defaults = {} \<and> g ` outputs op \<inter> defaults = {} then map_op f g op else end_op)"
  apply (simp add: op.set_map split: if_splits)
  apply (intro allI conjI impI)
  subgoal for fun1 fun2 op
    apply safe
    subgoal for op'
    apply (rule exI[of _ "map_op fun1 fun2 op'"])
    apply (intro conjI)
      apply safe
    subgoal
  apply (rule wbisim_trans[rotated])
       apply (rule aux)
      apply (meson wbisim_map_op)
      done
    subgoal for p
       apply (auto simp add: image_iff disjoint_iff op.set_map ran_def)[1]
      subgoal for p'
        apply (drule spec[of _ "fun1 p'"])
        apply (drule mp)
         apply (rule bexI[of _ "p'"])
          apply simp_all
       apply (auto simp add: image_iff disjoint_iff op.set_map ran_def dest!: wbisim_inputs)[1]
        
        thm wbisim_inputs

        term "fun1 p'"

    find_theorems "_ = _ ` _ \<Longrightarrow> _"




  find_theorems map_op name: cong

end
  by (auto simp add: op.set_map)

no_notation scomp_op (infixl "\<bullet>" 65)
definition scomp_operator (infixl "\<bullet>" 65) where
  "scomp_operator op1 op2 = map_operator projl projr (comp_operator Some (\<lambda>_. []) op1 op2)"

no_notation feedback_op ( "_ \<up>" [66] 65)
no_notation pcomp_op (infixl "\<parallel>" 64)

definition pcomp_operator (infixl "\<parallel>" 64) where
  "pcomp_operator = comp_operator (\<lambda>_. None) (\<lambda>_. [])"

definition feedback_operator ( "_ \<up>" [66] 65) where
  "feedback_operator op = map_operator projl projl (loop_operator (case_sum (\<lambda> _. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (\<lambda> _. [])) op)"

lift_definition id_operator :: "('a \<Rightarrow> 'b buf) \<Rightarrow> ('a :: {countable, defaults}, 'a, 'b) operator" is id_op
  using outputs_id_op inputs_id_op by force

no_notation id_empty_op ("\<I>")

abbreviation id_empty_operator ("\<I>") where
  "\<I> \<equiv> id_operator (\<lambda> _. [])"

no_notation wbisim (infix "\<approx>"40)

lift_definition wbisim_operator :: "('a :: defaults, 'b :: defaults, 'c) operator \<Rightarrow> ('a, 'b, 'c) operator \<Rightarrow> bool" is wbisim.

abbreviation wbisim_operator' (infix "\<approx>"40) where
  "wbisim_operator' \<equiv> wbisim_operator"

lemma loop_operator_scomp_commute:
  "(op2 \<bullet> (op1\<up>)) \<approx> ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  unfolding pcomp_operator_def scomp_operator_def feedback_operator_def
  apply transfer
  apply (simp split: if_splits add: image_iff)
  apply (intro impI conjI)
  by (fastforce intro!: loop_op_scomp_commute[unfolded scomp_op_def feedback_op_def pcomp_op_def] Inl_in_defaults Inr_in_defaults simp add: image_iff disjoint_iff op.set_map ran_def split: sum.splits if_splits)+

end