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

lemma aeq_vdash_absorb:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'))"
  using aeq_id_absorb using bisim_wbisim scomp_op_assoc wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma aeq_double_vdash_absorb:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'\<turnstile>))"
  using aeq_vdash_absorb using scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

lemma A10':
  "\<Q>' \<bullet> \<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q>' \<parallel> \<Q>')"
  apply (rule wbisim_trans[OF scomp_op_id_left_absorb A10])
  using inputs_acopy_op apply fastforce
  done

(* FIXME: make trans at the lemma *)
declare wbisim_trans[trans]

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

lemma F5':
  \<open>((\<I> \<parallel> \<C>) \<bullet> map_op reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Q>')) \<up> \<approx> ! \<bullet> \<exclamdown>\<close>
  oops

context notes [[typedef_overloaded]] begin
typedef ('ip, 'op, 'd) operator = 
  "{op :: ('ip :: defaults, 'op :: defaults, 'd) op. inputs op \<inter> defaults = {} \<and> outputs op \<inter> defaults = {}}" morphisms from_operator top_operator
  apply (rule exI[of _ end_op])
  apply simp
  done
end

setup_lifting type_definition_operator

lemma intersect_empty_iff:
  "A \<inter> B = {} \<longleftrightarrow> (\<forall> x \<in> A. x \<notin> B \<and> (\<forall> x \<in> B. x \<notin> A))"
  by blast

lift_definition 
  comp_operator :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) operator \<Rightarrow> ('ip2, 'op2, 'd) operator \<Rightarrow> ('ip1  :: defaults + 'ip2 :: defaults, 'op1 :: defaults + 'op2 :: defaults, 'd) operator" is comp_op
  apply (clarsimp simp add: intersect_empty_iff)
  apply (intro allI conjI ballI)
  subgoal for fun1 fun2 op1 op2 x
    apply (cases x)
    using inputs_comp_op_le[unfolded subset_eq, simplified]
     apply force+
    done
  subgoal 
    using inputs_comp_op_le by blast
  subgoal for fun1 fun2 op1 op2 x
    apply (cases x)
    using outputs_comp_op_le[unfolded subset_eq, simplified]
     apply force+
    done
  subgoal 
    using outputs_comp_op_le by blast
  done

lift_definition
  loop_operator ::  "('op \<rightharpoonup> 'ip) \<Rightarrow> ('ip \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip, 'op, 'd) operator \<Rightarrow> ('ip :: defaults, 'op :: defaults, 'd) operator" is loop_op
  by (smt (verit, del_insts) Diff_Diff_Int Diff_Int_distrib Int_Diff diff_shunt inputs_loop_op_le le_iff_inf outputs_loop_op_le)

lift_definition
  map_operator :: "('a :: defaults \<Rightarrow> 'b :: defaults) \<Rightarrow> ('c :: defaults \<Rightarrow> 'd :: defaults) \<Rightarrow> ('a, 'c, 'e) operator \<Rightarrow> ('b, 'd, 'e) operator" is 
  "\<lambda> f g op. (if f ` inputs op \<inter> defaults = {} \<and> g ` outputs op \<inter> defaults = {} then map_op f g op else end_op)"
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

(* FIXME: move me *)
lemma inputs_scomp_op_le_dest[dest!]:
  "c \<in> inputs (comp_op Some buf op1 op2) \<Longrightarrow> c \<in> Inl ` inputs op1"
  using set_mp[OF inputs_comp_op_le, simplified] by force
lemma inputs_pcomp_op_le_dest[dest!]:
  "c \<in> inputs (comp_op (\<lambda> _. None) buf op1 op2) \<Longrightarrow> c \<in> Inl ` inputs op1 \<or> c \<in> Inr ` (inputs op2)"
  using set_mp[OF inputs_comp_op_le, simplified] by force
lemma inputs_id_op_dest[dest!]:
  "x\<in>inputs (id_op buf) \<Longrightarrow> x \<notin> defaults"
  using inputs_id_op_alt by blast

lemma outputs_scomp_op_le_dest[dest!]:
  "c \<in> outputs (comp_op Some buf op1 op2) \<Longrightarrow>c \<in> Inr ` outputs op2"
  using set_mp[OF outputs_comp_op_le, simplified] by force
lemma outputs_pcomp_op_le_alt[dest!]:
  "c \<in> outputs (comp_op (\<lambda> _. None) buf op1 op2) \<Longrightarrow> c \<in> Inl ` outputs op1 \<or> c \<in> Inr ` outputs op2"
  using set_mp[OF outputs_comp_op_le, simplified] by force
lemma outputs_id_op_dest[dest!]:
  "x\<in>outputs (id_op buf) \<Longrightarrow> x \<notin> defaults"
  using outputs_id_op_alt by blast

lemma loop_operator_scomp_commute:
  "(op2 \<bullet> (op1\<up>)) \<approx> ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  unfolding pcomp_operator_def scomp_operator_def feedback_operator_def
  apply transfer
  apply (simp split: if_splits add: image_iff)
  apply (intro impI conjI)
  by (fastforce intro!: loop_op_scomp_commute[unfolded scomp_op_def feedback_op_def pcomp_op_def] Inl_in_defaults Inr_in_defaults simp add: image_iff disjoint_iff op.set_map ran_def split: sum.splits if_splits)+

end