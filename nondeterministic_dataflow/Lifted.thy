\<comment> \<open>Axioms from Table 1 for BNA operators\<close>
theory Lifted

imports
  BNA_Operators
  BNA_Axioms
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)


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
    using inputs_comp_op_le by force
  subgoal for fun1 fun2 op1 op2 x
    apply (cases x)
    using outputs_comp_op_le[unfolded subset_eq, simplified]
     apply force+
    done
  subgoal 
    using outputs_comp_op_le by force
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


lemma id_op_reads:
  "sub_op (Read p f) (id_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>id_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) id_op_code, simp) 
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) id_op_code, simp; force) 
qed

lemma id_op_writes:
  "sub_op (Write op p x) (id_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>id_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) id_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) id_op_code, simp)
qed

lemma inputs_id_op[intro]:
  "inputs (id_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using id_op_reads by (metis inputs_sub_op_Read)
lemma inputs_id_op_alt[intro]:
  "\<forall>x\<in>inputs (id_op buf). x \<notin> defaults"
  using inputs_id_op[unfolded subset_eq, simplified] by fast
lemma outputs_id_op[intro]:
  "outputs (id_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using id_op_writes by (metis outputs_sub_op_Write)
lemma outputs_id_op_alt[intro]:
  "\<forall>x\<in>outputs (id_op buf). x \<notin> defaults"
  using outputs_id_op[unfolded subset_eq, simplified] by fast



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
  apply (simp split: if_splits)
  apply (intro impI conjI)
  subgoal
    by (auto intro!: loop_op_scomp_commute [unfolded scomp_op_def feedback_op_def pcomp_op_def])
  subgoal
    apply (auto intro!: inputs_id_op_alt Inl_in_defaults Inr_in_defaults simp add: inputs_id_op_alt disjoint_iff op.set_map ran_def dest!:  split: sum.splits if_splits)
      apply (metis inputs_id_op_alt)
     apply (meson Inl_in_defaults)
    apply (meson Inr_in_defaults)
    done
  subgoal
    by (auto 5 5 simp add: op.set_map ran_def split: sum.splits if_splits)
  subgoal
    by (auto 5 5 simp add: op.set_map ran_def split: sum.splits if_splits)
  subgoal
    by (auto intro!: inputs_id_op_alt Inl_in_defaults Inr_in_defaults simp add: inputs_id_op_alt disjoint_iff op.set_map ran_def dest!:  split: sum.splits if_splits)
  subgoal
    by (auto 5 5 simp add: op.set_map ran_def dest!: set_mp[OF outputs_comp_op_le, simplified] set_mp[OF outputs_loop_op_le, simplified] set_mp[OF inputs_comp_op_le, simplified] set_mp[OF inputs_loop_op_le, simplified] split: sum.splits if_splits)
  subgoal
    apply (auto 2 2 simp add: op.set_map ran_def disjoint_iff_not_equal dest!: set_mp[OF outputs_comp_op_le, simplified] set_mp[OF outputs_loop_op_le, simplified] set_mp[OF inputs_comp_op_le, simplified] set_mp[OF inputs_loop_op_le, simplified] split: sum.splits if_splits)
     apply (metis (no_types, lifting) Inl_in_defaults Inr_in_defaults sum.exhaust_sel)+
    done
  subgoal
    apply (auto 0 0 intro!: Inl_in_defaults Inr_in_defaults simp add: inputs_id_op_alt disjoint_iff op.set_map ran_def dest!:  split: sum.splits if_splits)
            apply (metis inputs_id_op_alt)
           apply (meson Inl_in_defaults)
          apply (meson Inr_in_defaults)
         apply force+
    done
  subgoal
    by (auto 5 5 simp add: op.set_map ran_def dest!: set_mp[OF outputs_comp_op_le, simplified] set_mp[OF outputs_loop_op_le, simplified] set_mp[OF inputs_comp_op_le, simplified] set_mp[OF inputs_loop_op_le, simplified] split: sum.splits if_splits)
  subgoal
    by (auto 5 5 simp add: op.set_map ran_def dest!: set_mp[OF outputs_comp_op_le, simplified] set_mp[OF outputs_loop_op_le, simplified] set_mp[OF inputs_comp_op_le, simplified] set_mp[OF inputs_loop_op_le, simplified] split: sum.splits if_splits)
  subgoal
    by (auto intro!: Inl_in_defaults Inr_in_defaults simp add: inputs_id_op_alt disjoint_iff op.set_map ran_def dest!:  split: sum.splits if_splits)
  subgoal
    by (auto 5 5 simp add: op.set_map ran_def dest!: set_mp[OF outputs_comp_op_le, simplified] set_mp[OF outputs_loop_op_le, simplified] set_mp[OF inputs_comp_op_le, simplified] set_mp[OF inputs_loop_op_le, simplified] split: sum.splits if_splits)
  done

end