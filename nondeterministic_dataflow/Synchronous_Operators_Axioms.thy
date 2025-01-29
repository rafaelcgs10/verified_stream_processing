\<comment> \<open>Axioms from Table 3 for equalitity test and acopy\<close>
theory Synchronous_Operators_Axioms

imports
  BNA_Operators
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom: A1: Equality test commutes with identity\<close>
lemma aeq_op_commutes_identity:
  "(\<Q> \<parallel> \<I>) \<bullet> \<Q> ~ map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>)"
  oops

section \<open>Axiom: A2: Equality test transpose is equality test\<close>
lemma aeq_op_transp_op:
  "\<X> \<bullet> \<Q> \<approx> \<Q>"
  oops

section \<open>Axiom: A3: Equality test dummy source and identity\<close>
lemma aeq_op_dummy_source_op:
  "map_op projr id (\<exclamdown> \<parallel> \<I>) \<bullet> \<Q> \<approx> \<I>"
  oops

section \<open>Axiom: A4: Equality test to sink\<close>
lemma aeq_op_sink_op:
   "\<Q> \<bullet> ! ~ ! \<parallel> !"
  oops

section \<open>Axiom: A5: Acopy to acopy and identity\<close>
lemma acopy_op_acopy_id:
  "\<C> \<bullet> (\<C> \<parallel> \<I>) ~ map_op id assoc (\<C> \<bullet> (\<I> \<parallel> \<C>))"
  oops

section \<open>Axiom: A6: Acopy to transpose\<close>
lemma acopy_op_transp_op:
 "\<C> \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<C>"
  oops

section \<open>Axiom: A7: Acopy to sink and identity\<close>
lemma acopy_op_acopy_sink:
  "map_op id projr (\<C> \<bullet> (! \<parallel> \<I>)) ~ \<I>"
  oops

section \<open>Axiom: A8: Acopy dummy source\<close>

lemma acopy_op_dummy_source:
  \<open>\<exclamdown> \<bullet> \<C> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def
  apply (rule conjI)
  subgoal
    unfolding scomp_op_def pcomp_op_def
    apply (subst comp_op_code)
    apply (subst acopy_op_code)
    apply auto
    done
  subgoal
    apply (metis cempty_iff choices_pcomp_op_dummy_source step_choicesE)
    done
  done

section \<open>Axiom: A10: Equality test to acopy\<close>
lemma aeq_op_acopy:
 "\<Q> \<bullet> \<C> ~ (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q> \<parallel> \<Q>)"
  oops

section \<open>Axiom: A11: Acopy to equality test\<close>
lemma acopy_op_aeq:
  "\<C> \<bullet> \<Q> \<approx> \<I>"
  oops

section \<open>Axiom A15: Transpose and equality test\<close>
lemma aeq_op_transp_aeq:
  assumes "Qmn \<equiv> \<Q> :: (('m :: countable + 'n ::countable) + 'm + 'n, 'm + 'n, 'd) op"
    and "Qm \<equiv> \<Q> :: ('m + 'm, 'm, 'd) op"
    and "Qn \<equiv>  \<Q> :: ('n + 'n, 'n, 'd) op"
    and "Imm \<equiv> \<I> :: ('m, 'm, 'd) op"
    and "Inn \<equiv> \<I> :: ('n, 'n, 'd) op"
    and "Xnm \<equiv> \<X> :: ('n + 'm, 'm + 'n, 'd) op"
  shows "Qmn \<approx> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xnm) \<parallel> Inn) \<bullet> (Qm \<parallel> Qn)"
  oops

section \<open>Axiom A19: Acopy and equality test\<close>
lemma acopy_op_transp_acopy:
  assumes "Cmn \<equiv> \<C> :: ('m + 'n,('m :: countable + 'n ::countable) + 'm + 'n,  'd) op"
    and "Cm \<equiv> \<C> :: ('m, 'm + 'm, 'd) op"
    and "Cn \<equiv> \<C> :: ('n, 'n + 'n, 'd) op"
    and "Imm \<equiv> \<I> :: ('m, 'm, 'd) op"
    and "Inn \<equiv> \<I> :: ('n, 'n, 'd) op"
    and "Xmn \<equiv> \<X> :: ('m + 'n, 'n + 'm, 'd) op"
  shows "Cmn \<approx> (Cm \<parallel> Cn) \<bullet> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xmn) \<parallel> Inn)"
  oops

section \<open>Axiom F3: Loop equality test\<close>
lemma loop_op_aeq_sink:
  "map_op id Inr \<Q>\<up> ~ !"
  oops

section \<open>Axiom F4: Loop acopy\<close>
lemma loop_op_acopy_dummy_source:
  "map_op Inr id \<C>\<up> ~ \<exclamdown>"
  oops

end