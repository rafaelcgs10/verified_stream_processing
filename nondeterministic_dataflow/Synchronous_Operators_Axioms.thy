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

lemma transp_op_aeq_op_scomp_op_bufs:
  \<open>map_op projl projr (comp_op Some buf2 (transp_op buf1) (aeq_op buf3))
  \<approx> aeq_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> buf3)\<close>
  apply (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  subgoal for buf1 buf2 buf3
    unfolding wsim_def
    apply auto
    subgoal
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (erule step_transp_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>aeq_op ((BENQ p x buf1 >> (buf2 \<circ> case_sum Inr Inl)) >> buf3)\<close>])
        apply auto
        apply fastforce
        done
      subgoal for p x
        apply (erule step_aeq_op_Out)
         apply simp
        apply (rule exI[of _ \<open>aeq_op ((buf1 >> (buf2 \<circ> case_sum Inr Inl)) >> BTL (Inr p) (BTL (Inl p) buf3))\<close>])
        apply auto
        by (smt (verit, ccfv_threshold) BAPPEND_BTL BHD_BULK_BENQ_right_not_empty BTL_def BULK_BENQ_empty Inr_Inl_False fun_upd_apply step_wstep step_aeq_op_Write)
      subgoal for _ x
        apply (erule step_transp_op_Out)
          apply (auto split: sum.splits)
        subgoal for p
          apply (rule exI[of _ \<open>aeq_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> buf3)\<close>])
          apply auto
          apply (rule wbc_base)
          by (metis BAPPEND_BENQ_BHD BENQ_case_sum_compose sum.simps(5))
        subgoal for p
          apply (rule exI[of _ \<open>aeq_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> buf3)\<close>])
          apply auto
          apply (rule wbc_base)
          by (metis BAPPEND_BENQ_BHD BENQ_case_sum_compose sum.simps(6))
        done
      subgoal for p
        apply (erule step_aeq_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>aeq_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> buf3)\<close>])
        apply auto
        apply (rule wbc_base)
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ \<open>BTL p buf2\<close>])
        apply (rule exI[of _ \<open>BENQ p (BHD p buf2) buf3\<close>])
        sorry
       apply (meson no_step_transp_op_Tau)
      subgoal
        apply (erule step_aeq_op_Tau)
         apply simp
        subgoal for p
          apply (rule exI[of _ \<open>aeq_op ((buf1 >> (buf2 \<circ> case_sum Inr Inl)) >> BTL (Inr p) (BTL (Inl p) buf3))\<close>])
          apply (auto simp flip: wstep_steps_Tau)
          by (smt (verit, del_insts) BAPPEND_BTL BHD_BULK_BENQ_right_not_empty BTL_def BULK_BENQ_empty fun_upd_apply step_aeq_op_Silent step_wstep)
        done
      done
    subgoal
      apply (erule step_aeq_op_cases)
      subgoal for p x
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (transp_op (BENQ p x buf1)) (aeq_op buf3))\<close>])
        apply (rule conjI)
         apply fastforce
        apply (rule wbc_sym)
        apply auto
        done
      subgoal for p x
        sorry
      subgoal for p
        sorry
      done
    done
  oops

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

section \<open>Axiom A19: Acopy and transpose\<close>

lemma acopy_op_comp_op_transp_op_id_op:
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