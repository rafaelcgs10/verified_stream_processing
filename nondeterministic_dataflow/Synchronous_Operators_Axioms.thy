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

lemma acopy_op_aeq_op_id_op_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf buf) \<C> \<Q>) \<approx> id_op buf\<close>
  apply (coinduction arbitrary: buf rule: wbisim_coinduct_upto)
  subgoal for buf
    unfolding wsim_def
    apply auto
    subgoal
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (erule step_acopy_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>id_op (BENQ p x buf)\<close>])
        apply (rule conjI)
         apply fast
        apply (rule wbc_bisim)
        apply (rule wbisim_trans)
        sorry
          apply (meson no_step_aeq_op_Out no_step_acopy_op_Out)+
        apply (simp split: sum.splits)
      subgoal
        apply (erule step_aeq_op_Inp_L)
         apply simp
        apply (rule exI[of _ \<open>id_op buf\<close>])
        apply (rule conjI)
         apply fast
        sorry
      subgoal
        apply (erule step_aeq_op_Inp_R)
         apply simp
        apply (rule exI[of _ \<open>id_op buf\<close>])
        apply (rule conjI)
         apply fast
        sorry
       apply (meson no_step_acopy_op_Tau no_step_aeq_op_Tau)+
      done
    subgoal
      apply (erule step_id_op_cases)
        apply auto
      subgoal for p x
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BENQ p x buf) (BENQ p x buf)) \<C> \<Q>)\<close>])
        apply auto
        apply (rule step_io_step_tau_tau_wstep)
          apply fastforce+
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf) (BTL p buf)) \<C> \<Q>)\<close>])
        apply auto
        apply (rule step_tau_step_tau_step_io_wstep)
          apply fastforce+
        done
      done
    done
  oops

lemma acopy_op_aeq_op_id_op_bufs':
  \<open>map_op projl projr (comp_op Some (case_sum buf buf) \<C> \<Q>) \<approx> id_op buf\<close>
  apply (rule wbisim_coinduct_upto[of \<open>\<lambda>op1 op2.
  (\<exists>buf. op1 = map_op projl projr (comp_op Some (case_sum buf buf) \<C> \<Q>) \<and> op2 = id_op buf)
  \<or> (\<exists>buf p x. op1 = map_op projl projr (comp_op Some (case_sum buf buf) (Choice {|Write (Write \<C> (Inr p) x) (Inl p) x, Write (Write \<C> (Inl p) x) (Inr p) x|}) \<Q>) \<and> op2 = id_op (BENQ p x buf))
  \<or> (\<exists>buf p. buf p \<noteq> [] \<and> op1 = map_op projl projr (comp_op Some (case_sum (BTL p buf) buf) \<C> (Read (Inr p) (\<lambda>x. if x = BHD p buf then Write \<Q> p x else Silent \<Q>))) \<and> op2 = id_op buf)
  \<or> (\<exists>buf p. buf p \<noteq> [] \<and> op1 = map_op projl projr (comp_op Some (case_sum buf (BTL p buf)) \<C> (Read (Inl p) (\<lambda>x. if x = BHD p buf then Write \<Q> p x else Silent \<Q>))) \<and> op2 = id_op buf)
  \<or> (\<exists>buf p x. op1 = map_op projl projr (comp_op Some (case_sum (BENQ p x buf) buf) (Write \<C> (Inr p) x) \<Q>) \<and> op2 = id_op (BENQ p x buf))
  \<or> (\<exists>buf p x. op1 = map_op projl projr (comp_op Some (case_sum buf (BENQ p x buf)) (Write \<C> (Inl p) x) \<Q>) \<and> op2 = id_op (BENQ p x buf))\<close>])
  unfolding wsim_def
  apply auto
  subgoal for buf
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    subgoal for p x
      apply (erule step_acopy_op_Inp)
       apply simp
      apply (rule exI[of _ \<open>id_op (BENQ p x buf)\<close>])
      apply (rule conjI)
       apply blast
      apply (rule wbc_base)
      apply fast
      done
        apply (meson no_step_aeq_op_Out no_step_acopy_op_Out)+
      apply (simp split: sum.splits)
    subgoal
      apply (erule step_aeq_op_Inp_L)
       apply simp
      apply (rule exI[of _ \<open>id_op buf\<close>])
      apply (rule conjI)
       apply blast
      apply (rule wbc_base)
      apply fast
      done
    subgoal
      apply (erule step_aeq_op_Inp_R)
       apply blast+
      done
     apply (meson no_step_acopy_op_Tau no_step_aeq_op_Tau)+
    done
  subgoal for buf
    apply (erule step_id_op_cases)
      apply auto
    subgoal for p x
      apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BENQ p x buf) (BENQ p x buf)) \<C> \<Q>)\<close>])
      apply (rule conjI[rotated])
       apply (rule wbc_sym)
       apply auto
      apply (rule step_io_step_tau_tau_wstep)
        apply fastforce+
      done
    subgoal for p
      apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf) (BTL p buf)) \<C> \<Q>)\<close>])
      apply (rule conjI[rotated])
       apply (rule wbc_sym)
       apply auto
      apply (rule step_tau_step_tau_step_io_wstep)
        apply fastforce+
      done
    done
  subgoal for buf p x
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
        apply (meson no_step_aeq_op_Out)
       apply blast
      apply blast
    apply (simp split: sum.splits)
  oops

lemma
  \<open>buf p \<noteq> [] \<Longrightarrow>
  comp_op Some (case_sum (BTL p buf) buf) \<C> (Read (Inr p) (\<lambda>x. if x = BHD p buf then Write \<Q> p x else Silent \<Q>))
  \<greatersim> comp_op Some (case_sum buf buf) \<C> \<Q>\<close>
  apply (coinduction arbitrary: buf p rule: expand.coinduct)
  unfolding wsim_def expansion_def
  subgoal for buf p
    apply auto
    subgoal
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p' x
        apply (erule step_acopy_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>comp_op Some (case_sum (BTL p buf) buf) (Choice {|Write (Write \<C> (Inr p') x) (Inl p') x, Write (Write \<C> (Inl p') x) (Inr p') x|}) (Read (Inr p) (\<lambda>x. if x = BHD p buf then Write \<Q> p x else Silent \<Q>))\<close>])
        apply (rule conjI)
         apply (rule step_io_step_tau_wstep)
          apply fast+
        apply (rule disjI2)
        apply (simp add: expand_refl)
        done
        apply (meson no_step_acopy_op_Out)
      subgoal
        apply (rule exI[of _ \<open>comp_op Some (case_sum (BTL p buf) (BTL p buf)) \<C> (Write \<Q> p (BHD p buf))\<close>])
        apply (rule conjI)
         apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply blast
        using step_tau_comp_op_Inl_case_sum[of p \<open>BHD p buf\<close> \<open>Read (Inl p) (\<lambda>x. if x = BHD p buf then Write \<Q> p x else Silent \<Q>)\<close> \<open>Write \<Q> p (BHD p buf)\<close> buf \<open>BTL p buf\<close> \<C>]
         apply (smt (verit, ccfv_SIG) SR)
        apply (rule disjI2)
        apply (rule expand_refl)
        done
      apply (meson no_step_acopy_op_Tau)
      done
    subgoal
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p' x
        apply (erule step_acopy_op_Inp)
        apply simp
  oops


lemma acopy_op_aeq_op_id_op_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf buf) \<C> \<Q>) \<approx> id_op buf\<close>
  oops

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