theory B8

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B8\<close>
lemma B8_gen:
  \<open> (transp_op (case_sum buf A) :: ('a :: {countable,defaults} + 0, 0 + 'a, 'b) op) ~ map_op id (case_sum Inr Inl) (id_op (case_sum buf A))\<close>
proof (coinduction arbitrary: buf rule: bisim_coinduct)
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. step (Inp p x) (map_op id (case_sum Inr Inl) (id_op (case_sum buf A))) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>buf. op1xx = transp_op (case_sum buf A) \<and> op2xx = map_op id (case_sum Inr Inl) (id_op (case_sum buf A))) (transp_op (BENQ p x (case_sum buf A))) op2'"
      if "p \<notin> defaults"
      for p :: "'a + 0"
        and x :: 'b
      using that 
    proof (cases p)
      case (Inl a)
      from this that show ?thesis 
       apply (intro exI conjI[rotated,OF b_base])
       apply (intro conjI)
      apply simp
      apply (rule refl)+
        apply force
        done
    next
      case (Inr b)
      from this that show ?thesis 
        by force
    qed
    moreover have "\<exists>op2'. step (Out (Inr x2) (BHD x2 buf)) (map_op id (case_sum Inr Inl) (id_op (case_sum buf A))) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>buf. op1xx = transp_op (case_sum buf A) \<and> op2xx = map_op id (case_sum Inr Inl) (id_op (case_sum buf A))) (transp_op (case_sum (BTL x2 buf) A)) op2'"
      if "x2 \<notin> defaults"
        and "buf x2 \<noteq> []"
      for x2 :: 'a
      using that 
       apply (intro exI conjI[rotated,OF b_base])
       apply (intro conjI)
      apply simp
      apply (rule refl)+
        apply force
      done
    ultimately show ?thesis
      using SIM1 by (auto 0 0 del: disjCI elim !: step_transp_op_cases step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
  qed
next
  case SIM2
  then show ?case 
  proof -
    have "\<exists>op2'. step (Inp p x) (transp_op (case_sum buf A)) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>buf. op1xx = transp_op (case_sum buf A) \<and> op2xx = map_op id (case_sum Inr Inl) (id_op (case_sum buf A))) op2' (map_op id (case_sum Inr Inl) (id_op (BENQ p x (case_sum buf A))))"
      if "p \<notin> defaults"
      for p :: "'a + 0"
        and x :: 'b
     using that 
    proof (cases p)
      case (Inl a)
      from this that show ?thesis 
       apply (intro exI conjI[rotated,OF b_base])
       apply (intro conjI)
          apply simp
        apply simp
        apply force
        done
    next
      case (Inr b)
      from this that show ?thesis 
        by force
    qed
    moreover have "\<exists>op2'. step (Out (Inr x1) (BHD x1 buf)) (transp_op (case_sum buf A)) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>buf. op1xx = transp_op (case_sum buf A) \<and> op2xx = map_op id (case_sum Inr Inl) (id_op (case_sum buf A))) op2' (map_op id (case_sum Inr Inl) (id_op (case_sum (BTL x1 buf) A)))"
      if "x1 \<notin> defaults"
        and "buf x1 \<noteq> []"
      for x1 :: 'a
      using that 
       apply (intro exI conjI[rotated,OF b_base])
       apply (intro conjI)
      apply simp
      apply (rule refl)+
        apply force
      done
    ultimately show ?thesis
      using SIM2 by (auto 0 0 del: disjCI elim !: step_id_op_cases step_map_op_elim split: if_splits sum.splits)
  qed
qed

lemma B8:
  \<open>(\<X> :: ('a :: {countable,defaults} + 0, 0 + 'a, 'b) op) ~ map_op id (case_sum Inr Inl) \<I>\<close>
  using B8_gen[of "\<lambda> _. []" "\<lambda> _. []", simplified] by simp


end