theory R5

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom R5\<close>
lemma R5:
  fixes op :: "('a :: {countable, defaults} + 0, 'b :: {countable, defaults} + 0, 'c) op"
  assumes "Inr -` inputs op = {}"
    and "Inr -` outputs op = {}"
  shows "map_op Inl Inl (op\<up>) \<approx> op"
  unfolding feedback_op_def using assms
proof (coinduction arbitrary: op rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp (Inl (projl p)) x) op op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. op1xx = map_op Inl Inl (map_op projl projl (loop_op (\<lambda>_. None) (case_sum undefined (\<lambda>_. [])) op2xx)) \<and> Inr -` inputs op2xx = {} \<and> Inr -` outputs op2xx = {}) (map_op Inl Inl (map_op projl projl (loop_op (\<lambda>_. None) (case_sum undefined (\<lambda>_. [])) op''b))) op2'"
      if "Inr -` inputs op = {}"
        and "Inr -` outputs op = {}"
        and "step (Inp p x) op op''b"
      for p :: "'a + 0"
        and x :: 'c
        and op''b :: "('a + 0, 'b + 0, 'c) op"
      using that 
    proof (cases p)
      case (Inl a)
      from this that show ?thesis 
        apply -
        apply (intro conjI[rotated] wbc_base exI)
           defer
           defer
           apply blast
          apply force
         apply (metis bot.extremum_uniqueI step_inputs_outputs vimage_mono)+
        done
    next
      case (Inr b)
      from this that show ?thesis 
        by (metis ex_in_conv step_Inp_inputs vimageI2)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl (projl p)) x) op op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. op1xx = map_op Inl Inl (map_op projl projl (loop_op (\<lambda>_. None) (case_sum undefined (\<lambda>_. [])) op2xx)) \<and> Inr -` inputs op2xx = {} \<and> Inr -` outputs op2xx = {}) (map_op Inl Inl (map_op projl projl (loop_op (\<lambda>_. None) (case_sum undefined (\<lambda>_. [])) op''b))) op2'"
      if "Inr -` inputs op = {}"
        and "Inr -` outputs op = {}"
        and "step (Out p x) op op''b"
      for p :: "'b + 0"
        and x :: 'c
        and op''b :: "('a + 0, 'b + 0, 'c) op"
      using that 
    proof (cases p)
      case (Inl a)
      from this that show ?thesis 
        apply -
        apply (intro conjI[rotated] wbc_base exI)
           defer
           defer
           apply blast
          apply force
         apply (metis bot.extremum_uniqueI step_inputs_outputs vimage_mono)+
        done
    next
      case (Inr b)
      from this that show ?thesis 
        by (smt (verit, del_insts) bot.extremum_uniqueI equals0D step_Out_outputs step_inputs_outputs step_wstep sum.exhaust_sel that(1) that(2) that(3) vimageI2 vimage_mono wbc_base)
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* op op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. op1xx = map_op Inl Inl (map_op projl projl (loop_op (\<lambda>_. None) (case_sum undefined (\<lambda>_. [])) op2xx)) \<and> Inr -` inputs op2xx = {} \<and> Inr -` outputs op2xx = {}) (map_op Inl Inl (map_op projl projl (loop_op (\<lambda>_. None) (case_sum undefined (\<lambda>_. [])) op''b))) op2'"
      if "Inr -` inputs op = {}"
        and "Inr -` outputs op = {}"
        and "step Tau op op''b"
      for op''b :: "('a + 0, 'b + 0, 'c) op"
      using that 
      apply -
      apply -
      apply (intro conjI[rotated] wbc_base exI)
         defer
         defer
         apply blast
        apply force
       apply (metis bot.extremum_uniqueI step_inputs_outputs vimage_mono)+
      done
    ultimately show ?thesis
      using SIM1  by (auto elim !: step_map_op_elim step_loop_op_elim)
  qed
next
  case SIM2
  then show ?case 
  proof -
    have "\<exists>op2'. wstep io (map_op Inl Inl (map_op projl projl (loop_op (\<lambda>_. None) (case_sum undefined (\<lambda>_. [])) op))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. op1xx = map_op Inl Inl (map_op projl projl (loop_op (\<lambda>_. None) (case_sum undefined (\<lambda>_. [])) op2xx)) \<and> Inr -` inputs op2xx = {} \<and> Inr -` outputs op2xx = {}) op2' op1'"
      if "Inr -` inputs op = {}"
        and "Inr -` outputs op = {}"
        and "step io op op1'"
      using that 
    proof (cases io)
      case (Inp x11 x12)
      from this that show ?thesis 
        apply -
        apply (intro conjI[rotated] wbc_base exI)
           defer
           defer
           apply blast
          apply (rule step_wstep)
          apply (rule step_map_op)+
            apply auto[1]
           apply simp_all
          apply (metis IO.simps(15) empty_iff id_apply step_Inp_inputs sum.exhaust_sel vimageI)
         apply (metis bot.extremum_uniqueI step_inputs_outputs vimage_mono)+
        done
    next
      case (Out x21 x22)
      from this that show ?thesis 
        apply -
        apply (intro conjI[rotated] wbc_base exI)
           defer
           defer
           apply blast
          apply (rule step_wstep)
          apply (rule step_map_op)+
            apply auto[1]
           apply simp_all
          apply (metis IO.simps(16) empty_iff id_apply step_Out_outputs sum.exhaust_sel vimageI)      
         apply (metis bot.extremum_uniqueI step_inputs_outputs vimage_mono)+
        done
    next
      case Tau
      from this that show ?thesis 
        apply -
        apply (intro conjI[rotated] wbc_base exI)
           defer
           defer
           apply blast
          apply (rule step_wstep)
          apply (rule step_map_op)+
            apply auto[1]
           apply simp_all
         apply (metis bot.extremum_uniqueI step_inputs_outputs vimage_mono)+
        done
    qed
    then show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_loop_op_elim)
  qed
qed

end