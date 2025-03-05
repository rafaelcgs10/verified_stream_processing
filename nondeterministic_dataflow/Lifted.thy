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

abbreviation "\<Q>' \<equiv> \<Q>\<turnstile>"

lemma scomp_op_id_left_absorb_gen:
  assumes "inputs op2 \<inter> defaults = {}"
  shows  "map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<approx> map_op projl projr (comp_op Some (buf1 >> buf2 >> buf3) op1 op2)"
  using assms proof (coinduction arbitrary: op1 op2 buf1 buf2 buf3 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
    explore (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1'a (id_op buf2))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Inp p x) op1 op1'a"
      for p :: 'd
        and x :: 'c
        and op1'a :: "('d, 'a, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         apply blast+
      done
    moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2')) op2'a"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Out p x) op2 op2'"
      for p :: 'b
        and x :: 'c
        and op2' :: "('a, 'b, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply blast
      apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some (BENQ q (BHD q buf2) buf3) (map_op projl projr (comp_op Some buf1 op1 (id_op (BTL q buf2)))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "q \<notin> defaults"
        and "buf2 q \<noteq> []"
      for q :: 'a
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         apply assumption
        apply (rule refl)+
      apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      done  
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some (BTL p buf3) (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2')) op2'a"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Inp p (BHD p buf3)) op2 op2'"
        and "buf3 p \<noteq> []"
      for p :: 'a
        and op2' :: "('a, 'b, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce
      apply (metis disjoint_iff_not_equal step_inputs_outputs subset_eq)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some (BENQ q xa buf1) op1'a (id_op buf2))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Out q xa) op1 op1'a"
      for xa :: 'c
        and op1'a :: "('d, 'a, 'c) op"
        and q :: 'a
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some (BTL pb buf1) op1 (id_op (BENQ pb (BHD pb buf1) buf2)))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "buf1 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1'a (id_op buf2))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "step Tau op1 op1'a"
      for op1'a :: "('d, 'a, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce+
      done
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2')) op2'a"
      if "inputs op2 \<inter> defaults = {}"
        and "step Tau op2 op2'"
      for op2' :: "('a, 'b, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce+
      apply (metis disjoint_iff_not_equal step_inputs_outputs subset_eq)
      done
    ultimately show ?thesis
      using SIM1  by (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim!: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2' (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1' op2))"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Inp p x) op1 op1'"
      for p :: 'd
        and x :: 'c
        and op1' :: "('d, 'a, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         apply blast+
      done
    moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2'))"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Out p x) op2 op2'"
      for p :: 'b
        and x :: 'c
        and op2' :: "('a, 'b, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         prefer 2
         apply (rule refl)
        apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
       apply (rule refl)
      apply fast
      done    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2' (map_op projl projr (comp_op Some ((BENQ q x buf1 >> buf2) >> buf3) op1' op2))"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Out q x) op1 op1'"
      for x :: 'c
        and op1' :: "('d, 'a, 'c) op"
        and q :: 'a
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         apply assumption+
        apply (rule refl)+
      apply fast
      done
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((BTL p buf1 >> buf2) >> buf3) op1 op2'))"
      if "step (Inp p (BHD p buf1)) op2 op2'"
        and "buf1 p \<noteq> []"
        and "inputs op2 \<inter> defaults = {}"
        and "buf3 p = []"
        and "buf2 p = []"
      for p :: 'a
        and op2' :: "('a, 'b, 'c) op"
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2))
     (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some (BTL p buf1) op1 (id_op (BENQ p (BHD p buf1) buf2)))) op2))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Tau)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_id_op_Read)
                  apply simp_all
        apply (meson step_inputs_not_in_defaults)
        done
      also have "step Tau \<dots> 
                 (map_op projl projr (comp_op Some (BENQ p (BHD p buf1) buf3) (map_op projl projr (comp_op Some (BTL p buf1) op1 (id_op buf2))) op2))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                  apply simp_all
        apply (meson step_inputs_not_in_defaults)
        done
      also have "step Tau \<dots> 
                 (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some (BTL p buf1) op1 (id_op buf2))) op2'))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro exI conjI[rotated] wbc_base)
           prefer 2
           apply (rule refl)
          apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
         apply (rule refl)
        apply blast
        done
    qed
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((buf1 >> BTL p buf2) >> buf3) op1 op2'))"
      if "step (Inp p (BHD p buf2)) op2 op2'"
        and "inputs op2 \<inter> defaults = {}"
        and "buf3 p = []"
        and "buf2 p \<noteq> []"
      for p :: 'a
        and op2' :: "('a, 'b, 'c) op"
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2))
     (map_op projl projr (comp_op Some (BENQ p (BHD p buf2) buf3) (map_op projl projr (comp_op Some buf1 op1 (id_op (BTL p buf2)))) op2))"
        using that by auto
      also have "step Tau \<dots>
                 (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op (BTL p buf2)))) op2'))"
        using that by auto
      finally show ?thesis 
        using that apply -
        apply (intro exI conjI[rotated] wbc_base)
           prefer 2
           apply (rule refl)
          apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
         apply (rule refl)
        apply blast
        done
    qed
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((buf1 >> buf2) >> BTL p buf3) op1 op2'))"
      if "step (Inp p (BHD p buf3)) op2 op2'"
        and "inputs op2 \<inter> defaults = {}"
        and "buf3 p \<noteq> []"
      for p :: 'a
        and op2' :: "('a, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
         prefer 2
         apply (rule refl)
        apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
       apply (rule refl)
      apply force
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2' (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1' op2))"
      if "inputs op2 \<inter> defaults = {}"
        and "step Tau op1 op1'"
      for op1' :: "('d, 'a, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
         prefer 3
         apply (rule refl)
        apply assumption+
       apply (rule refl)
      apply force
      done
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2'))"
      if "inputs op2 \<inter> defaults = {}"
        and "step Tau op2 op2'"
      for op2' :: "('a, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
         prefer 2
         apply (rule refl)
        apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
       apply (rule refl)
      apply force
      done
    ultimately show ?thesis
      using SIM2  by (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits)
  qed
qed

lemma aeq_op_reads:
  "sub_op (Read p f) (aeq_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>aeq_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) aeq_op_code, simp) 
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) aeq_op_code, simp; force) 
qed

lemma inputs_aeq_op[intro]:
  "inputs (aeq_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using aeq_op_reads by (metis inputs_sub_op_Read)

lemma aeq_op_writes:
  "sub_op (Write op p x) (aeq_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>aeq_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) aeq_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) aeq_op_code, simp)
qed

lemma outputs_aeq_op[intro]:
  "outputs (aeq_op buf) \<subseteq> UNIV - defaults"
 apply (intro subsetI)
  using aeq_op_writes by (metis outputs_sub_op_Write)

lemma acopy_op_reads:
  "sub_op (Read p f) (acopy_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>acopy_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) acopy_op_code, simp) 
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) acopy_op_code, simp; force) 
qed

lemma inputs_acopy_op[intro]:
  "inputs (acopy_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using acopy_op_reads by (metis inputs_sub_op_Read)

lemma acopy_op_writes:
  "sub_op (Write op p x) (acopy_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>acopy_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) acopy_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) acopy_op_code, simp)
qed

lemma outputs_acopy_op[intro]:
  "outputs (acopy_op buf) \<subseteq> UNIV - defaults"
 apply (intro subsetI)
  using acopy_op_writes by (metis outputs_sub_op_Write)

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
lemma inputs_id_op_alt[intro!]:
  "\<forall>x\<in>inputs (id_op buf). x \<notin> defaults"
  using inputs_id_op[unfolded subset_eq, simplified] by fast
lemma outputs_id_op[intro]:
  "outputs (id_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using id_op_writes by (metis outputs_sub_op_Write)
lemma outputs_id_op_alt[intro!]:
  "\<forall>x\<in>outputs (id_op buf). x \<notin> defaults"
  using outputs_id_op[unfolded subset_eq, simplified] by fast


lemma scomp_op_id_left_absorb:
  assumes "inputs op2 \<inter> defaults = {}"
  shows  "op1\<turnstile> \<bullet> op2 \<approx> op1 \<bullet> op2"
  unfolding scomp_op_def using assms scomp_op_id_left_absorb_gen[of op2  "\<lambda> _. []"  "\<lambda> _. []" op1  "\<lambda> _. []"] by force

lemma aux2:
  "map_op f id (op\<turnstile>) \<approx> (map_op f id op)\<turnstile>"
  sorry

lemma A10':
  "\<Q>' \<bullet> \<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q>' \<parallel> \<Q>')"
  apply (rule wbisim_trans[OF scomp_op_id_left_absorb A10])
  using inputs_acopy_op apply fastforce
  done

lemma aux3:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'\<turnstile>))"
  sorry

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
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> \<Q>'" using scomp_op_id_left_absorb by (smt (verit, ccfv_SIG) aux3 bisim_wbisim scomp_op_assoc scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  also have "\<dots> \<approx> (\<Q> \<parallel> \<I>) \<bullet> \<Q> \<bullet> \<I>"
    using bisim_wbisim scomp_op_assoc wbisim_sym by blast 
  also have "\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>) \<bullet> \<I>" using wbisim_refl wbisim_scomp_op_cong using Synchronous_Operators_Axioms.A1 bisim_wbisim by blast
  also have "\<dots> \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>')" using aux2 bisim_wbisim scomp_op_assoc wbisim_map_op wbisim_sym wbisim_trans by blast
  also have "\<dots>  \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>)\<turnstile> \<bullet> \<Q>')" using scomp_op_id_left_absorb wbisim_map_op wbisim_sym by (smt (verit, best) aux3 bisim_wbisim scomp_op_assoc scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_trans)
  also have "\<dots>  \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>) \<bullet> (\<I> \<parallel> \<I>) \<bullet> \<Q>')" by (metis bisim_wbisim pcomp_op_id_id wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have "\<dots>  \<approx> map_op (case_sum Inr Inl) id ((\<I>\<turnstile> \<parallel> \<Q>') \<bullet> \<Q>')" by (simp add: bisim_wbisim pcomp_op_scomp_distributes wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  also have "\<dots>  \<approx> map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>') \<bullet> \<Q>')" by (simp add: pcomp_op_def scomp_op_id_id wbisim_comp_op_cong wbisim_map_op wbisim_refl wbisim_scomp_op_cong)
  finally show ?thesis.
qed

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