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

lemma map_op_out_id_vdash_gen:
  "map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<approx> map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))"
proof (coinduction arbitrary: op buf1 buf2 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp (f p) x) (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some buf2 op1' (id_op buf1)))) op2'"
      if "step (Inp p x) op op1'"
      for p :: 'd
        and x :: 'c
        and op1' :: "('d, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf1)) (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op (BTL pa buf1))))) op2'"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some (BENQ q x buf2) op1' (id_op buf1)))) op2'"
      if "step (Out q x) op op1'"
      for x :: 'c
        and op1' :: "('d, 'b, 'c) op"
        and q :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some (BTL pa buf2) op (id_op (BENQ pa (BHD pa buf2) buf1))))) op2'"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some buf2 op1' (id_op buf1)))) op2'"
      if "step Tau op op1'"
      for op1' :: "('d, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some buf2 (map_op f id op''a) (id_op buf1)))"
      if "step io'a op op''a"
        and "map_IO f id id io'a = Inp p x"
      for p :: 'a
        and x :: 'c
        and io'a :: "('d, 'b, 'c) IO"
        and op''a :: "('d, 'b, 'c) op"
    proof (cases "io'a")
      case (Inp x11 x12)
      from this that show ?thesis 
        using that apply -
        apply hypsubst_thin
        apply (intro exI conjI[rotated] wbc_base)
          apply (rule refl)+
        apply fastforce
        done
    next
      case (Out x21 x22)
      from this that show ?thesis 
        using that apply -
        apply hypsubst_thin
        apply (intro exI conjI[rotated] wbc_base)
          apply (rule refl)+
        apply fastforce
        done
    next
      case Tau
      from this that show ?thesis 
        using that apply -
        apply hypsubst_thin
        apply (intro exI conjI[rotated] wbc_base)
          apply (rule refl)+
        apply fastforce
        done
    qed
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf1)) (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op (BTL pa buf1))))"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some (BENQ q x buf2) (map_op f id op''a) (id_op buf1)))"
      if "step io'a op op''a"
        and "map_IO f id id io'a = Out q x"
      for x :: 'c
        and q :: 'b
        and io'a :: "('d, 'b, 'c) IO"
        and op''a :: "('d, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply (rule refl)+
      apply (smt (z3) IO.exhaust IO.simps(15) IO.simps(16) IO.simps(17) IO.simps(4) id_def step_Tau_comp_op_L_alt step_star_map_op step_wstep wstep_steps_Tau)
      done     moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some (BTL pa buf2) (map_op f id op) (id_op (BENQ pa (BHD pa buf2) buf1))))"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some buf2 (map_op f id op''a) (id_op buf1)))"
      if "step Tau op op''a"
      for op''a :: "('d, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    ultimately show ?thesis
      using SIM2  by (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits)
  qed
qed

lemma map_op_out_id_vdash:
  "map_op f id (op\<turnstile>) \<approx> (map_op f id op)\<turnstile>"
  unfolding scomp_op_def using map_op_out_id_vdash_gen by force

lemma A10':
  "\<Q>' \<bullet> \<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q>' \<parallel> \<Q>')"
  apply (rule wbisim_trans[OF scomp_op_id_left_absorb A10])
  using inputs_acopy_op apply fastforce
  done

lemma aeq_id_absorb_gen:
  "aeq_op (case_sum (buf1L >> buf2L >> buf3L) (buf1R >> buf2R >> buf3R)) \<approx> map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R) ) (aeq_op (case_sum buf3L buf3R) ))"
proof (coinduction arbitrary: buf1L buf2L buf3L buf1R buf2R buf3R  rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
    explore (elim exE conjE disjE step_id_op_cases step_comp_op_elim step_map_op_elim step_aeq_op_elim; simp split: if_splits sum.splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp (Inl p) y) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BENQ p y buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and y :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Inp (Inr p) y) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((BENQ p y buf1R >> buf2R) >> buf3R))) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and y :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "buf1R p \<noteq> []"
        and "BHD p buf1L = BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p = []"
        and "buf2L p = []"
      for p :: 'a
        and x :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1R p \<noteq> []"
        and "BHD p buf2L = BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p = []"
        and "buf2L p \<noteq> []"
      for p :: 'a
        and x :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "BHD p buf1L = BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p \<noteq> []"
        and "buf2L p = []"
      for p :: 'a
        and x :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "BHD p buf2L = BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p \<noteq> []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1R p \<noteq> []"
        and "BHD p buf3L = BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p \<noteq> []"
        and "buf2R p = []"
      for p :: 'a
        and x :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "BHD p buf3L = BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p \<noteq> []"
        and "buf2R p \<noteq> []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "BHD p buf1L = BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p = []"
        and "buf2L p = []"
      for p :: 'a
        and x :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "BHD p buf2L = BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p = []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "BHD p buf3L = BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p \<noteq> []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "buf1R p \<noteq> []"
        and "BHD p buf1L \<noteq> BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p = []"
        and "buf2L p = []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1R p \<noteq> []"
        and "BHD p buf2L \<noteq> BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p = []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "BHD p buf1L \<noteq> BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p \<noteq> []"
        and "buf2L p = []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "BHD p buf2L \<noteq> BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p \<noteq> []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1R p \<noteq> []"
        and "BHD p buf3L \<noteq> BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p \<noteq> []"
        and "buf2R p = []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "BHD p buf3L \<noteq> BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p \<noteq> []"
        and "buf2R p \<noteq> []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "BHD p buf1L \<noteq> BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p = []"
        and "buf2L p = []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "BHD p buf2L \<noteq> BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p = []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "BHD p buf3L \<noteq> BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p \<noteq> []"
      for p :: 'a
      using that sorry
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM1 apply (elim exE conjE disjE step_id_op_cases step_comp_op_elim step_map_op_elim step_aeq_op_elim; simp split: if_splits sum.splits ; hypsubst_thin)
                           apply (rule prems; assumption)+
        done
      done
  qed
next
  case SIM2
  then show ?case 
   apply -
    explore (elim exE conjE disjE step_id_op_cases step_comp_op_elim step_map_op_elim step_aeq_op_elim; simp split: if_splits sum.splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp pa x) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (BENQ pa x (case_sum buf1L buf1R))) (aeq_op (case_sum buf3L buf3R))))"
      if "(pa::'a + 'a) \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, 'a + 'a, 'b) op"
        and pa :: "'a + 'a"
      using that sorry
    moreover have "\<exists>op2'. wstep (Inp (Inl pa) y) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BENQ pa y buf3L) buf3R))))"
      if "Out p x = Inp (Inl pa::'a + 'a) y"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: 'a
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
        and y :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Inp (Inr pa) y) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L (BENQ pa y buf3R)))))"
      if "Out p x = Inp (Inr pa::'a + 'a) y"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: 'a
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
        and y :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3R)) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BTL pa buf3L) (BTL pa buf3R)))))"
      if "(Out p x::('a + 'a, 'a, 'b) IO) = Out pa (BHD pa buf3R)"
        and "buf3L pa \<noteq> []"
        and "buf3R pa \<noteq> []"
        and "BHD pa buf3L = BHD pa buf3R"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: 'a
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
        and xa :: 'b
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1L) buf2L) buf2R) (id_op (case_sum (BTL x1 buf1L) buf1R)) (aeq_op (case_sum buf3L buf3R))))"
      if "(x1::'a) \<notin> defaults"
        and "buf1L x1 \<noteq> []"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, 'a + 'a, 'b) op"
        and q :: "'a + 'a"
        and pa :: "'a + 'a"
        and x1 :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L (BENQ x2 (BHD x2 buf1R) buf2R)) (id_op (case_sum buf1L (BTL x2 buf1R))) (aeq_op (case_sum buf3L buf3R))))"
      if "(x2::'a) \<notin> defaults"
        and "buf1R x2 \<noteq> []"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, 'a + 'a, 'b) op"
        and q :: "'a + 'a"
        and pa :: "'a + 'a"
        and x2 :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum (BTL pa buf2L) buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BENQ pa (BHD pa buf2L) buf3L) buf3R))))"
      if "buf2L pa \<noteq> []"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L (BTL pa buf2R)) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L (BENQ pa (BHD pa buf2R) buf3R)))))"
      if "buf2R pa \<noteq> []"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BTL pa buf3L) (BTL pa buf3R)))))"
      if "buf3L pa \<noteq> []"
        and "buf3R pa \<noteq> []"
        and "BHD pa buf3L \<noteq> BHD pa buf3R"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
      using that sorry
    ultimately show ?thesis
  apply -
      subgoal premises prems
        using SIM2 apply (elim exE conjE disjE step_id_op_cases step_comp_op_elim step_map_op_elim step_aeq_op_elim; simp split: if_splits sum.splits ; hypsubst_thin)
                           apply (rule prems; assumption)+
        done
      done
  qed
qed  

lemma aeq_id_absorb:
  "\<Q> \<approx> \<stileturn>\<Q>"
  unfolding scomp_op_def
  using aeq_id_absorb_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", simplified] by simp

lemma aeq_vdash_absorb:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'))"
  using aeq_id_absorb using bisim_wbisim scomp_op_assoc wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma aeq_double_vdash_absorb:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'\<turnstile>))"
  using aeq_vdash_absorb using scomp_op_id_op_right_neutral wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

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
  \<open>map_op projr id (\<exclamdown> \<parallel> \<I>) \<bullet> \<Q>' \<approx> ! \<bullet> \<exclamdown>\<close>
  oops

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
  \<open>map_op id Inr \<Q>' \<up> \<approx> !\<close>
  oops

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