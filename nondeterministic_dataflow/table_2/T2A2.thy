theory T2A2

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A2: Equality test transpose is equality test\<close>

lemma A2_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3')))
  \<approx> (aeq_op (case_sum (buf1 >> buf2' >> buf3') (buf1' >> buf2 >> buf3)))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (BENQ pa xa (case_sum buf1 buf1'))) (aeq_op (case_sum buf3 buf3')))) op2'"
      if "pa \<notin> defaults"
      for pa :: "'a + 'a"
        and xa :: "'b option"
      using that by (cases pa; fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3')) (aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
      if "buf3 pa \<noteq> []"
        and "buf3' pa \<noteq> []"
        and "pa \<notin> defaults"
        and "BHD pa buf3 = BHD pa buf3'"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out pa None) (aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
      if "buf3 pa \<noteq> []"
        and "buf3' pa \<noteq> []"
        and "pa \<notin> defaults"
        and "BHD pa buf3 \<noteq> BHD pa buf3'"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL x1 buf1'))) (aeq_op (case_sum buf3 buf3')))) op2'"
      if "x1 \<notin> defaults"
        and "buf1' x1 \<noteq> []"
      for x1 :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1) buf2')) (transp_op (case_sum (BTL x2 buf1) buf1')) (aeq_op (case_sum buf3 buf3')))) op2'"
      if "x2 \<notin> defaults"
        and "buf1 x2 \<noteq> []"
      for x2 :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum (BENQ pa (BHD pa buf2) buf3) buf3')))) op2'"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      by (intro exI conjI[rotated, OF wbc_base], blast, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa buf2')) (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 (BENQ pa (BHD pa buf2') buf3'))))) op2'"
      if "buf2' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      by (intro exI conjI[rotated, OF wbc_base], blast, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_transp_op_cases step_aeq_op_elim split: sum.splits)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inl p) y) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((BENQ p y buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)))"
      if "p \<notin> defaults"
      for p :: 'a
        and y :: "'b option"
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp (Inr p) y) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((BENQ p y buf1' >> buf2) >> buf3)))"
      if "p \<notin> defaults"
      for p :: 'a
        and y :: "'b option"
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((BTL p buf1 >> buf2') >> buf3') ((BTL p buf1' >> buf2) >> buf3)))"
      if "buf1 p \<noteq> []"
        and "buf1' p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf1 = BHD p buf1'"
        and "buf3 p = []"
        and "buf3' p = []"
        and "buf2 p = []"
        and "buf2' p = []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf1')) \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> BTL p buf2') >> buf3') ((BTL p buf1' >> buf2) >> buf3)))"
      if "buf1' p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf2' = BHD p buf1'"
        and "buf3 p = []"
        and "buf3' p = []"
        and "buf2 p = []"
        and "buf2' p \<noteq> []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf1')) \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((BTL p buf1 >> buf2') >> buf3') ((buf1' >> BTL p buf2) >> buf3)))"
      if "buf1 p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf1 = BHD p buf2"
        and "buf3 p = []"
        and "buf3' p = []"
        and "buf2 p \<noteq> []"
        and "buf2' p = []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum (BTL p buf2) (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf2)) \<dots> (map_op projl projr
     (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> BTL p buf2') >> buf3') ((buf1' >> BTL p buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "BHD p buf2' = BHD p buf2"
        and "buf3 p = []"
        and "buf3' p = []"
        and "buf2 p \<noteq> []"
        and "buf2' p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> buf2') >> BTL p buf3') ((BTL p buf1' >> buf2) >> buf3)))"
      if "buf1' p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf3' = BHD p buf1'"
        and "buf3 p = []"
        and "buf3' p \<noteq> []"
        and "buf2 p = []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf1')) \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> buf2') >> BTL p buf3') ((buf1' >> BTL p buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "BHD p buf3' = BHD p buf2"
        and "buf3 p = []"
        and "buf3' p \<noteq> []"
        and "buf2 p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((BTL p buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> BTL p buf3)))"
      if "buf1 p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf1 = BHD p buf3"
        and "buf3 p \<noteq> []"
        and "buf3' p = []"
        and "buf2' p = []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf3)) \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum (BTL p buf3) buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> BTL p buf2') >> buf3') ((buf1' >> buf2) >> BTL p buf3)))"
      if "p \<notin> defaults"
        and "BHD p buf2' = BHD p buf3"
        and "buf3 p \<noteq> []"
        and "buf3' p = []"
        and "buf2' p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> buf2') >> BTL p buf3') ((buf1' >> buf2) >> BTL p buf3)))"
      if "p \<notin> defaults"
        and "BHD p buf3' = BHD p buf3"
        and "buf3 p \<noteq> []"
        and "buf3' p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((BTL p buf1 >> buf2') >> buf3') ((BTL p buf1' >> buf2) >> buf3)))"
      if "buf1 p \<noteq> []"
        and "buf1' p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf1 \<noteq> BHD p buf1'"
        and "buf3 p = []"
        and "buf3' p = []"
        and "buf2 p = []"
        and "buf2' p = []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p None) \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> BTL p buf2') >> buf3') ((BTL p buf1' >> buf2) >> buf3)))"
      if "buf1' p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf2' \<noteq> BHD p buf1'"
        and "buf3 p = []"
        and "buf3' p = []"
        and "buf2 p = []"
        and "buf2' p \<noteq> []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p None) \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((BTL p buf1 >> buf2') >> buf3') ((buf1' >> BTL p buf2) >> buf3)))"
      if "buf1 p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf1 \<noteq> BHD p buf2"
        and "buf3 p = []"
        and "buf3' p = []"
        and "buf2 p \<noteq> []"
        and "buf2' p = []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum (BTL p buf2) (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p None) \<dots> (map_op projl projr
     (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> BTL p buf2') >> buf3') ((buf1' >> BTL p buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "BHD p buf2' \<noteq> BHD p buf2"
        and "buf3 p = []"
        and "buf3' p = []"
        and "buf2 p \<noteq> []"
        and "buf2' p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> buf2') >> BTL p buf3') ((BTL p buf1' >> buf2) >> buf3)))"
      if "buf1' p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf3' \<noteq> BHD p buf1'"
        and "buf3 p = []"
        and "buf3' p \<noteq> []"
        and "buf2 p = []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p None) \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
       (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> buf2') >> BTL p buf3') ((buf1' >> BTL p buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "BHD p buf3' \<noteq> BHD p buf2"
        and "buf3 p = []"
        and "buf3' p \<noteq> []"
        and "buf2 p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((BTL p buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> BTL p buf3)))"
      if "buf1 p \<noteq> []"
        and "p \<notin> defaults"
        and "BHD p buf1 \<noteq> BHD p buf3"
        and "buf3 p \<noteq> []"
        and "buf3' p = []"
        and "buf2' p = []"
      for p :: 'a
    proof -
      have \<open>step Tau (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
       (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
     (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 buf3'))))\<close>
        using that
        by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
      also have \<open>step Tau \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum buf3 (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p None) \<dots> (map_op projl projr
     (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) buf1'))
       (aeq_op (case_sum (BTL p buf3) buf3'))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> BTL p buf2') >> buf3') ((buf1' >> buf2) >> BTL p buf3)))"
      if "p \<notin> defaults"
        and "BHD p buf2' \<noteq> BHD p buf3"
        and "buf3 p \<noteq> []"
        and "buf3' p = []"
        and "buf2' p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p None) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = aeq_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (aeq_op (case_sum ((buf1 >> buf2') >> BTL p buf3') ((buf1' >> buf2) >> BTL p buf3)))"
      if "p \<notin> defaults"
        and "BHD p buf3' \<noteq> BHD p buf3"
        and "buf3 p \<noteq> []"
        and "buf3' p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM2 by (auto elim !: step_aeq_op_elim split: if_splits simp add: prems)
      done
  qed
qed

lemma A2:
  \<open>\<X> \<bullet> \<Q> \<approx> \<Q>\<close>
  unfolding scomp_op_def
  using A2_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end