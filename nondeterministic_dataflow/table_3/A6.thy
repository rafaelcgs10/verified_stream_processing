theory A6

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A6: Split to transpose\<close>

lemma A6_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))
  \<approx> map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'a + 'a, 'b) IO"
      and op1' :: "('a, 'a + 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op1'"
    show "\<exists>op2'. wstep io (map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp pa xa) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum (BENQ pa xa buf1) buf1')) (transp_op (case_sum buf3 buf3')))) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'b
        using that by (fastforce del: wbc_base intro!: wbc_base wstep_map_op[of \<open>Inp pa xa\<close>])
      moreover have "\<exists>op2'. wstep (Inp pa xa) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 (BENQ pa xa buf1'))) (transp_op (case_sum buf3 buf3')))) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'b
        using that by (fastforce del: wbc_base intro!: wbc_base wstep_map_op[of \<open>Inp pa xa\<close>])
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BTL x1 buf3'))))) op2'"
        if "x1 \<notin> defaults"
          and "buf3' x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base wstep_map_op[of \<open>Out (Inr x1) (BHD x1 buf3')\<close>])
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3)) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum (BTL x2 buf3) buf3')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3 x2 \<noteq> []"
        for x2 :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base wstep_map_op[of \<open>Out (Inl x2) (BHD x2 buf3)\<close>])
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (split_op (case_sum (BTL x1 buf1) buf1')) (transp_op (case_sum buf3 buf3')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1 x1 \<noteq> []"
        for x1 :: 'a
        using that by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1') buf2')) (split_op (case_sum buf1 (BTL x2 buf1'))) (transp_op (case_sum buf3 buf3')))) op2'"
        if "x2 \<notin> defaults"
          and "buf1' x2 \<noteq> []"
        for x2 :: 'a
        using that by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3')))) op2'"
        if "x1 \<notin> defaults"
          and "buf2 x1 \<noteq> []"
        for x1 :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2')) (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BENQ x2 (BHD x2 buf2') buf3'))))) op2'"
        if "x2 \<notin> defaults"
          and "buf2' x2 \<noteq> []"
        for x2 :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_split_op_cases step_transp_op_cases split: sum.splits)
    qed
  next
    fix io :: "('a, 'a + 'a, 'b) IO"
      and op1' :: "('a, 'a + 'a, 'b) op"
    assume H: "step io (map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((BENQ p x buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that by force
      moreover have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((BENQ p x buf1' >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that by (fastforce intro!: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inr x1a) (BHD x1a buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((BTL x1a buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "buf1 x1a \<noteq> []"
          and "x1a \<notin> defaults"
          and "buf2 x1a = []"
          and "buf3 x1a = []"
        for x1a :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum (BENQ x1a (BHD x1a buf1) buf2) buf2')
    (split_op (case_sum (BTL x1a buf1) buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        also have \<open>step Tau \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum (BTL x1a buf1) buf1')) (transp_op (case_sum (BENQ x1a (BHD x1a buf1) buf3) buf3'))))\<close>
          using that by auto
        also have \<open>step (Out (Inr x1a) (BHD x1a buf1)) \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum (BTL x1a buf1) buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inr x1a)) (BHD x1a buf1)\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x1a) (BHD x1a buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> BTL x1a buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "x1a \<notin> defaults"
          and "buf2 x1a \<noteq> []"
          and "buf3 x1a = []"
        for x1a :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum (BTL x1a buf2) buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum (BENQ x1a (BHD x1a buf2) buf3) buf3'))))\<close>
          using that by auto
        also have \<open>step (Out (Inr x1a) (BHD x1a buf2)) \<dots>
    (map_op projl projr (comp_op Some (case_sum (BTL x1a buf2) buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inr x1a)) (BHD x1a buf2)\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x1a) (BHD x1a buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> BTL x1a buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "x1a \<notin> defaults"
          and "buf2 x1a = []"
          and "buf3 x1a \<noteq> []"
        for x1a :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], (force del: step_wstep intro!: step_wstep)+)
      moreover have "\<exists>op2'. wstep (Out (Inr x1a) (BHD x1a buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> BTL x1a buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "x1a \<notin> defaults"
          and "buf2 x1a \<noteq> []"
          and "buf3 x1a \<noteq> []"
        for x1a :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], (force del: step_wstep intro!: step_wstep)+)
      moreover have "\<exists>op2'. wstep (Out (Inl x2a) (BHD x2a buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2a buf1' >> buf2') >> buf3')))) op2'"
        if "buf1' x2a \<noteq> []"
          and "x2a \<notin> defaults"
          and "buf2' x2a = []"
          and "buf3' x2a = []"
        for x2a :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2a (BHD x2a buf1') buf2'))
    (split_op (case_sum buf1 (BTL x2a buf1'))) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        also have \<open>step Tau \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 (BTL x2a buf1'))) (transp_op (case_sum buf3 (BENQ x2a (BHD x2a buf1') buf3')))))\<close>
          using that by auto
        also have \<open>step (Out (Inl x2a) (BHD x2a buf1')) \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 (BTL x2a buf1'))) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inl x2a)) (BHD x2a buf1')\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x2a) (BHD x2a buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2a buf2') >> buf3')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2' x2a \<noteq> []"
          and "buf3' x2a = []"
        for x2a :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2a buf2'))
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BENQ x2a (BHD x2a buf2') buf3')))))\<close>
          using that by auto
        also have \<open>step (Out (Inl x2a) (BHD x2a buf2')) \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2a buf2'))
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inl x2a)) (BHD x2a buf2')\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x2a) (BHD x2a buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> BTL x2a buf3')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2' x2a = []"
          and "buf3' x2a \<noteq> []"
        for x2a :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], (force del: step_wstep intro!: step_wstep)+)
      moreover have "\<exists>op2'. wstep (Out (Inl x2a) (BHD x2a buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> BTL x2a buf3')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2' x2a \<noteq> []"
          and "buf3' x2a \<noteq> []"
        for x2a :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], (force del: step_wstep intro!: step_wstep)+)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_split_op_cases split: sum.splits if_splits)
    qed
  qed
qed

lemma A6:
  \<open>\<Lambda> \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<Lambda>\<close>
  unfolding scomp_op_def
  using A6_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end