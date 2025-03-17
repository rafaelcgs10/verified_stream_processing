theory A2

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A2: Merge transpose is merge\<close>

lemma A2_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum buf3 buf3')))
  \<approx> merge_op (case_sum (buf1 >> buf2' >> buf3') (buf1' >> buf2 >> buf3))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (BENQ pa xa (case_sum buf1 buf1'))) (merge_op (case_sum buf3 buf3')))) op2'"
      if "pa \<notin> defaults"
      for pa :: "'a + 'a"
        and xa :: 'b
    proof (cases pa)
      case (Inl a)
      from this that show ?thesis by (fastforce del: wbc_base intro: wbc_base)
    next
      case (Inr b)
      from this that show ?thesis by (fastforce del: wbc_base intro: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3)) (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum (BTL pa buf3) buf3')))) op2'"
      if "buf3 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3')) (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 (BTL pa buf3'))))) op2'"
      if "buf3' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL x1 buf1'))) (merge_op (case_sum buf3 buf3')))) op2'"
      if "x1 \<notin> defaults"
        and "buf1' x1 \<noteq> []"
      for x1 :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1) buf2')) (transp_op (case_sum (BTL x2 buf1) buf1')) (merge_op (case_sum buf3 buf3')))) op2'"
      if "x2 \<notin> defaults"
        and "buf1 x2 \<noteq> []"
      for x2 :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum (BENQ pa (BHD pa buf2) buf3) buf3')))) op2'"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa buf2')) (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 (BENQ pa (BHD pa buf2') buf3'))))) op2'"
      if "buf2' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_transp_op_cases step_merge_op_elim split: sum.splits)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inl p) x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (merge_op (case_sum ((BENQ p x buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)))"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'b
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp (Inr p) x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((BENQ p x buf1' >> buf2) >> buf3)))"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'b
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (merge_op (case_sum ((BTL p buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)))"
      if "buf1 p \<noteq> []"
        and "p \<notin> defaults"
        and "buf3' p = []"
        and "buf2' p = []"
      for p :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2'))
    (transp_op (case_sum (BTL p buf1) buf1'))
    (merge_op (case_sum buf3 buf3'))))\<close>
        using that by (auto del: step_Tau_comp_op_L intro!: step_Tau_comp_op_L split: sum.splits)
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum (BTL p buf1) buf1'))
    (merge_op (case_sum buf3 (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf1)) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum (BTL p buf1) buf1'))
    (merge_op (case_sum buf3 buf3'))))\<close>
        apply (rule step_map_op[of \<open>Out (Inr p) (BHD p buf1)\<close>])
        using that
        by (simp_all add: step_comp_op_R_Out step_merge_op_Write_R)
      ultimately show ?thesis
        by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans(1))
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (merge_op (case_sum ((buf1 >> BTL p buf2') >> buf3') ((buf1' >> buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "buf3' p = []"
        and "buf2' p \<noteq> []"
      for p :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum buf3 (BENQ p (BHD p buf2') buf3')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum buf3 buf3'))))\<close>
        apply (rule step_map_op[of \<open>Out (Inr p) (BHD p buf2')\<close>])
        using that
        by (simp_all add: step_comp_op_R_Out step_merge_op_Write_R)
      ultimately show ?thesis
        by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans_base(1))
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (merge_op (case_sum ((buf1 >> buf2') >> BTL p buf3') ((buf1' >> buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "buf3' p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((BTL p buf1' >> buf2) >> buf3)))"
      if "buf1' p \<noteq> []"
        and "p \<notin> defaults"
        and "buf3 p = []"
        and "buf2 p = []"
      for p :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2')
    (transp_op (case_sum buf1 (BTL p buf1')))
    (merge_op (case_sum buf3 buf3'))))\<close>
        using that by (auto split: sum.splits)
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 (BTL p buf1')))
    (merge_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 (BTL p buf1')))
    (merge_op (case_sum buf3 buf3'))))\<close>
        apply (rule step_map_op[of \<open>Out (Inr p) (BHD p buf1')\<close>])
        using that
        by (simp_all add: step_comp_op_R_Out step_merge_op_Write_L)
      ultimately show ?thesis
        by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans(1))
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> BTL p buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "buf3 p = []"
        and "buf2 p \<noteq> []"
      for p :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf2)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (transp_op (case_sum buf1 buf1'))
    (merge_op (case_sum buf3 buf3'))))\<close>
        apply (rule step_map_op[of \<open>Out (Inr p) (BHD p buf2)\<close>])
        using that
        by (simp_all add: step_comp_op_R_Out step_merge_op_Write_L)
      ultimately show ?thesis
        by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans_base(1))
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3'))) \<and> op2 = merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' (merge_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> BTL p buf3)))"
      if "p \<notin> defaults"
        and "buf3 p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_merge_op_elim split: if_splits)
  qed
qed

lemma A2:
  \<open>\<X> \<bullet> \<V> \<approx> \<V>\<close>
  unfolding scomp_op_def
  using A2_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end