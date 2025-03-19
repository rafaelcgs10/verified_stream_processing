theory A11

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A11: Acopy to equality test\<close>

lemma A11_gen:
  assumes \<open>buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3'\<close>
  shows \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3')))
  \<approx> id_op (buf1 >> buf2 >> buf3)\<close>
  using assms proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum (BENQ pa xa buf1) (BENQ pa xa buf1'))) (aeq_op (case_sum buf3 buf3')))) op2'"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "pa \<notin> defaults"
      for pa :: 'a
        and xa :: "'b option"
      using that
      by (intro exI conjI[rotated, OF wbc_base]; auto) (metis BAPPEND_BENQ)+
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3')) (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "buf3 pa \<noteq> []"
        and "buf3' pa \<noteq> []"
        and "pa \<notin> defaults"
        and "BHD pa buf3 = BHD pa buf3'"
      for pa :: 'a
      using that
      apply (intro exI conjI[rotated, OF wbc_base]; auto) 
       apply (metis BAPPEND_BTL)
      by (metis BAPPEND_BTL BHD_BULK_BENQ_right_not_empty BULK_BENQ_empty step_id_op_Write step_wstep)
    moreover have "\<exists>op2'. wstep (Out pa None) (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "buf3 pa \<noteq> []"
        and "buf3' pa \<noteq> []"
        and "pa \<notin> defaults"
        and "BHD pa buf3 \<noteq> BHD pa buf3'"
      for pa :: 'a
      using that
      by (intro exI conjI[rotated, OF wbc_base]; auto) (metis BHD_BULK_BENQ_right_not_empty)+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf1) buf2) buf2') (acopy_op (case_sum (BTL pa buf1) buf1')) (aeq_op (case_sum buf3 buf3')))) op2'"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "buf1 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa buf1') buf2')) (acopy_op (case_sum buf1 (BTL pa buf1'))) (aeq_op (case_sum buf3 buf3')))) op2'"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "buf1' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum (BENQ pa (BHD pa buf2) buf3) buf3')))) op2'"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      by (intro exI conjI[rotated, OF wbc_base]; auto) (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa buf2')) (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 (BENQ pa (BHD pa buf2') buf3'))))) op2'"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "buf2' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      by (intro exI conjI[rotated, OF wbc_base]; auto) (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_aeq_op_elim)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') op2' (id_op ((BENQ p x buf1' >> buf2') >> buf3'))"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "p \<notin> defaults"
      for p :: 'a
        and x :: "'b option"
      using that
      apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
  (acopy_op (case_sum (BENQ p x buf1) (BENQ p x buf1')))
  (aeq_op (case_sum buf3 buf3')))\<close>] conjI[rotated, OF wbc_base])
       apply (metis BAPPEND_BENQ BULK_BENQ_assoc)
      by fastforce
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') op2' (id_op ((BTL p buf1' >> buf2') >> buf3'))"
      if "buf1' p \<noteq> []"
        and "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "p \<notin> defaults"
        and "buf3' p = []"
        and "buf2' p = []"
      for p :: 'a
    proof (cases \<open>buf3 p \<noteq> []\<close>)
      case True
      hence \<open>BHD p buf1' = BHD p buf3\<close>
        using that
        by (metis BHD_BULK_BENQ_right_not_empty BHD_def BULK_BENQ_right_empty)
      thus ?thesis
        using that True
        apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
  (acopy_op (case_sum buf1 (BTL p buf1')))
  (aeq_op (case_sum (BTL p buf3) buf3')))\<close>] conjI[rotated, OF wbc_base])
         apply (metis BAPPEND_BTL)
        by fastforce
    next
      case False
      then show ?thesis
      proof (cases \<open>buf2 p \<noteq> []\<close>)
        case True
        hence BHD_eq: \<open>BHD p buf1' = BHD p buf2\<close>
          using that False
          by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1') buf2'))
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf1') buf3')))))\<close>
          using that by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf1') buf3')))))\<close>
          using that True by auto fastforce
        also have \<open>step (Out p (BHD p buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum buf3 buf3'))))\<close>
          using that True False BHD_eq by auto
        ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
  (acopy_op (case_sum buf1 (BTL p buf1')))
  (aeq_op (case_sum buf3 buf3')))\<close>] conjI[rotated, OF wbc_base])
          using that True False
           apply (metis BAPPEND_BTL)
          by (meson wstep_trans(1))
      next
        case False
        hence buf1_not_empty: \<open>buf1 p \<noteq> []\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close>
          by (metis BULK_BENQ_empty)
        hence BHD_eq: \<open>BHD p buf1' = BHD p buf1\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False
          by (metis BHD_BULK_BENQ_left_empty)
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1') buf2'))
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf1') buf3')))))\<close>
          using that by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1) buf2) buf2')
    (acopy_op (case_sum (BTL p buf1) (BTL p buf1')))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf1') buf3')))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum (BTL p buf1) (BTL p buf1')))
    (aeq_op (case_sum (BENQ p (BHD p buf1) buf3) (BENQ p (BHD p buf1') buf3')))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty by auto fastforce
        also have \<open>step (Out p (BHD p buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum (BTL p buf1) (BTL p buf1')))
    (aeq_op (case_sum buf3 buf3'))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty BHD_eq by auto
        ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
  (acopy_op (case_sum (BTL p buf1) (BTL p buf1')))
  (aeq_op (case_sum buf3 buf3')))\<close>] conjI[rotated, OF wbc_base])
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
           apply (metis (mono_tags, opaque_lifting) BAPPEND_BTL)
          by (meson wstep_trans(1))
      qed
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') op2' (id_op ((buf1' >> BTL p buf2') >> buf3'))"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "p \<notin> defaults"
        and "buf3' p = []"
        and "buf2' p \<noteq> []"
      for p :: 'a
    proof (cases \<open>buf3 p \<noteq> []\<close>)
      case True
      hence \<open>BHD p buf2' = BHD p buf3\<close>
        using that
        by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
      thus ?thesis
        using that True
        apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
  (acopy_op (case_sum buf1 buf1'))
  (aeq_op (case_sum (BTL p buf3) buf3')))\<close>] conjI[rotated, OF wbc_base])
         apply (metis BAPPEND_BTL)
        by fastforce
    next
      case False
      then show ?thesis
      proof (cases \<open>buf2 p \<noteq> []\<close>)
        case True
        hence BHD_eq: \<open>BHD p buf2' = BHD p buf2\<close>
          using that False
          by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) (BTL p buf2'))
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
          using that True by auto fastforce
        also have \<open>step (Out p (BHD p buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) (BTL p buf2'))
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3'))))\<close>
          using that True False BHD_eq by auto
        ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf2) (BTL p buf2'))
  (acopy_op (case_sum buf1 buf1'))
  (aeq_op (case_sum buf3 buf3')))\<close>] conjI[rotated, OF wbc_base])
          using that True False
           apply (metis BAPPEND_BTL)
          by (meson wstep_trans(1))
      next
        case False
        hence buf1_not_empty: \<open>buf1 p \<noteq> []\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close>
          by (metis BULK_BENQ_empty)
        hence BHD_eq: \<open>BHD p buf2' = BHD p buf1\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False
          by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1) buf2) (BTL p buf2'))
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf2') buf3')))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum (BENQ p (BHD p buf1) buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty by auto fastforce
        also have \<open>step (Out p (BHD p buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum buf3 buf3'))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty BHD_eq by auto
        ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
  (acopy_op (case_sum (BTL p buf1) buf1'))
  (aeq_op (case_sum buf3 buf3')))\<close>] conjI[rotated, OF wbc_base])
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
           apply (metis (mono_tags, opaque_lifting) BAPPEND_BTL)
          by (meson wstep_trans(1))
      qed
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') op2' (id_op ((buf1' >> buf2') >> BTL p buf3'))"
      if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
        and "p \<notin> defaults"
        and "buf3' p \<noteq> []"
      for p :: 'a
    proof (cases \<open>buf3 p \<noteq> []\<close>)
      case True
      hence \<open>BHD p buf3' = BHD p buf3\<close>
        using that by (metis BHD_BULK_BENQ_right_not_empty)
      thus ?thesis
        using that True
        apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
  (acopy_op (case_sum buf1 buf1'))
  (aeq_op (case_sum (BTL p buf3) (BTL p buf3'))))\<close>] conjI[rotated, OF wbc_base])
         apply (metis BAPPEND_BTL)
        by fastforce
    next
      case False
      then show ?thesis
      proof (cases \<open>buf2 p \<noteq> []\<close>)
        case True
        hence BHD_eq: \<open>BHD p buf3' = BHD p buf2\<close>
          using that False
          by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
          using that True by auto fastforce
        also have \<open>step (Out p (BHD p buf3')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
          using that True False BHD_eq by auto
        ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
  (acopy_op (case_sum buf1 buf1'))
  (aeq_op (case_sum buf3 (BTL p buf3'))))\<close>] conjI[rotated, OF wbc_base])
          using that True False
           apply (metis (mono_tags, opaque_lifting) BAPPEND_BTL)
          by (meson step_tau_step_io_wstep)
      next
        case False
        hence buf1_not_empty: \<open>buf1 p \<noteq> []\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close>
          by (metis BULK_BENQ_empty)
        hence BHD_eq: \<open>BHD p buf3' = BHD p buf1\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False
          by (metis BHD_BULK_BENQ_right_not_empty BHD_def BULK_BENQ_right_empty)
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1) buf2) buf2')
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum buf3 buf3'))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty by auto fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum (BENQ p (BHD p buf1) buf3) buf3'))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty by auto fastforce
        also have \<open>step (Out p (BHD p buf3')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty BHD_eq by auto
        ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
  (acopy_op (case_sum (BTL p buf1) buf1'))
  (aeq_op (case_sum buf3 (BTL p buf3'))))\<close>] conjI[rotated, OF wbc_base])
          using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
           apply (metis (mono_tags, opaque_lifting) BAPPEND_BTL)
          by (meson wstep_trans(1))
      qed
    qed
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_id_op_cases split: if_splits)
  qed
qed

lemma A11:
  \<open>\<C> \<bullet> \<Q> \<approx> \<I>\<close>
  unfolding scomp_op_def
  using A11_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end