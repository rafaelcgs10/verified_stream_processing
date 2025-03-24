theory T2A5

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A5: Acopy to acopy and identity\<close>

lemma A5_gen:
  assumes \<open>A1 >> A2 >> A3 = B1 >> B2 >> B3\<close>
    and \<open>A1 >> A2 >> A3' = B1' >> B2' >> B3'\<close>
    and \<open>A1' >> A2' >> A3'' = B1' >> B2' >> B3''\<close>
  shows \<open>map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (acopy_op (case_sum A3 A3') \<parallel> id_op A3''))
  \<approx> map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (id_op B3 \<parallel> acopy_op (case_sum B3' B3''))))\<close>
  unfolding pcomp_op_def
using assms proof (coinduction arbitrary: A1 A1' A2 A2' A3 A3' A3'' B1 B1' B2 B2' B3 B3' B3'' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3'')))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum (BENQ pa xa A1) (BENQ pa xa A1'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2'"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'b
      using that
      apply (intro exI conjI)
       apply force
      apply (rule wbc_base)
      by (metis BAPPEND_BENQ)
    moreover have "\<exists>op2'. wstep (Out (Inr pb) (BHD pb A3'')) (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3'')))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op (BTL pb A3''))))) op2'"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "pb \<notin> defaults"
        and "A3'' pb \<noteq> []"
      for pb :: 'a
    proof (cases \<open>B3'' pb \<noteq> []\<close>)
      case True
      then show ?thesis
      proof -
        have \<open>BHD pb B3'' = BHD pb A3''\<close>
          using that True
          by (metis BHD_BULK_BENQ_right_not_empty)
        hence \<open>wstep (Out (Inr pb) (BHD pb A3''))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' (BTL pb B3'')))))))\<close>
          using that True by fastforce
        thus ?thesis
          using that True
          apply (intro exI conjI)
           apply blast
          apply (rule wbc_base)
          by (metis BAPPEND_BTL)
      qed
    next
      case False
      then show ?thesis
      proof (cases \<open>B2' pb \<noteq> []\<close>)
        case True
        then show ?thesis
        proof -
          have H: \<open>BHD pb B2' = BHD pb A3''\<close>
            using that True False by (metis (full_types) BHD_BAPPEND_2_cases BULK_BENQ_empty)
          hence \<open>step Tau
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 (BTL pb B2'))
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BENQ pb (BHD pb A3'') B3') (BENQ pb (BHD pb A3'') B3'')))))))\<close>
            using that True False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inr pb) (BHD pb A3'')) \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 (BTL pb B2'))
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BENQ pb (BHD pb A3'') B3') B3''))))))\<close>
            using that True False by fastforce
          finally show ?thesis
            using that True False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (metis BAPPEND_BENQ_BHD BAPPEND_BTL BULK_BENQ_assoc)
        qed
      next
        case False
        then show ?thesis
        proof -
          have H: \<open>BHD pb B1' = BHD pb A3''\<close>
            using that \<open>\<not> B3'' pb \<noteq> []\<close> False
            by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
          hence \<open>step Tau
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 (BENQ pb (BHD pb A3'') B2'))
    (acopy_op (case_sum B1 (BTL pb B1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))\<close>
            using that \<open>\<not> B3'' pb \<noteq> []\<close> False
            apply auto[1]
            by (metis (no_types, lifting) BULK_BENQ_empty case_sum_BENQ_R case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_acopy_op_WriteR)
          also have \<open>step Tau \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 (BTL pb B1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BENQ pb (BHD pb A3'') B3') (BENQ pb (BHD pb A3'') B3'')))))))\<close>
            using that \<open>\<not> B3'' pb \<noteq> []\<close> False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inr pb) (BHD pb A3'')) \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 (BTL pb B1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BENQ pb (BHD pb A3'') B3') B3''))))))\<close>
            using that \<open>\<not> B3'' pb \<noteq> []\<close> False by fastforce
          finally show ?thesis
            using that \<open>\<not> B3'' pb \<noteq> []\<close> False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (smt (verit, ccfv_threshold) BAPPEND_BENQ_BHD BAPPEND_BTL BHD_BULK_BENQ_cases BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_right_empty False H that(2) that(3) that(5))
        qed
      qed
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl (Inl pb)) (BHD pb A3)) (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3'')))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BTL pb A3) A3')) (id_op A3'')))) op2'"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "A3 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
    proof (cases \<open>B3 pb \<noteq> []\<close>)
      case True
      then show ?thesis
      proof -
        have \<open>BHD pb B3 = BHD pb A3\<close>
          using that True
          by (metis BHD_BULK_BENQ_right_not_empty)
        hence \<open>wstep (Out (Inl (Inl pb)) (BHD pb A3))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pb B3)) (acopy_op (case_sum B3' B3''))))))\<close>
          using that True by fastforce
        thus ?thesis
          using that True
          apply (intro exI conjI)
           apply blast
          apply (rule wbc_base)
          by (metis BAPPEND_BTL)
      qed
    next
      case False
      then show ?thesis
      proof (cases \<open>B2 pb \<noteq> []\<close>)
        case True
        then show ?thesis
        proof -
          have H: \<open>BHD pb B2 = BHD pb A3\<close>
            using that True False by (metis (full_types) BHD_BAPPEND_2_cases BULK_BENQ_empty)
          hence \<open>step Tau
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum (BTL pb B2) B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pb (BHD pb A3) B3)) (acopy_op (case_sum B3' B3''))))))\<close>
            using that True False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inl (Inl pb)) (BHD pb A3)) \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum (BTL pb B2) B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))\<close>
            using that True False by fastforce
          finally show ?thesis
            using that True False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (metis BAPPEND_BTL)
        qed
      next
        case False
        then show ?thesis
        proof -
          have H: \<open>BHD pb B1 = BHD pb A3\<close>
            using that \<open>\<not> B3 pb \<noteq> []\<close> False
            by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
          hence \<open>step Tau
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb A3) B2) B2')
    (acopy_op (case_sum (BTL pb B1) B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))\<close>
            using that \<open>\<not> B3 pb \<noteq> []\<close> False
            apply auto[1]
            by (metis (no_types, lifting) BULK_BENQ_empty case_sum_BENQ_L case_sum_BHD_L case_sum_BTL_L step_Tau_comp_op_L step_acopy_op_WriteL sum.case(1))
          also have \<open>step Tau \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum (BTL pb B1) B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pb (BHD pb A3) B3)) (acopy_op (case_sum B3' B3''))))))\<close>
            using that \<open>\<not> B3 pb \<noteq> []\<close> False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inl (Inl pb)) (BHD pb A3)) \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum (BTL pb B1) B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))\<close>
            using that \<open>\<not> B3 pb \<noteq> []\<close> False by fastforce
          finally show ?thesis
            using that \<open>\<not> B3 pb \<noteq> []\<close> False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (smt (verit, ccfv_threshold) BAPPEND_BENQ_BHD BAPPEND_BTL BHD_BULK_BENQ_cases BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_right_empty False H that(2) that(3) that(5))
        qed
      qed
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl (Inr pb)) (BHD pb A3')) (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3'')))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 (BTL pb A3'))) (id_op A3'')))) op2'"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "A3' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
    proof (cases \<open>B3' pb \<noteq> []\<close>)
      case True
      then show ?thesis
      proof -
        have \<open>BHD pb B3' = BHD pb A3'\<close>
          using that True
          by (metis BHD_BULK_BENQ_right_not_empty)
        hence \<open>wstep (Out (Inl (Inr pb)) (BHD pb A3'))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BTL pb B3') B3''))))))\<close>
          using that True by fastforce
        thus ?thesis
          using that True
          apply (intro exI conjI)
           apply blast
          apply (rule wbc_base)
          by (metis BAPPEND_BTL)
      qed
    next
      case False
      then show ?thesis
      proof (cases \<open>B2' pb \<noteq> []\<close>)
        case True
        then show ?thesis
        proof -
          have H: \<open>BHD pb B2' = BHD pb A3'\<close>
            using that True False by (metis (full_types) BHD_BAPPEND_2_cases BULK_BENQ_empty)
          hence \<open>step Tau
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 (BTL pb B2'))
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BENQ pb (BHD pb A3') B3') (BENQ pb (BHD pb A3') B3'')))))))\<close>
            using that True False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inl (Inr pb)) (BHD pb A3')) \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 (BTL pb B2'))
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' (BENQ pb (BHD pb A3') B3'')))))))\<close>
            using that True False by fastforce
          finally show ?thesis
            using that True False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (metis BAPPEND_BENQ_BHD BAPPEND_BTL BULK_BENQ_assoc)
        qed
      next
        case False
        then show ?thesis
        proof -
          have H: \<open>BHD pb B1' = BHD pb A3'\<close>
            using that \<open>\<not> B3' pb \<noteq> []\<close> False
            by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
          hence \<open>step Tau
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 B1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 (BENQ pb (BHD pb A3') B2'))
    (acopy_op (case_sum B1 (BTL pb B1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))\<close>
            using that \<open>\<not> B3' pb \<noteq> []\<close> False
            apply auto[1]
            by (metis (mono_tags, lifting) BULK_BENQ_empty case_sum_BENQ_R case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_acopy_op_WriteR)
          also have \<open>step Tau \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 (BTL pb B1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BENQ pb (BHD pb A3') B3') (BENQ pb (BHD pb A3') B3'')))))))\<close>
            using that \<open>\<not> B3' pb \<noteq> []\<close> False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inl (Inr pb)) (BHD pb A3')) \<dots>
  (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2')
    (acopy_op (case_sum B1 (BTL pb B1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' (BENQ pb (BHD pb A3') B3'')))))))\<close>
            using that \<open>\<not> B3' pb \<noteq> []\<close> False by fastforce
          finally show ?thesis
            using that \<open>\<not> B3' pb \<noteq> []\<close> False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (smt (verit, ccfv_threshold) BAPPEND_BENQ_BHD BAPPEND_BTL BHD_BULK_BENQ_cases BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_right_empty False H that(2) that(3) that(5))
        qed
      qed
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3'')))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa A1) A2) A2') (acopy_op (case_sum (BTL pa A1) A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2'"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "A1 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3'')))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) (map_op projl projr (comp_op Some (case_sum A2 (BENQ pa (BHD pa A1') A2')) (acopy_op (case_sum A1 (BTL pa A1'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2'"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "A1' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3'')))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) (map_op projl projr (comp_op Some (case_sum (BTL pb A2) A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BENQ pb (BHD pb A2) A3) (BENQ pb (BHD pb A2) A3'))) (id_op A3'')))) op2'"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "A2 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3'')))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) (map_op projl projr (comp_op Some (case_sum A2 (BTL pb A2')) (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op (BENQ pb (BHD pb A2') A3''))))) op2'"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "A2' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_id_op_cases)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) op2' (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum (BENQ pa xa B1) (BENQ pa xa B1'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'b
      using that
      apply (intro exI conjI)
       apply force
      apply (rule wbc_base)
      by (metis BAPPEND_BENQ)
    moreover have "\<exists>op2'. wstep (Out (Inl (Inr pb)) (BHD pb B3')) (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) op2' (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BTL pb B3') B3''))))))"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "B3' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
    proof (cases \<open>A3' pb \<noteq> []\<close>)
      case True
      then show ?thesis
      proof -
        have \<open>BHD pb A3' = BHD pb B3'\<close>
          using that True
          by (metis BHD_BULK_BENQ_right_not_empty)
        hence \<open>wstep (Out (Inl (Inr pb)) (BHD pb B3'))
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 (BTL pb A3'))) (id_op A3''))))\<close>
          using that True by fastforce
        thus ?thesis
          using that True
          apply (intro exI conjI)
           apply blast
          apply (rule wbc_base)
          by (metis BAPPEND_BTL)
      qed
    next
      case False
      then show ?thesis
      proof (cases \<open>A2 pb \<noteq> []\<close>)
        case True
        then show ?thesis
        proof -
          have H: \<open>BHD pb A2 = BHD pb B3'\<close>
            using that True False by (metis (full_types) BHD_BAPPEND_2_cases BULK_BENQ_empty)
          hence \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum (BTL pb A2) A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BENQ pb (BHD pb B3') A3) (BENQ pb (BHD pb B3') A3'))) (id_op A3''))))\<close>
            using that True False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inl (Inr pb)) (BHD pb B3')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL pb A2) A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BENQ pb (BHD pb B3') A3) A3')) (id_op A3''))))\<close>
            using that True False by fastforce
          finally show ?thesis
            using that True False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (metis BAPPEND_BENQ_BHD BAPPEND_BTL BULK_BENQ_assoc)
        qed
      next
        case False
        then show ?thesis
        proof -
          have H: \<open>BHD pb A1 = BHD pb B3'\<close>
            using that \<open>\<not> A3' pb \<noteq> []\<close> False
            by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
          hence \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb B3') A2) A2')
    (acopy_op (case_sum (BTL pb A1) A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))\<close>
            using that \<open>\<not> A3' pb \<noteq> []\<close> False
            apply auto[1]
            by (metis (mono_tags, lifting) BULK_BENQ_empty False case_sum_BENQ_L case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_acopy_op_WriteL)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum (BTL pb A1) A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BENQ pb (BHD pb B3') A3) (BENQ pb (BHD pb B3') A3'))) (id_op A3''))))\<close>
            using that \<open>\<not> A3' pb \<noteq> []\<close> False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inl (Inr pb)) (BHD pb B3')) \<dots>
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum (BTL pb A1) A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BENQ pb (BHD pb B3') A3) A3')) (id_op A3''))))\<close>
            using that \<open>\<not> A3' pb \<noteq> []\<close> False by fastforce
          finally show ?thesis
            using that \<open>\<not> A3' pb \<noteq> []\<close> False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (smt (verit, ccfv_threshold) BAPPEND_BENQ_BHD BAPPEND_BTL BHD_BULK_BENQ_cases BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_right_empty False H that(2) that(3) that(5))
        qed
      qed
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr pb) (BHD pb B3'')) (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) op2' (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' (BTL pb B3'')))))))"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "B3'' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
    proof (cases \<open>A3'' pb \<noteq> []\<close>)
      case True
      then show ?thesis
      proof -
        have \<open>BHD pb A3'' = BHD pb B3''\<close>
          using that True
          by (metis BHD_BULK_BENQ_right_not_empty)
        hence \<open>wstep (Out (Inr pb) (BHD pb B3''))
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op (BTL pb A3'')))))\<close>
          using that True by fastforce
        thus ?thesis
          using that True
          apply (intro exI conjI)
           apply blast
          apply (rule wbc_base)
          by (metis BAPPEND_BTL)
      qed
    next
      case False
      then show ?thesis
      proof (cases \<open>A2' pb \<noteq> []\<close>)
        case True
        then show ?thesis
        proof -
          have H: \<open>BHD pb A2' = BHD pb B3''\<close>
            using that True False by (metis (full_types) BHD_BAPPEND_2_cases BULK_BENQ_empty)
          hence \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum A2 (BTL pb A2'))
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op (BENQ pb (BHD pb B3'') A3'')))))\<close>
            using that True False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inr pb) (BHD pb B3'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum A2 (BTL pb A2'))
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))\<close>
            using that True False by fastforce
          finally show ?thesis
            using that True False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (metis BAPPEND_BTL)
        qed
      next
        case False
        then show ?thesis
        proof -
          have H: \<open>BHD pb A1' = BHD pb B3''\<close>
            using that \<open>\<not> A3'' pb \<noteq> []\<close> False
            by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
          hence \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum A2 (BENQ pb (BHD pb B3'') A2'))
    (acopy_op (case_sum A1 (BTL pb A1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))\<close>
            using that \<open>\<not> A3'' pb \<noteq> []\<close> False
            apply auto[1]
            by (metis (no_types, lifting) BULK_BENQ_empty case_sum_BENQ_R case_sum_BHD_R case_sum_BTL_R old.sum.simps(6) step_Tau_comp_op_L step_acopy_op_WriteR that(4))
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 (BTL pb A1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op (BENQ pb (BHD pb B3'') A3'')))))\<close>
            using that \<open>\<not> A3'' pb \<noteq> []\<close> False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inr pb) (BHD pb B3'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 (BTL pb A1')))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))\<close>
            using that \<open>\<not> A3'' pb \<noteq> []\<close> False by fastforce
          finally show ?thesis
            using that \<open>\<not> A3'' pb \<noteq> []\<close> False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (smt (verit, ccfv_threshold) BAPPEND_BENQ_BHD BAPPEND_BTL BHD_BULK_BENQ_cases BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_right_empty False H that(2) that(3) that(5))
        qed
      qed
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl (Inl pb)) (BHD pb B3)) (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) op2' (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pb B3)) (acopy_op (case_sum B3' B3''))))))"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "pb \<notin> defaults"
        and "B3 pb \<noteq> []"
      for pb :: 'a
    proof (cases \<open>A3 pb \<noteq> []\<close>)
      case True
      then show ?thesis
      proof -
        have \<open>BHD pb A3 = BHD pb B3\<close>
          using that True
          by (metis BHD_BULK_BENQ_right_not_empty)
        hence \<open>wstep (Out (Inl (Inl pb)) (BHD pb B3))
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BTL pb A3) A3')) (id_op A3''))))\<close>
          using that True by fastforce
        thus ?thesis
          using that True
          apply (intro exI conjI)
           apply blast
          apply (rule wbc_base)
          by (metis BAPPEND_BTL)
      qed
    next
      case False
      then show ?thesis
      proof (cases \<open>A2 pb \<noteq> []\<close>)
        case True
        then show ?thesis
        proof -
          have H: \<open>BHD pb A2 = BHD pb B3\<close>
            using that True False by (metis (full_types) BHD_BAPPEND_2_cases BULK_BENQ_empty)
          hence \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum (BTL pb A2) A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BENQ pb (BHD pb B3) A3) (BENQ pb (BHD pb B3) A3'))) (id_op A3''))))\<close>
            using that True False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inl (Inl pb)) (BHD pb B3)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL pb A2) A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 (BENQ pb (BHD pb B3) A3'))) (id_op A3''))))\<close>
            using that True False by fastforce
          finally show ?thesis
            using that True False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (metis BAPPEND_BENQ_BHD BAPPEND_BTL BULK_BENQ_assoc)
        qed
      next
        case False
        then show ?thesis
        proof -
          have H: \<open>BHD pb A1 = BHD pb B3\<close>
            using that \<open>\<not> A3 pb \<noteq> []\<close> False
            by (metis BHD_BULK_BENQ_left_empty BHD_BULK_BENQ_right_not_empty)
          hence \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum A1 A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))
  (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb B3) A2) A2')
    (acopy_op (case_sum (BTL pb A1) A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))))\<close>
            using that \<open>\<not> A3 pb \<noteq> []\<close> False
            apply auto[1]
            by (metis (mono_tags, lifting) BULK_BENQ_empty False case_sum_BENQ_L case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_acopy_op_WriteL)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum (BTL pb A1) A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BENQ pb (BHD pb B3) A3) (BENQ pb (BHD pb B3) A3'))) (id_op A3''))))\<close>
            using that \<open>\<not> A3 pb \<noteq> []\<close> False by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out (Inl (Inl pb)) (BHD pb B3)) \<dots>
  (map_op projl projr (comp_op Some (case_sum A2 A2')
    (acopy_op (case_sum (BTL pb A1) A1'))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 (BENQ pb (BHD pb B3) A3'))) (id_op A3''))))\<close>
            using that \<open>\<not> A3 pb \<noteq> []\<close> False by fastforce
          finally show ?thesis
            using that \<open>\<not> A3 pb \<noteq> []\<close> False H
            apply (intro exI conjI)
             apply blast
            apply (rule wbc_base)
            by (smt (verit, ccfv_threshold) BAPPEND_BENQ_BHD BAPPEND_BTL BHD_BULK_BENQ_cases BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_right_empty False H that(2) that(3) that(5))
        qed
      qed
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) op2' (map_op id assoc (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa B1) B2) B2') (acopy_op (case_sum (BTL pa B1) B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "B1 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) op2' (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 (BENQ pa (BHD pa B1') B2')) (acopy_op (case_sum B1 (BTL pa B1'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))))"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "B1' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) op2' (map_op id assoc (map_op projl projr (comp_op Some (case_sum (BTL pb B2) B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pb (BHD pb B2) B3)) (acopy_op (case_sum B3' B3''))))))"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "B2 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3'')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A1' A2 A2' A3 A3' A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2') (acopy_op (case_sum A1 A1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A3 A3')) (id_op A3''))) \<and> (\<exists>B1 B1' B2 B2' B3 B3' B3''. op2 = map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 B2') (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum B3' B3''))))) \<and> (A1 >> A2) >> A3 = (B1 >> B2) >> B3 \<and> (A1 >> A2) >> A3' = (B1' >> B2') >> B3' \<and> (A1' >> A2') >> A3'' = (B1' >> B2') >> B3'')) op2' (map_op id assoc (map_op projl projr (comp_op Some (case_sum B2 (BTL pb B2')) (acopy_op (case_sum B1 B1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B3) (acopy_op (case_sum (BENQ pb (BHD pb B2') B3') (BENQ pb (BHD pb B2') B3'')))))))"
      if "(A1 >> A2) >> A3 = (B1 >> B2) >> B3"
        and "(A1 >> A2) >> A3' = (B1' >> B2') >> B3'"
        and "(A1' >> A2') >> A3'' = (B1' >> B2') >> B3''"
        and "B2' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_id_op_cases)
  qed
qed

lemma A5:
  \<open>\<C> \<bullet> (\<C> \<parallel> \<I>) \<approx> map_op id assoc (\<C> \<bullet> (\<I> \<parallel> \<C>))\<close>
  unfolding scomp_op_def
  using A5_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end