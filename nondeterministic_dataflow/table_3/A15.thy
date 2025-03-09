theory A15

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A15: Transpose and merge\<close>

lemma A15_gen:
  \<open>merge_op (case_sum
    (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3''))
    (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3''')))
  \<approx> map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
       (map_op reassoc reassoc (map_op assoc assoc
      (id_op buf1 \<parallel> transp_op (case_sum buf1' buf1'')) \<parallel> id_op buf1'''))
      (merge_op (case_sum buf3 buf3') \<parallel> merge_op (case_sum buf3'' buf3''')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3''' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "(('a + 'b) + 'a + 'b, 'a + 'b, 'c) IO"
      and op1' :: "(('a + 'b) + 'a + 'b, 'a + 'b, 'c) op"
    assume H: "step io (merge_op (case_sum (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3'')) (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3''')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3'')) (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl p) x) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (BENQ p x (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3''))) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "p \<notin> defaults"
        for p :: "'a + 'b"
          and x :: 'c
      proof (cases p)
        case (Inl a)
        from this that show ?thesis
          by (fastforce del: wbc_base intro: wbc_base)
      next
        case (Inr b)
        from this that show ?thesis
          by (fastforce del: wbc_base intro: wbc_base)
      qed
      moreover have "\<exists>op2'. wstep (Inp (Inr p) x) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (BENQ p x (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))))) op2'"
        if "p \<notin> defaults"
        for p :: "'a + 'b"
          and x :: 'c
      proof (cases p)
        case (Inl a)
        from this that show ?thesis
          by (fastforce del: wbc_base intro: wbc_base)
      next
        case (Inr b)
        from this that show ?thesis
          by (fastforce del: wbc_base intro: wbc_base)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf1)) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1 x1 \<noteq> []"
          and "buf3 x1 = []"
          and "buf2 x1 = []"
        for x1 :: 'a
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op (BTL x1 buf1))
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op (BTL x1 buf1))
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out (Inl x1) (BHD x1 buf1)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op (BTL x1 buf1))
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inl x1)) (BHD x1 buf1)\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_L)
        ultimately show ?thesis
          by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2)) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf3 x1 = []"
          and "buf2 x1 \<noteq> []"
        for x1 :: 'a
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out (Inl x1) (BHD x1 buf2)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inl x1)) (BHD x1 buf2)\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_L)
        ultimately show ?thesis
          by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans_base(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3)) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf3 x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf1' x2 \<noteq> []"
          and "buf3'' x2 = []"
          and "buf2'' x2 = []"
        for x2 :: 'b
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
           apply (rule step_Tau_comp_op_L[of \<open>Inr (Inl x2)\<close> \<open>BHD x2 buf1'\<close>])
          using that
              apply force
          by auto
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out (Inr x2) (BHD x2 buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inr x2)) (BHD x2 buf1')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_L)
        ultimately show ?thesis
          by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf2'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3'' x2 = []"
          and "buf2'' x2 \<noteq> []"
        for x2 :: 'b
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out (Inr x2) (BHD x2 buf2'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inr x2)) (BHD x2 buf2'')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_L)
        ultimately show ?thesis
          by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans_base(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> BTL x2 buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3'' x2 \<noteq> []"
        for x2 :: 'b
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf1'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((BTL x1 buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1'' x1 \<noteq> []"
          and "buf3' x1 = []"
          and "buf2' x1 = []"
        for x1 :: 'a
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
           apply (rule step_Tau_comp_op_L[of \<open>Inl (Inr x1)\<close> \<open>BHD x1 buf1''\<close>])
          using that
              apply force
          by auto
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 (BENQ x1 (BHD x1 buf1'') buf3')))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out (Inl x1) (BHD x1 buf1'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inl x1)) (BHD x1 buf1'')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_R)
        ultimately show ?thesis
          by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> BTL x1 buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf3' x1 = []"
          and "buf2' x1 \<noteq> []"
        for x1 :: 'a
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 (BENQ x1 (BHD x1 buf2') buf3')))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out (Inl x1) (BHD x1 buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inl x1)) (BHD x1 buf2')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_R)
        ultimately show ?thesis
          by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans_base(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> BTL x1 buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf3' x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((BTL x2 buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf1''' x2 \<noteq> []"
          and "buf3''' x2 = []"
          and "buf2''' x2 = []"
        for x2 :: 'b
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ x2 (BHD x2 buf1''') buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          using that by auto
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' (BENQ x2 (BHD x2 buf1''') buf3'''))))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out (Inr x2) (BHD x2 buf1''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inr x2)) (BHD x2 buf1''')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_R)
        ultimately show ?thesis
          by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf2''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> BTL x2 buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3''' x2 = []"
          and "buf2''' x2 \<noteq> []"
        for x2 :: 'b
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' (BENQ x2 (BHD x2 buf2''') buf3'''))))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out (Inr x2) (BHD x2 buf2''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inr x2)) (BHD x2 buf2''')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_R)
        ultimately show ?thesis
          by (intro exI conjI[rotated, OF wbc_base], blast, meson wstep_trans_base(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> BTL x2 buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3''' x2 \<noteq> []"
        for x2 :: 'b
        using that by (fastforce del: wbc_base intro: wbc_base del: step_wstep intro!: step_wstep)
      ultimately show ?thesis
        using H by (auto elim !: step_merge_op_elim split: sum.splits if_splits)
    qed
  next
    fix io :: "(('a + 'b) + 'a + 'b, 'a + 'b, 'c) IO"
      and op1' :: "(('a + 'b) + 'a + 'b, 'a + 'b, 'c) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op1'"
    show "\<exists>op2'. wstep io (merge_op (case_sum (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3'')) (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3'')) (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl (Inl pc)) x) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pc x buf1)) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "pc \<notin> defaults"
        for x :: 'c
          and pc :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Inp (Inl (Inr x1a)) x) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum (BENQ x1a x buf1') buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "x1a \<notin> defaults"
        for x :: 'c
          and x1a :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Inp (Inr (Inl x2)) x) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' (BENQ x2 x buf1''))))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "x2 \<notin> defaults"
        for x :: 'c
          and x2 :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Inp (Inr (Inr pb)) x) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op (BENQ pb x buf1''')))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "pb \<notin> defaults"
        for x :: 'c
          and pb :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inr pb) (BHD pb buf3'')) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum (BTL pb buf3'') buf3'''))))) op2'"
        if "buf3'' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inr pb) (BHD pb buf3''')) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' (BTL pb buf3''')))))) op2'"
        if "buf3''' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inl pb) (BHD pb buf3)) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL pb buf3) buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "buf3 pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inl pb) (BHD pb buf3')) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 (BTL pb buf3'))) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "buf3' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ pb (BHD pb buf1''') buf2'''))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op (BTL pb buf1''')))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "pb \<notin> defaults"
          and "buf1''' pb \<noteq> []"
        for pb :: 'b
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) auto
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' (BTL x1 buf1''))))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf1'' x1 \<noteq> []"
        for x1 :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) auto
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum (BTL x2 buf1') buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf1' x2 \<noteq> []"
        for x2 :: 'b
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) auto
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ pc (BHD pc buf1) buf2) buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pc buf1)) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "pc \<notin> defaults"
          and "buf1 pc \<noteq> []"
        for pc :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) auto
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum (BTL pb buf2) buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ pb (BHD pb buf2) buf3) buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "buf2 pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], blast, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL pb buf2')) (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 (BENQ pb (BHD pb buf2') buf3'))) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "buf2' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], blast, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL pb buf2'') buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum (BENQ pb (BHD pb buf2'') buf3'') buf3'''))))) op2'"
        if "buf2'' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'b
        using that
        by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], blast, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL pb buf2'''))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' (BENQ pb (BHD pb buf2''') buf3''')))))) op2'"
        if "buf2''' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'b
        using that
        by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], blast, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_transp_op_cases step_merge_op_elim split: sum.splits)
    qed
  qed
qed

lemma A15:
  assumes \<open>Vmn = (\<V> :: (('m :: {countable, defaults} + 'n :: {countable, defaults}) + 'm + 'n, 'm + 'n, 'd) op)\<close>
    and \<open>Vm = (\<V> :: ('m + 'm, 'm, 'd) op)\<close>
    and \<open>Vn = (\<V> :: ('n + 'n, 'n, 'd) op)\<close>
    and \<open>Imm = (\<I> :: ('m, 'm, 'd) op)\<close>
    and \<open>Inn = (\<I> :: ('n, 'n, 'd) op)\<close>
    and \<open>Xnm = (\<X> :: ('n + 'm, 'm + 'n, 'd) op)\<close>
  shows \<open>Vmn \<approx> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xnm) \<parallel> Inn) \<bullet> (Vm \<parallel> Vn)\<close>
  unfolding scomp_op_def
  using assms A15_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end