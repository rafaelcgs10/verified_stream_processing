theory A15

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A15: Transpose and equality test\<close>

lemma A15_gen:
  \<open>(aeq_op (case_sum
    (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3''))
    (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3''')))
  :: (('m :: {countable, defaults} + 'n :: {countable, defaults}) + 'm + 'n, 'm + 'n, 'd option) op)
  \<approx> map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
      (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
          (id_op buf1)
          (transp_op (case_sum buf1' buf1''))))
        (id_op buf1''')))
      (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (aeq_op (case_sum buf3 buf3'))
        (aeq_op (case_sum buf3'' buf3'''))))\<close>
proof (coinduction arbitrary: buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3''' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inl p) y) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (BENQ p y (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3''))) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "p \<notin> defaults"
      for p :: "'m + 'n"
        and y :: "'d option"
      using that by (cases p; fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp (Inr p) y) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (BENQ p y (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))))) op2'"
      if "p \<notin> defaults"
      for p :: "'m + 'n"
        and y :: "'d option"
      using that by (cases p; fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf1'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((BTL x1 buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1'' x1 \<noteq> []"
        and "x1 \<notin> defaults"
        and "BHD x1 buf1 = BHD x1 buf1''"
        and "buf1 x1 \<noteq> []"
        and "buf3' x1 = []"
        and "buf3 x1 = []"
        and "buf2' x1 = []"
        and "buf2 x1 = []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) (BENQ x1 (BHD x1 buf1'') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) (BHD x1 buf1'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf1'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((BTL x1 buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1'' x1 \<noteq> []"
        and "x1 \<notin> defaults"
        and "BHD x1 buf2 = BHD x1 buf1''"
        and "buf3' x1 = []"
        and "buf3 x1 = []"
        and "buf2' x1 = []"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) (BENQ x1 (BHD x1 buf1'') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) (BHD x1 buf1'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> BTL x1 buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf1 = BHD x1 buf2'"
        and "buf1 x1 \<noteq> []"
        and "buf3' x1 = []"
        and "buf3 x1 = []"
        and "buf2' x1 \<noteq> []"
        and "buf2 x1 = []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) (BENQ x1 (BHD x1 buf2') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) (BHD x1 buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> BTL x1 buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf2 = BHD x1 buf2'"
        and "buf3' x1 = []"
        and "buf3 x1 = []"
        and "buf2' x1 \<noteq> []"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) (BENQ x1 (BHD x1 buf2') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) (BHD x1 buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf1'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((BTL x1 buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1'' x1 \<noteq> []"
        and "x1 \<notin> defaults"
        and "BHD x1 buf3 = BHD x1 buf1''"
        and "buf3' x1 = []"
        and "buf3 x1 \<noteq> []"
        and "buf2' x1 = []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 (BENQ x1 (BHD x1 buf1'') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) (BHD x1 buf1'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BTL x1 buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> BTL x1 buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf3 = BHD x1 buf2'"
        and "buf3' x1 = []"
        and "buf3 x1 \<noteq> []"
        and "buf2' x1 \<noteq> []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 (BENQ x1 (BHD x1 buf2') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) (BHD x1 buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BTL x1 buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> BTL x1 buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf1 = BHD x1 buf3'"
        and "buf1 x1 \<noteq> []"
        and "buf3' x1 \<noteq> []"
        and "buf3 x1 = []"
        and "buf2 x1 = []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) (BHD x1 buf3')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 (BTL x1 buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> BTL x1 buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf2 = BHD x1 buf3'"
        and "buf3' x1 \<noteq> []"
        and "buf3 x1 = []"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) (BHD x1 buf3')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 (BTL x1 buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> BTL x1 buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf3 = BHD x1 buf3'"
        and "buf3' x1 \<noteq> []"
        and "buf3 x1 \<noteq> []"
      for x1 :: 'm
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((BTL x2 buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1''' x2 \<noteq> []"
        and "x2 \<notin> defaults"
        and "BHD x2 buf1' = BHD x2 buf1'''"
        and "buf1' x2 \<noteq> []"
        and "buf3''' x2 = []"
        and "buf3'' x2 = []"
        and "buf2''' x2 = []"
        and "buf2'' x2 = []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ x2 (BHD x2 buf1''') buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') (BENQ x2 (BHD x2 buf1''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) (BHD x2 buf1''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((BTL x2 buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1''' x2 \<noteq> []"
        and "x2 \<notin> defaults"
        and "BHD x2 buf2'' = BHD x2 buf1'''"
        and "buf3''' x2 = []"
        and "buf3'' x2 = []"
        and "buf2''' x2 = []"
        and "buf2'' x2 \<noteq> []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') (BENQ x2 (BHD x2 buf1''') buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') (BENQ x2 (BHD x2 buf1''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) (BHD x2 buf1''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf2''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> BTL x2 buf2''') >> buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf1' = BHD x2 buf2'''"
        and "buf1' x2 \<noteq> []"
        and "buf3''' x2 = []"
        and "buf3'' x2 = []"
        and "buf2''' x2 \<noteq> []"
        and "buf2'' x2 = []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') (BENQ x2 (BHD x2 buf2''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) (BHD x2 buf2''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf2''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> BTL x2 buf2''') >> buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf2'' = BHD x2 buf2'''"
        and "buf3''' x2 = []"
        and "buf3'' x2 = []"
        and "buf2''' x2 \<noteq> []"
        and "buf2'' x2 \<noteq> []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') (BENQ x2 (BHD x2 buf2''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) (BHD x2 buf2''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> BTL x2 buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((BTL x2 buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1''' x2 \<noteq> []"
        and "x2 \<notin> defaults"
        and "BHD x2 buf3'' = BHD x2 buf1'''"
        and "buf3''' x2 = []"
        and "buf3'' x2 \<noteq> []"
        and "buf2''' x2 = []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ x2 (BHD x2 buf1''') buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' (BENQ x2 (BHD x2 buf1''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) (BHD x2 buf1''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BTL x2 buf3'') buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf2''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> BTL x2 buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> BTL x2 buf2''') >> buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf3'' = BHD x2 buf2'''"
        and "buf3''' x2 = []"
        and "buf3'' x2 \<noteq> []"
        and "buf2''' x2 \<noteq> []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' (BENQ x2 (BHD x2 buf2''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) (BHD x2 buf2''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BTL x2 buf3'') buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> BTL x2 buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf1' = BHD x2 buf3'''"
        and "buf1' x2 \<noteq> []"
        and "buf3''' x2 \<noteq> []"
        and "buf3'' x2 = []"
        and "buf2'' x2 = []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) (BHD x2 buf3''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' (BTL x2 buf3'''))))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> BTL x2 buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf2'' = BHD x2 buf3'''"
        and "buf3''' x2 \<noteq> []"
        and "buf3'' x2 = []"
        and "buf2'' x2 \<noteq> []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) (BHD x2 buf3''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' (BTL x2 buf3'''))))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> BTL x2 buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> BTL x2 buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf3'' = BHD x2 buf3'''"
        and "buf3''' x2 \<noteq> []"
        and "buf3'' x2 \<noteq> []"
      for x2 :: 'n
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((BTL x1 buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1'' x1 \<noteq> []"
        and "x1 \<notin> defaults"
        and "BHD x1 buf1 \<noteq> BHD x1 buf1''"
        and "buf1 x1 \<noteq> []"
        and "buf3' x1 = []"
        and "buf3 x1 = []"
        and "buf2' x1 = []"
        and "buf2 x1 = []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) (BENQ x1 (BHD x1 buf1'') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((BTL x1 buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1'' x1 \<noteq> []"
        and "x1 \<notin> defaults"
        and "BHD x1 buf2 \<noteq> BHD x1 buf1''"
        and "buf3' x1 = []"
        and "buf3 x1 = []"
        and "buf2' x1 = []"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) (BENQ x1 (BHD x1 buf1'') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> BTL x1 buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf1 \<noteq> BHD x1 buf2'"
        and "buf1 x1 \<noteq> []"
        and "buf3' x1 = []"
        and "buf3 x1 = []"
        and "buf2' x1 \<noteq> []"
        and "buf2 x1 = []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) (BENQ x1 (BHD x1 buf2') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> BTL x1 buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf2 \<noteq> BHD x1 buf2'"
        and "buf3' x1 = []"
        and "buf3 x1 = []"
        and "buf2' x1 \<noteq> []"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) (BENQ x1 (BHD x1 buf2') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((BTL x1 buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1'' x1 \<noteq> []"
        and "x1 \<notin> defaults"
        and "BHD x1 buf3 \<noteq> BHD x1 buf1''"
        and "buf3' x1 = []"
        and "buf3 x1 \<noteq> []"
        and "buf2' x1 = []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 (BENQ x1 (BHD x1 buf1'') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BTL x1 buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> BTL x1 buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf3 \<noteq> BHD x1 buf2'"
        and "buf3' x1 = []"
        and "buf3 x1 \<noteq> []"
        and "buf2' x1 \<noteq> []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 (BENQ x1 (BHD x1 buf2') buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BTL x1 buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> BTL x1 buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf1 \<noteq> BHD x1 buf3'"
        and "buf1 x1 \<noteq> []"
        and "buf3' x1 \<noteq> []"
        and "buf3 x1 = []"
        and "buf2 x1 = []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op (BTL x1 buf1))
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 (BTL x1 buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> BTL x1 buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf2 \<noteq> BHD x1 buf3'"
        and "buf3' x1 \<noteq> []"
        and "buf3 x1 = []"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'm
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inl x1) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 (BTL x1 buf3')))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> BTL x1 buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
      if "x1 \<notin> defaults"
        and "BHD x1 buf3 \<noteq> BHD x1 buf3'"
        and "buf3' x1 \<noteq> []"
        and "buf3 x1 \<noteq> []"
      for x1 :: 'm
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((BTL x2 buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1''' x2 \<noteq> []"
        and "x2 \<notin> defaults"
        and "BHD x2 buf1' \<noteq> BHD x2 buf1'''"
        and "buf1' x2 \<noteq> []"
        and "buf3''' x2 = []"
        and "buf3'' x2 = []"
        and "buf2''' x2 = []"
        and "buf2'' x2 = []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ x2 (BHD x2 buf1''') buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') (BENQ x2 (BHD x2 buf1''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((BTL x2 buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1''' x2 \<noteq> []"
        and "x2 \<notin> defaults"
        and "BHD x2 buf2'' \<noteq> BHD x2 buf1'''"
        and "buf3''' x2 = []"
        and "buf3'' x2 = []"
        and "buf2''' x2 = []"
        and "buf2'' x2 \<noteq> []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') (BENQ x2 (BHD x2 buf1''') buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') (BENQ x2 (BHD x2 buf1''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> BTL x2 buf2''') >> buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf1' \<noteq> BHD x2 buf2'''"
        and "buf1' x2 \<noteq> []"
        and "buf3''' x2 = []"
        and "buf3'' x2 = []"
        and "buf2''' x2 \<noteq> []"
        and "buf2'' x2 = []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') (BENQ x2 (BHD x2 buf2''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> BTL x2 buf2''') >> buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf2'' \<noteq> BHD x2 buf2'''"
        and "buf3''' x2 = []"
        and "buf3'' x2 = []"
        and "buf2''' x2 \<noteq> []"
        and "buf2'' x2 \<noteq> []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') (BENQ x2 (BHD x2 buf2''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> BTL x2 buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((BTL x2 buf1''' >> buf2''') >> buf3''')))) op2'"
      if "buf1''' x2 \<noteq> []"
        and "x2 \<notin> defaults"
        and "BHD x2 buf3'' \<noteq> BHD x2 buf1'''"
        and "buf3''' x2 = []"
        and "buf3'' x2 \<noteq> []"
        and "buf2''' x2 = []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ x2 (BHD x2 buf1''') buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' (BENQ x2 (BHD x2 buf1''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BTL x2 buf3'') buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> BTL x2 buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> BTL x2 buf2''') >> buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf3'' \<noteq> BHD x2 buf2'''"
        and "buf3''' x2 = []"
        and "buf3'' x2 \<noteq> []"
        and "buf2''' x2 \<noteq> []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' (BENQ x2 (BHD x2 buf2''') buf3'''))))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BTL x2 buf3'') buf3''')))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> BTL x2 buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf1' \<noteq> BHD x2 buf3'''"
        and "buf1' x2 \<noteq> []"
        and "buf3''' x2 \<noteq> []"
        and "buf3'' x2 = []"
        and "buf2'' x2 = []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))\<close>
        using that
        apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
        by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' (BTL x2 buf3'''))))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> BTL x2 buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf2'' \<noteq> BHD x2 buf3'''"
        and "buf3''' x2 \<noteq> []"
        and "buf3'' x2 = []"
        and "buf2'' x2 \<noteq> []"
      for x2 :: 'n
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out (Inr x2) None) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
        (id_op buf1)
        (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (aeq_op (case_sum buf3 buf3'))
      (aeq_op (case_sum buf3'' (BTL x2 buf3'''))))))\<close>
        using that by auto
      finally show ?thesis by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) None) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> BTL x2 buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> BTL x2 buf3''')))) op2'"
      if "x2 \<notin> defaults"
        and "BHD x2 buf3'' \<noteq> BHD x2 buf3'''"
        and "buf3''' x2 \<noteq> []"
        and "buf3'' x2 \<noteq> []"
      for x2 :: 'n
      using that by (fastforce del: wbc_base intro!: wbc_base)
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM1 by (auto 0 0 elim !: step_aeq_op_elim split: sum.splits if_splits simp add: prems)
      done
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inl (Inl pc)) x) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pc x buf1)) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "pc \<notin> defaults"
      for x :: "'d option"
        and pc :: 'm
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp (Inl (Inr x1a)) x) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum (BENQ x1a x buf1') buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "x1a \<notin> defaults"
      for x :: "'d option"
        and x1a :: 'n
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp (Inr (Inl x2)) x) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' (BENQ x2 x buf1''))))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "x2 \<notin> defaults"
      for x :: "'d option"
        and x2 :: 'm
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp (Inr (Inr pb)) x) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op (BENQ pb x buf1''')))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "pb \<notin> defaults"
      for x :: "'d option"
        and pb :: 'n
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr pb) (BHD pb buf3''')) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum (BTL pb buf3'') (BTL pb buf3'''))))))"
      if "buf3'' pb \<noteq> []"
        and "buf3''' pb \<noteq> []"
        and "pb \<notin> defaults"
        and "BHD pb buf3'' = BHD pb buf3'''"
      for pb :: 'n
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr pb) None) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum (BTL pb buf3'') (BTL pb buf3'''))))))"
      if "buf3'' pb \<noteq> []"
        and "buf3''' pb \<noteq> []"
        and "pb \<notin> defaults"
        and "BHD pb buf3'' \<noteq> BHD pb buf3'''"
      for pb :: 'n
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl pb) (BHD pb buf3')) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb buf3) (BTL pb buf3'))) (aeq_op (case_sum buf3'' buf3''')))))"
      if "buf3 pb \<noteq> []"
        and "buf3' pb \<noteq> []"
        and "pb \<notin> defaults"
        and "BHD pb buf3 = BHD pb buf3'"
      for pb :: 'm
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl pb) None) (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb buf3) (BTL pb buf3'))) (aeq_op (case_sum buf3'' buf3''')))))"
      if "buf3 pb \<noteq> []"
        and "buf3' pb \<noteq> []"
        and "pb \<notin> defaults"
        and "BHD pb buf3 \<noteq> BHD pb buf3'"
      for pb :: 'm
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ pb (BHD pb buf1''') buf2'''))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op (BTL pb buf1''')))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "pb \<notin> defaults"
        and "buf1''' pb \<noteq> []"
      for pb :: 'n
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' (BTL x1 buf1''))))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "x1 \<notin> defaults"
        and "buf1'' x1 \<noteq> []"
      for x1 :: 'm
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum (BTL x2 buf1') buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "x2 \<notin> defaults"
        and "buf1' x2 \<noteq> []"
      for x2 :: 'n
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ pc (BHD pc buf1) buf2) buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pc buf1)) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "pc \<notin> defaults"
        and "buf1 pc \<noteq> []"
      for pc :: 'm
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum (BTL pb buf2) buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ pb (BHD pb buf2) buf3) buf3')) (aeq_op (case_sum buf3'' buf3''')))))"
      if "buf2 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'm
      using that
      by (intro exI conjI[rotated, OF wbc_base], blast, metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL pb buf2')) (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 (BENQ pb (BHD pb buf2') buf3'))) (aeq_op (case_sum buf3'' buf3''')))))"
      if "buf2' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'm
      using that
      by (intro exI conjI[rotated, OF wbc_base], blast, metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL pb buf2'') buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum (BENQ pb (BHD pb buf2'') buf3'') buf3''')))))"
      if "buf2'' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'n
      using that
      by (intro exI conjI[rotated, OF wbc_base], blast, metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = aeq_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' buf3'''))))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL pb buf2'''))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf3 buf3')) (aeq_op (case_sum buf3'' (BENQ pb (BHD pb buf2''') buf3'''))))))"
      if "buf2''' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'n
      using that
      by (intro exI conjI[rotated, OF wbc_base], blast, metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM2 by (auto 0 0 elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_transp_op_cases step_aeq_op_elim split: sum.splits simp add: prems)
      done
  qed
qed

lemma A15:
  \<open>(\<Q> :: (('m :: {countable, defaults} + 'n :: {countable, defaults}) + 'm + 'n, 'm + 'n, 'd option) op)
  \<approx> map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>) \<bullet> (\<Q> \<parallel> \<Q>)\<close>
  unfolding scomp_op_def pcomp_op_def
  using A15_gen[of \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close> \<open>\<lambda> _. []\<close>]
  by simp

end