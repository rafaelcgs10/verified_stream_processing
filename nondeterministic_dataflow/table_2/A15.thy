theory A15

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)



section \<open>Axiom A15: Transpose and equality test\<close>

lemma A15_gen:
  "(aeq_op (case_sum (case_sum (buf1M >> buf1M' >> buf1M'') (buf2N >> buf2N' >> buf2N'')) (case_sum (buf2M >> buf2M' >> buf2M'') (buf1N >> buf1N' >> buf1N''))) :: (('m :: {countable,defaults} + 'n ::{countable,defaults}) + 'm + 'n, 'm + 'n, 'd) op) \<approx>
   map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
   (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (buf1N)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
proof (coinduction arbitrary: buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N'' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case 
    unfolding wsim_def
  proof (intro allI impI conjI)
    fix io :: "(('m + 'n) + 'm + 'n, 'm + 'n, 'd) IO"
      and op1' :: "(('m + 'n) + 'm + 'n, 'm + 'n, 'd) op"
    assume H: "step io (aeq_op (case_sum (case_sum (buf1M >> buf1M' >> buf1M'') (buf2N >> buf2N' >> buf2N'')) (case_sum (buf2M >> buf2M' >> buf2M'') (buf1N >> buf1N' >> buf1N'')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum (buf1M >> buf1M' >> buf1M'') (buf2N >> buf2N' >> buf2N'')) (case_sum (buf2M >> buf2M' >> buf2M'') (buf1N >> buf1N' >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl p) y) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (BENQ p y (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N''))) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "p \<notin> defaults"
        for p :: "'m + 'n"
          and y :: 'd
        using that 
      proof (cases p)
        case (Inl a)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force+
          done
      next
        case (Inr b)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force+
          done
      qed
      moreover have "\<exists>op2'. wstep (Inp (Inr p) y) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (BENQ p y (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))))) op2'"
        if "p \<notin> defaults"
        for p :: "'m + 'n"
          and y :: 'd
        using that 
      proof (cases p)
        case (Inl a)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force+
          done
      next
        case (Inr b)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply (force del: step_wstep intro!: step_wstep)+
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((BTL x1 buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf2M x1 \<noteq> []"
          and "BHD x1 buf1M = BHD x1 buf2M"
          and "x1 \<notin> defaults"
          and "buf1M x1 \<noteq> []"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 = []"
          and "buf2M' x1 = []"
          and "buf1M' x1 = []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that   
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        also  have "step Tau
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        also have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        also have "step Tau \<dots>
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        also have "step (Out (Inr (Inl x1)) (BHD x1 buf2M))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by auto
        finally show ?thesis using BISIM by (force del: wbc_base intro!: wbc_base)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> BTL x1 buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((BTL x1 buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf2M x1 \<noteq> []"
          and "BHD x1 buf1M' = BHD x1 buf2M"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 = []"
          and "buf2M' x1 = []"
          and "buf1M' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step (Out (Inr (Inl x1)) (BHD x1 buf2M))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by auto
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> BTL x1 buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M = BHD x1 buf2M'"
          and "x1 \<notin> defaults"
          and "buf1M x1 \<noteq> []"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 = []"
          and "buf2M' x1 \<noteq> []"
          and "buf1M' x1 = []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step (Out (Inr (Inl x1)) (BHD x1 buf2M'))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by auto
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> BTL x1 buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> BTL x1 buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M' = BHD x1 buf2M'"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 = []"
          and "buf2M' x1 \<noteq> []"
          and "buf1M' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step (Out (Inr (Inl x1)) (BHD x1 buf2M'))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by auto
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> BTL x1 buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((BTL x1 buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf2M x1 \<noteq> []"
          and "BHD x1 buf1M'' = BHD x1 buf2M"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 \<noteq> []"
          and "buf2M' x1 = []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step (Out (Inr (Inl x1)) (BHD x1 buf2M))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL x1 buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> BTL x1 buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> BTL x1 buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M'' = BHD x1 buf2M'"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 \<noteq> []"
          and "buf2M' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step (Out (Inr (Inl x1)) (BHD x1 buf2M'))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL x1 buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> BTL x1 buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M = BHD x1 buf2M''"
          and "x1 \<notin> defaults"
          and "buf1M x1 \<noteq> []"
          and "buf2M'' x1 \<noteq> []"
          and "buf1M'' x1 = []"
          and "buf1M' x1 = []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step (Out (Inr (Inl x1)) (BHD x1 buf2M'')) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BTL x1 buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> BTL x1 buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> BTL x1 buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M' = BHD x1 buf2M''"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 \<noteq> []"
          and "buf1M'' x1 = []"
          and "buf1M' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step (Out (Inr (Inl x1)) (BHD x1 buf2M'')) ?op'
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BTL x1 buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2M'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> BTL x1 buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> BTL x1 buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M'' = BHD x1 buf2M''"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 \<noteq> []"
          and "buf1M'' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x1 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply force
        done
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((BTL x2 buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((BTL x2 buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf1N x2 \<noteq> []"
          and "BHD x2 buf2N = BHD x2 buf1N"
          and "x2 \<notin> defaults"
          and "buf2N x2 \<noteq> []"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 = []"
          and "buf1N' x2 = []"
          and "buf2N' x2 = []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BENQ x2 (BHD x2 buf1N) buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BENQ x2 (BHD x2 buf2N) buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N) buf2N'') (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step (Out (Inr (Inr x2)) (BHD x2 buf1N)) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force+
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> BTL x2 buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((BTL x2 buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf1N x2 \<noteq> []"
          and "BHD x2 buf2N' = BHD x2 buf1N"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 = []"
          and "buf1N' x2 = []"
          and "buf2N' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BENQ x2 (BHD x2 buf1N) buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N') buf2N'') (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step (Out (Inr (Inr x2)) (BHD x2 buf1N)) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((BTL x2 buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> BTL x2 buf1N') >> buf1N'')))) op2'"
        if "BHD x2 buf2N = BHD x2 buf1N'"
          and "x2 \<notin> defaults"
          and "buf2N x2 \<noteq> []"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 = []"
          and "buf1N' x2 \<noteq> []"
          and "buf2N' x2 = []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that 
      proof -
        have "step Tau 
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BENQ x2 (BHD x2 buf2N) buf2N') (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N) buf2N'') (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step (Out (Inr (Inr x2)) (BHD x2 buf1N')) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" 
          using that by auto
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> BTL x2 buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> BTL x2 buf1N') >> buf1N'')))) op2'"
        if "BHD x2 buf2N' = BHD x2 buf1N'"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 = []"
          and "buf1N' x2 \<noteq> []"
          and "buf2N' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that  
      proof -
        have "step Tau 
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N') buf2N'') (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step (Out (Inr (Inr x2)) (BHD x2 buf1N')) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" 
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> BTL x2 buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((BTL x2 buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf1N x2 \<noteq> []"
          and "BHD x2 buf2N'' = BHD x2 buf1N"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 \<noteq> []"
          and "buf1N' x2 = []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BENQ x2 (BHD x2 buf1N) buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step (Out (Inr (Inr x2)) (BHD x2 buf1N)) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BTL x2 buf2N'') buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> BTL x2 buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> BTL x2 buf1N') >> buf1N'')))) op2'"
        if "BHD x2 buf2N'' = BHD x2 buf1N'"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 \<noteq> []"
          and "buf1N' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step (Out (Inr (Inr x2)) (BHD x2 buf1N')) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BTL x2 buf2N'') buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((BTL x2 buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> BTL x2 buf1N'')))) op2'"
        if "BHD x2 buf2N = BHD x2 buf1N''"
          and "x2 \<notin> defaults"
          and "buf2N x2 \<noteq> []"
          and "buf1N'' x2 \<noteq> []"
          and "buf2N'' x2 = []"
          and "buf2N' x2 = []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BENQ x2 (BHD x2 buf2N) buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N) buf2N'') buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step (Out (Inr (Inr x2)) (BHD x2 buf1N'')) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BTL x2 buf1N'')))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> BTL x2 buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> BTL x2 buf1N'')))) op2'"
        if "BHD x2 buf2N' = BHD x2 buf1N''"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 \<noteq> []"
          and "buf2N'' x2 = []"
          and "buf2N' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N') buf2N'') buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step (Out (Inr (Inr x2)) (BHD x2 buf1N'')) ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BTL x2 buf1N'')))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1N'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> BTL x2 buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> BTL x2 buf1N'')))) op2'"
        if "BHD x2 buf2N'' = BHD x2 buf1N''"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 \<noteq> []"
          and "buf2N'' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x :: 'd
          and x2 :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply force
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((BTL x1 buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf2M x1 \<noteq> []"
          and "BHD x1 buf1M \<noteq> BHD x1 buf2M"
          and "x1 \<notin> defaults"
          and "buf1M x1 \<noteq> []"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 = []"
          and "buf2M' x1 = []"
          and "buf1M' x1 = []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> BTL x1 buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((BTL x1 buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf2M x1 \<noteq> []"
          and "BHD x1 buf1M' \<noteq> BHD x1 buf2M"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 = []"
          and "buf2M' x1 = []"
          and "buf1M' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> BTL x1 buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M \<noteq> BHD x1 buf2M'"
          and "x1 \<notin> defaults"
          and "buf1M x1 \<noteq> []"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 = []"
          and "buf2M' x1 \<noteq> []"
          and "buf1M' x1 = []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> BTL x1 buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> BTL x1 buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M' \<noteq> BHD x1 buf2M'"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 = []"
          and "buf2M' x1 \<noteq> []"
          and "buf1M' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> BTL x1 buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((BTL x1 buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf2M x1 \<noteq> []"
          and "BHD x1 buf1M'' \<noteq> BHD x1 buf2M"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 \<noteq> []"
          and "buf2M' x1 = []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL x1 buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> BTL x1 buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> BTL x1 buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M'' \<noteq> BHD x1 buf2M'"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 = []"
          and "buf1M'' x1 \<noteq> []"
          and "buf2M' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ x1 (BHD x1 buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' (BTL x1 buf2M')) (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL x1 buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((BTL x1 buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> BTL x1 buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M \<noteq> BHD x1 buf2M''"
          and "x1 \<notin> defaults"
          and "buf1M x1 \<noteq> []"
          and "buf2M'' x1 \<noteq> []"
          and "buf1M'' x1 = []"
          and "buf1M' x1 = []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1M) buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BTL x1 buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> BTL x1 buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> BTL x1 buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M' \<noteq> BHD x1 buf2M''"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 \<noteq> []"
          and "buf1M'' x1 = []"
          and "buf1M' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum (BTL x1 buf1M') buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BTL x1 buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> BTL x1 buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> BTL x1 buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2'"
        if "BHD x1 buf1M'' \<noteq> BHD x1 buf2M''"
          and "x1 \<notin> defaults"
          and "buf2M'' x1 \<noteq> []"
          and "buf1M'' x1 \<noteq> []"
        for p :: "'m + 'n"
          and x1 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply force
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((BTL x2 buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((BTL x2 buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf1N x2 \<noteq> []"
          and "BHD x2 buf2N \<noteq> BHD x2 buf1N"
          and "x2 \<notin> defaults"
          and "buf2N x2 \<noteq> []"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 = []"
          and "buf1N' x2 = []"
          and "buf2N' x2 = []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BENQ x2 (BHD x2 buf1N) buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BENQ x2 (BHD x2 buf2N) buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N) buf2N'') (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> BTL x2 buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((BTL x2 buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf1N x2 \<noteq> []"
          and "BHD x2 buf2N' \<noteq> BHD x2 buf1N"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 = []"
          and "buf1N' x2 = []"
          and "buf2N' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that   using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BENQ x2 (BHD x2 buf1N) buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N') buf2N'') (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((BTL x2 buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> BTL x2 buf1N') >> buf1N'')))) op2'"
        if "BHD x2 buf2N \<noteq> BHD x2 buf1N'"
          and "x2 \<notin> defaults"
          and "buf2N x2 \<noteq> []"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 = []"
          and "buf1N' x2 \<noteq> []"
          and "buf2N' x2 = []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that 
      proof -
        have "step Tau 
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BENQ x2 (BHD x2 buf2N) buf2N') (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N) buf2N'') (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" 
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> BTL x2 buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> BTL x2 buf1N') >> buf1N'')))) op2'"
        if "BHD x2 buf2N' \<noteq> BHD x2 buf1N'"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 = []"
          and "buf1N' x2 \<noteq> []"
          and "buf2N' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that 
      proof -
        have "step Tau 
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N') buf2N'') (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by force
        moreover  have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" 
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> BTL x2 buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((BTL x2 buf1N >> buf1N') >> buf1N'')))) op2'"
        if "buf1N x2 \<noteq> []"
          and "BHD x2 buf2N'' \<noteq> BHD x2 buf1N"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 \<noteq> []"
          and "buf1N' x2 = []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BENQ x2 (BHD x2 buf1N) buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N) buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL x2 buf1N))))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BTL x2 buf2N'') buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> BTL x2 buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> BTL x2 buf1N') >> buf1N'')))) op2'"
        if "BHD x2 buf2N'' \<noteq> BHD x2 buf1N'"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 = []"
          and "buf2N'' x2 \<noteq> []"
          and "buf1N' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ x2 (BHD x2 buf1N') buf1N'')))))" (is "step Tau ?op ?op'")
          using that by fastforce
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL x2 buf1N')))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BTL x2 buf2N'') buf1N''))))"
          using that by fastforce
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((BTL x2 buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> BTL x2 buf1N'')))) op2'"
        if "BHD x2 buf2N \<noteq> BHD x2 buf1N''"
          and "x2 \<notin> defaults"
          and "buf2N x2 \<noteq> []"
          and "buf1N'' x2 \<noteq> []"
          and "buf2N'' x2 = []"
          and "buf2N' x2 = []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BENQ x2 (BHD x2 buf2N) buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N) buf2N'') buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BTL x2 buf1N'')))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> BTL x2 buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> BTL x2 buf1N'')))) op2'"
        if "BHD x2 buf2N' \<noteq> BHD x2 buf1N''"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 \<noteq> []"
          and "buf2N'' x2 = []"
          and "buf2N' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ x2 (BHD x2 buf2N') buf2N'') buf1N''))))" (is "step Tau ?op ?op'")
          using that by force
        moreover have "step Tau ?op'
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL x2 buf2N') buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BTL x2 buf1N'')))))"
          using that by force
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> BTL x2 buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> BTL x2 buf1N'')))) op2'"
        if "BHD x2 buf2N'' \<noteq> BHD x2 buf1N''"
          and "x2 \<notin> defaults"
          and "buf1N'' x2 \<noteq> []"
          and "buf2N'' x2 \<noteq> []"
        for p :: "'m + 'n"
          and x2 :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply force
        done
      ultimately show ?thesis
        apply -
        subgoal premises prems
          using H apply (elim step_aeq_op_elim step_map_op_elim step_split_op_cases step_transp_op_cases step_comp_op_elim step_id_op_cases; simp split: sum.splits if_splits; hypsubst_thin?)
          apply (rule prems; assumption)+
          done
        done
    qed
  next
    fix io :: "(('m + 'n) + 'm + 'n, 'm + 'n, 'd) IO"
      and op1' :: "(('m + 'n) + 'm + 'n, 'm + 'n, 'd) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op1'"
    show "\<exists>op2'. wstep io (aeq_op (case_sum (case_sum (buf1M >> buf1M' >> buf1M'') (buf2N >> buf2N' >> buf2N'')) (case_sum (buf2M >> buf2M' >> buf2M'') (buf1N >> buf1N' >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum (buf1M >> buf1M' >> buf1M'') (buf2N >> buf2N' >> buf2N'')) (case_sum (buf2M >> buf2M' >> buf2M'') (buf1N >> buf1N' >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl (Inl pc)) x) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pc x buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "pc \<notin> defaults"
        for x :: 'd
          and pc :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Inp (Inl (Inr x1a)) x) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BENQ x1a x buf2N) buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "x1a \<notin> defaults"
        for x :: 'd
          and x1a :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Inp (Inr (Inl x2)) x) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BENQ x2 x buf2M))))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "x2 \<notin> defaults"
        for x :: 'd
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Inp (Inr (Inr pb)) x) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BENQ pb x buf1N)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "pb \<notin> defaults"
        for x :: 'd
          and pb :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Out (Inr pb) (BHD pb buf1N'')) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BTL pb buf2N'') (BTL pb buf1N'')))))) op2'"
        if "buf2N'' pb \<noteq> []"
          and "buf1N'' pb \<noteq> []"
          and "BHD pb buf2N'' = BHD pb buf1N''"
          and "pb \<notin> defaults"
        for pb :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Out (Inl pb) (BHD pb buf2M'')) (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb buf1M'') (BTL pb buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "buf1M'' pb \<noteq> []"
          and "buf2M'' pb \<noteq> []"
          and "BHD pb buf1M'' = BHD pb buf2M''"
          and "pb \<notin> defaults"
        for pb :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BENQ pb (BHD pb buf1N) buf1N'))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (BTL pb buf1N)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "pb \<notin> defaults"
          and "buf1N pb \<noteq> []"
        for pb :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' (BENQ x1 (BHD x1 buf2M) buf2M')) (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf2M x1 \<noteq> []"
        for x1 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BENQ x2 (BHD x2 buf2N) buf2N') buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum (BTL x2 buf2N) buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf2N x2 \<noteq> []"
        for x2 :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ pc (BHD pc buf1M) buf1M') buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pc buf1M)) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "pc \<notin> defaults"
          and "buf1M pc \<noteq> []"
        for pc :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum (BTL pb buf1M') buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ pb (BHD pb buf1M') buf1M'') buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "buf1M' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' (BTL pb buf2M')) (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' (BENQ pb (BHD pb buf2M') buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "buf2M' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'm
        using that
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum (BTL pb buf2N') buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BENQ pb (BHD pb buf2N') buf2N'') buf1N''))))) op2'"
        if "buf2N' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'n
        using that
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' (BTL pb buf1N'))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' (BENQ pb (BHD pb buf1N') buf1N'')))))) op2'"
        if "buf1N' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'n
        using that
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb buf1M'') (BTL pb buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))) op2'"
        if "buf1M'' pb \<noteq> []"
          and "buf2M'' pb \<noteq> []"
          and "BHD pb buf1M'' \<noteq> BHD pb buf2M''"
          and "pb \<notin> defaults"
        for pb :: 'm
        using that
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply force
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum ((buf1M >> buf1M') >> buf1M'') ((buf2N >> buf2N') >> buf2N'')) (case_sum ((buf2M >> buf2M') >> buf2M'') ((buf1N >> buf1N') >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum (BTL pb buf2N'') (BTL pb buf1N'')))))) op2'"
        if "buf2N'' pb \<noteq> []"
          and "buf1N'' pb \<noteq> []"
          and "BHD pb buf2N'' \<noteq> BHD pb buf1N''"
          and "pb \<notin> defaults"
        for pb :: 'n
        using that
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply force
        done
      ultimately show ?thesis
        using H by (auto 0 0 elim !: step_aeq_op_elim step_map_op_elim step_split_op_cases step_transp_op_cases step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
    qed
  qed
qed


lemma A15:
  assumes "Qmn = (\<Q> :: (('m :: {countable,defaults} + 'n ::{countable,defaults}) + 'm + 'n, 'm + 'n, 'd) op)"
    and "Qm = (\<Q> :: ('m + 'm, 'm, 'd) op)"
    and "Qn =  (\<Q> :: ('n + 'n, 'n, 'd) op)"
    and "Imm = (\<I> :: ('m, 'm, 'd) op)"
    and "Inn = (\<I> :: ('n, 'n, 'd) op)"
    and "Xnm = (\<X> :: ('n + 'm, 'm + 'n, 'd) op)"
  shows "Qmn \<approx> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xnm) \<parallel> Inn) \<bullet> (Qm \<parallel> Qn)"
  using assms unfolding scomp_op_def pcomp_op_def using A15_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by auto

end