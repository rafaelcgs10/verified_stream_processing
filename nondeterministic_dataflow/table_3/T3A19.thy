theory T3A19

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A19\<close>
lemma A19_gen:
  "(split_op (case_sum (case_sum (buf1L >> buf1L' >> buf1L'') (buf2L >> buf2L' >> buf2L'')) (case_sum (buf1R >> buf1R' >> buf1R'') (buf2R >> buf2R' >> buf2R''))) :: ('m + 'n :: {countable, defaults},('m :: {countable, defaults} + 'n) + 'm + 'n,  'd) op) \<approx>
   map_op projl projr
   (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
   (map_op BNA_Operators.reassoc BNA_Operators.reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
   (map_op BNA_Operators.assoc BNA_Operators.assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
proof (coinduction arbitrary: buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R'' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case 
    unfolding wsim_def
  proof (intro allI conjI allI impI)
    fix io :: "('m + 'n, ('m + 'n) + 'm + 'n, 'd) IO"
      and op1' :: "('m + 'n, ('m + 'n) + 'm + 'n, 'd) op"
    assume H: "step io (split_op (case_sum (case_sum (buf1L >> buf1L' >> buf1L'') (buf2L >> buf2L' >> buf2L'')) (case_sum (buf1R >> buf1R' >> buf1R'') (buf2R >> buf2R' >> buf2R'')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum (buf1L >> buf1L' >> buf1L'') (buf2L >> buf2L' >> buf2L'')) (case_sum (buf1R >> buf1R' >> buf1R'') (buf2R >> buf2R' >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (BENQ p x (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L''))) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "p \<notin> defaults"
        for p :: "'m + 'n"
          and x :: 'd
        using that 
      proof (cases p)
        case (Inl a)
        from this that show ?thesis by force
      next
        case (Inr b)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force+
          done
      qed
      moreover have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (BENQ p x (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))))) op2'"
        if "p \<notin> defaults"
        for p :: "'m + 'n"
          and x :: 'd
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
      moreover have "\<exists>op2'. wstep (Out (Inl (Inl x1a)) (BHD x1a buf1L)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((BTL x1a buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x1a \<notin> defaults"
          and "buf1L x1a \<noteq> []"
          and "buf1L'' x1a = []"
          and "buf1L' x1a = []"
        for x1a :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum (BENQ x1a (BHD x1a buf1L) buf1L') buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum (BTL x1a buf1L) buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that apply -
          apply (rule step_Tau_comp_op_L)
             apply simp_all
           apply (rule step_comp_op_L_Out)
              apply (rule step_split_op_Write[where p="Inl x1a"])
                 apply auto
          done
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum (BENQ x1a (BHD x1a buf1L) buf1L') buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum (BTL x1a buf1L) buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum (BTL x1a buf1L) buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1a (BHD x1a buf1L) buf1L'')) (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that apply -
          apply (rule step_Tau_comp_op_R)
               apply fastforce
              apply auto
          done
        moreover have "step (Out (Inr (Inl (Inl x1a))) (BHD x1a buf1L))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum (BTL x1a buf1L) buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1a (BHD x1a buf1L) buf1L'')) (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum (BTL x1a buf1L) buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that apply -
          apply (rule step_comp_op_R_Out)
            apply fastforce
           apply auto
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inl x1a)) (BHD x1a buf1L')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> BTL x1a buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x1a \<notin> defaults"
          and "buf1L'' x1a = []"
          and "buf1L' x1a \<noteq> []"
        for x1a :: 'm
        using that 
      proof -
have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum (BTL x1a buf1L') buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1a (BHD x1a buf1L') buf1L'')) (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
  using that apply -
          apply (rule step_Tau_comp_op_R)
               apply fastforce
              apply auto
  done
     moreover have "step (Out (Inr (Inl (Inl x1a))) (BHD x1a buf1L'))
     (comp_op Some (case_sum (case_sum (BTL x1a buf1L') buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1a (BHD x1a buf1L') buf1L'')) (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum (BTL x1a buf1L') buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that apply -
          apply (rule step_comp_op_R_Out)
            apply fastforce
           apply auto
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inl x1a)) (BHD x1a buf1L'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> BTL x1a buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x1a \<notin> defaults"
          and "buf1L'' x1a \<noteq> []"
        for x1a :: 'm
        using that 
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply (force del: step_wstep intro!: step_wstep)
          done
      moreover have "\<exists>op2'. wstep (Out (Inl (Inr x2)) (BHD x2 buf2L)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((BTL x2 buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x2 \<notin> defaults"
          and "buf2L x2 \<noteq> []"
          and "buf2L'' x2 = []"
          and "buf2L' x2 = []"
        for x2 :: 'n
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum (BENQ x2 (BHD x2 buf2L) buf2L') buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum (BTL x2 buf2L) buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that apply -
          apply (rule step_Tau_comp_op_L)
             apply simp_all
           apply force
          apply auto
          done
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum (BENQ x2 (BHD x2 buf2L) buf2L') buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum (BTL x2 buf2L) buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum (BTL x2 buf2L) buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' (BENQ x2 (BHD x2 buf2L) buf2L''))))) (id_op buf2R''))))"
          using that apply -
          apply (rule step_Tau_comp_op_R[where p="Inr (Inl x2)"])
          apply force
              apply auto
          done
   moreover have "step (Out (Inr (Inl (Inr x2))) (BHD x2 buf2L))
(comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum (BTL x2 buf2L) buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' (BENQ x2 (BHD x2 buf2L) buf2L''))))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum (BTL x2 buf2L) buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
      using that apply -
      apply (rule step_comp_op_R_Out)
        apply simp_all
      apply (rule step_map_op)
      apply (rule step_comp_op_L_Out)
      apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
             apply auto[1]
            apply auto
      done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inr x2)) (BHD x2 buf2L')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> BTL x2 buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x2 \<notin> defaults"
          and "buf2L'' x2 = []"
          and "buf2L' x2 \<noteq> []"
        for x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum (BTL x2 buf2L') buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' (BENQ x2 (BHD x2 buf2L') buf2L''))))) (id_op buf2R''))))"
          using that apply -
          apply (rule step_Tau_comp_op_R[where p="Inr (Inl x2)"])
          apply force
              apply auto
          done
        moreover have "step (Out (Inr (Inl (Inr x2))) (BHD x2 buf2L'))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum (BTL x2 buf2L') buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' (BENQ x2 (BHD x2 buf2L') buf2L''))))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum (BTL x2 buf2L') buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that apply -
           apply (rule step_comp_op_R_Out)
        apply simp_all
      apply (rule step_map_op)
      apply (rule step_comp_op_L_Out)
      apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
             apply auto[1]
                apply auto
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inr x2)) (BHD x2 buf2L'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> BTL x2 buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x2 \<notin> defaults"
          and "buf2L'' x2 \<noteq> []"
        for x2 :: 'n
        using that 
         apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply force
        apply auto
        done
      moreover have "\<exists>op2'. wstep (Out (Inr (Inl x1)) (BHD x1 buf1R)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((BTL x1 buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1R x1 \<noteq> []"
          and "buf1R'' x1 = []"
          and "buf1R' x1 = []"
        for x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' (BENQ x1 (BHD x1 buf1R) buf1R')) (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L (BTL x1 buf1R))) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that apply -
          apply (rule step_Tau_comp_op_L)
             apply (rule step_comp_op_L_Out)
                apply force
               apply auto
          done
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' (BENQ x1 (BHD x1 buf1R) buf1R')) (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L (BTL x1 buf1R))) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L (BTL x1 buf1R))) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum (BENQ x1 (BHD x1 buf1R) buf1R'') buf2L'')))) (id_op buf2R''))))"
          using that by fastforce
      moreover have "step (Out (Inr (Inr (Inl x1))) (BHD x1 buf1R))
(comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L (BTL x1 buf1R))) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum (BENQ x1 (BHD x1 buf1R) buf1R'') buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L (BTL x1 buf1R))) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
        using that apply -
        apply (rule step_comp_op_R_Out)
        apply simp_all
      apply (rule step_map_op)
      apply (rule step_comp_op_L_Out)
      apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
             apply auto[1]
        apply auto
        done
      ultimately show ?thesis
           apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr (Inl x1)) (BHD x1 buf1R')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> BTL x1 buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1R'' x1 = []"
          and "buf1R' x1 \<noteq> []"
        for x1 :: 'm
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' (BTL x1 buf1R')) (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum (BENQ x1 (BHD x1 buf1R') buf1R'') buf2L'')))) (id_op buf2R''))))"
          using that by fastforce
        moreover have "step (Out (Inr (Inr (Inl x1))) (BHD x1 buf1R'))
     (comp_op Some (case_sum (case_sum buf1L' (BTL x1 buf1R')) (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum (BENQ x1 (BHD x1 buf1R') buf1R'') buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' (BTL x1 buf1R')) (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that apply -
        apply (rule step_comp_op_R_Out)
        apply simp_all
      apply (rule step_map_op)
      apply (rule step_comp_op_L_Out)
      apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
             apply auto[1]
                apply auto
          done
      ultimately show ?thesis
           apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr (Inl x1)) (BHD x1 buf1R'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> BTL x1 buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1R'' x1 \<noteq> []"
        for x1 :: 'm
        using that 
      apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply (force del: step_wstep intro!: step_wstep)
        done
      moreover have "\<exists>op2'. wstep (Out (Inr (Inr x2a)) (BHD x2a buf2R)) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((BTL x2a buf2R >> buf2R') >> buf2R'')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2R x2a \<noteq> []"
          and "buf2R'' x2a = []"
          and "buf2R' x2a = []"
        for x2a :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' (BENQ x2a (BHD x2a buf2R) buf2R'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L (BTL x2a buf2R))))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that by force
        moreover have "step Tau
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' (BENQ x2a (BHD x2a buf2R) buf2R'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L (BTL x2a buf2R))))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L (BTL x2a buf2R))))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op (BENQ x2a (BHD x2a buf2R) buf2R'')))))"
          using that by fastforce
        moreover have "step (Out (Inr (Inr (Inr x2a))) (BHD x2a buf2R))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L (BTL x2a buf2R))))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op (BENQ x2a (BHD x2a buf2R) buf2R'')))))
     (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L (BTL x2a buf2R))))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))"
          using that by force
     ultimately show ?thesis
           apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply force
          done
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr (Inr x2a)) (BHD x2a buf2R')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> BTL x2a buf2R') >> buf2R'')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2R'' x2a = []"
          and "buf2R' x2a \<noteq> []"
        for x2a :: 'n
        using that 
          apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Out (Inr (Inr x2a)) (BHD x2a buf2R'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> BTL x2a buf2R'')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2R'' x2a \<noteq> []"
        for x2a :: 'n
        using that 
          apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply (force del: step_wstep intro!: step_wstep)
        done
        ultimately show ?thesis
        using H  by (auto 0 0 elim!: step_split_op_cases step_transp_op_cases step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
    qed
  next
    fix io :: "('m + 'n, ('m + 'n) + 'm + 'n, 'd) IO"
      and op1' :: "('m + 'n, ('m + 'n) + 'm + 'n, 'd) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op1'"
    show "\<exists>op2'. wstep io (split_op (case_sum (case_sum (buf1L >> buf1L' >> buf1L'') (buf2L >> buf2L' >> buf2L'')) (case_sum (buf1R >> buf1R' >> buf1R'') (buf2R >> buf2R' >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum (buf1L >> buf1L' >> buf1L'') (buf2L >> buf2L' >> buf2L'')) (case_sum (buf1R >> buf1R' >> buf1R'') (buf2R >> buf2R' >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl pb) xb) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum (BENQ pb xb buf1L) buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'm
          and xb :: 'd
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Inp (Inl pb) xb) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L (BENQ pb xb buf1R))) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'm
          and xb :: 'd
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done      moreover have "\<exists>op2'. wstep (Inp (Inr pb) xb) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum (BENQ pb xb buf2L) buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'n
          and xb :: 'd
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Inp (Inr pb) xb) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L (BENQ pb xb buf2R)))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'n
          and xb :: 'd
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Out (Inr (Inr pb)) (BHD pb buf2R'')) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op (BTL pb buf2R'')))))) op2'"
        if "pb \<notin> defaults"
          and "buf2R'' pb \<noteq> []"
        for pb :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Out (Inl (Inr x1)) (BHD x1 buf2L'')) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' (BTL x1 buf2L''))))) (id_op buf2R''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf2L'' x1 \<noteq> []"
        for x1 :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Out (Inr (Inl x2)) (BHD x2 buf1R'')) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum (BTL x2 buf1R'') buf2L'')))) (id_op buf2R''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf1R'' x2 \<noteq> []"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. wstep (Out (Inl (Inl pc)) (BHD pc buf1L'')) (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pc buf1L'')) (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "pc \<notin> defaults"
          and "buf1L'' pc \<noteq> []"
        for pc :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum (BENQ x1 (BHD x1 buf2L) buf2L') buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum (BTL x1 buf2L) buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf2L x1 \<noteq> []"
        for x1 :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' (BENQ x2 (BHD x2 buf2R) buf2R'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L (BTL x2 buf2R)))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf2R x2 \<noteq> []"
        for x2 :: 'n
        using that
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1L) buf1L') buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum (BTL x1 buf1L) buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf1L x1 \<noteq> []"
        for x1 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' (BENQ x2 (BHD x2 buf1R) buf1R')) (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L (BTL x2 buf1R))) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf1R x2 \<noteq> []"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply fastforce
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1b buf1L') buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1b (BHD x1b buf1L') buf1L'')) (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) op2'"
        if "x1b \<notin> defaults"
          and "buf1L' x1b \<noteq> []"
        for x1b :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)     
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' (BTL x2 buf1R')) (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum (BENQ x2 (BHD x2 buf1R') buf1R'') buf2L'')))) (id_op buf2R''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf1R' x2 \<noteq> []"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)     
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum (BTL x1 buf2L') buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' (BENQ x1 (BHD x1 buf2L') buf2L''))))) (id_op buf2R''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf2L' x1 \<noteq> []"
        for x1 :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)     
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf1L' buf1L'' buf2L buf2L' buf2L'' buf1R buf1R' buf1R'' buf2R buf2R' buf2R''. op1xx = split_op (case_sum (case_sum ((buf1L >> buf1L') >> buf1L'') ((buf2L >> buf2L') >> buf2L'')) (case_sum ((buf1R >> buf1R') >> buf1R'') ((buf2R >> buf2R') >> buf2R''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' buf2R')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op buf2R''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf1L' buf1R') (case_sum buf2L' (BTL x2a buf2R'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (split_op (case_sum buf1L buf1R)) (split_op (case_sum buf2L buf2R))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1L'') (transp_op (case_sum buf1R'' buf2L'')))) (id_op (BENQ x2a (BHD x2a buf2R') buf2R'')))))) op2'"
        if "x2a \<notin> defaults"
          and "buf2R' x2a \<noteq> []"
        for x2a :: 'n
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)     
        done
      ultimately show ?thesis
        apply -
        subgoal premises prems
          using H by (auto 0 0 simp: prems elim !: step_map_op_elim step_split_op_cases step_transp_op_cases step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
        done
    qed
  qed
qed

lemma A19:
  assumes "Smn = (\<Lambda> :: ('m + 'n,('m :: {countable, defaults}+ 'n :: {countable, defaults}) + 'm + 'n,  'd) op)"
    and "Sm = (\<Lambda> :: ('m, 'm + 'm, 'd) op)"
    and "Sn = (\<Lambda> :: ('n, 'n + 'n, 'd) op)"
    and "Imm = (\<I> :: ('m, 'm, 'd) op)"
    and "Inn = (\<I> :: ('n, 'n, 'd) op)"
    and "Xmn = (\<X> :: ('m + 'n, 'n + 'm, 'd) op)"
  shows "Smn \<approx> (Sm \<parallel> Sn) \<bullet> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xmn) \<parallel> Inn)"
  unfolding scomp_op_def pcomp_op_def
  using assms A19_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by simp

end