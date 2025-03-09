theory A19

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)


section \<open>Axiom A19: Acopy and equality test\<close>
lemma A19_gen:
  "(acopy_op (case_sum (case_sum (bufML >> bufML' >> bufML'') (bufNL >> bufNL' >> bufNL'')) (case_sum (bufMR >> bufMR' >> bufMR'') (bufNR >> bufNR' >> bufNR''))) :: ('m + 'n,('m :: {countable,defaults} + 'n ::{countable,defaults}) + 'm + 'n, 'd) op) \<approx>
   map_op projl projr
   (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
   (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
proof -
  define R:: "('m :: {countable,defaults} + 'n :: {countable,defaults}, ('m + 'n) + 'm + 'n, 'd) op \<Rightarrow> ('m + 'n, ('m + 'n) + 'm + 'n, 'd) op \<Rightarrow> bool" where 
    "R = (\<lambda>op1xx op2xx.
        \<exists>bufML bufML' bufML'' bufMR bufMR' bufMR'' bufNL bufNL' bufNL'' bufNR bufNR' bufNR''.
           op1xx = acopy_op (case_sum (case_sum (bufML >> bufML' >> bufML'') (bufNL >> bufNL' >> bufNL'')) (case_sum (bufMR >> bufMR' >> bufMR'') (bufNR >> bufNR' >> bufNR''))) \<and>
           op2xx =
           map_op projl projr
            (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
              (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
  show ?thesis
  proof (coinduction arbitrary: bufML bufML' bufML'' bufMR bufMR' bufMR'' bufNL bufNL' bufNL'' bufNR bufNR' bufNR'' rule: wbisim_coinduct_upto'')
    case SIM1
    then show ?case 
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (BENQ p x (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL''))) (BENQ p x (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR''))))) op2'"
        if "p \<notin> defaults"
        for p :: "'m + 'n"
          and x :: 'd
        using that 
      proof (cases p)
        case (Inl a)
        from this that show ?thesis unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      next
        case (Inr b)
        from this that show ?thesis unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inl x1)) (BHD x1 bufML)) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((BTL x1 bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x1 \<notin> defaults"
          and "bufML x1 \<noteq> []"
          and "bufML'' x1 = []"
          and "bufML' x1 = []"
        for x1 :: 'm
        using that
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))
     (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 bufML) bufML') bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BTL x1 bufML) bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by force
        also have "step Tau \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BTL x1 bufML) bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1 (BHD x1 bufML) bufML'')) (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by fastforce
        also have "step (Out (Inr (Inl (Inl x1))) (BHD x1 bufML))  \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BTL x1 bufML) bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by fastforce
        finally show ?thesis
          unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inl x1)) (BHD x1 bufML')) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> BTL x1 bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x1 \<notin> defaults"
          and "bufML'' x1 = []"
          and "bufML' x1 \<noteq> []"
        for x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))
     (comp_op Some (case_sum (case_sum (BTL x1 bufML') bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1 (BHD x1 bufML') bufML'')) (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by fastforce
        also have "step (Out (Inr (Inl (Inl x1))) (BHD x1 bufML')) \<dots>
     (comp_op Some (case_sum (case_sum (BTL x1 bufML') bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by fastforce
        finally show ?thesis
          unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inl x1)) (BHD x1 bufML'')) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> BTL x1 bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x1 \<notin> defaults"
          and "bufML'' x1 \<noteq> []"
        for x1 :: 'm
        using that 
        unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      moreover have "\<exists>op2'. wstep (Out (Inl (Inr x2)) (BHD x2 bufNL)) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((BTL x2 bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x2 \<notin> defaults"
          and "bufNL x2 \<noteq> []"
          and "bufNL'' x2 = []"
          and "bufNL' x2 = []"
        for x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum (BENQ x2 (BHD x2 bufNL) bufNL') bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum (BTL x2 bufNL) bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by fastforce
        also have "step Tau \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum (BTL x2 bufNL) bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' (BENQ x2 (BHD x2 bufNL) bufNL''))))) (id_op bufNR''))))"
          using that by fastforce
        also have "step (Out (Inr (Inl (Inr x2))) (BHD x2 bufNL)) \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum (BTL x2 bufNL) bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          apply (rule step_comp_op_R_Out)
          apply (rule step_map_op)
          apply (rule step_comp_op_L_Out)
          apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
          using that apply auto
          done
        finally show ?thesis
          unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inr x2)) (BHD x2 bufNL')) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> BTL x2 bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x2 \<notin> defaults"
          and "bufNL'' x2 = []"
          and "bufNL' x2 \<noteq> []"
        for x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum (BTL x2 bufNL') bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' (BENQ x2 (BHD x2 bufNL') bufNL''))))) (id_op bufNR''))))"
          using that by fastforce
        also have "step (Out (Inr (Inl (Inr x2))) (BHD x2 bufNL')) \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum (BTL x2 bufNL') bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          apply (rule step_comp_op_R_Out)
          apply (rule step_map_op)
          apply (rule step_comp_op_L_Out)
          apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
          using that apply auto
          done
        finally show ?thesis
          unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl (Inr x2)) (BHD x2 bufNL'')) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> BTL x2 bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x2 \<notin> defaults"
          and "bufNL'' x2 \<noteq> []"
        for x2 :: 'n
        using that 
        unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, (force del: step_wstep intro!: step_wstep))
      moreover have "\<exists>op2'. wstep (Out (Inr (Inl x1)) (BHD x1 bufMR)) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((BTL x1 bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x1 \<notin> defaults"
          and "bufMR x1 \<noteq> []"
          and "bufMR'' x1 = []"
          and "bufMR' x1 = []"
        for x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))
     (comp_op Some (case_sum (case_sum bufML' (BENQ x1 (BHD x1 bufMR) bufMR')) (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML (BTL x1 bufMR))) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by force
        also have "step Tau \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML (BTL x1 bufMR))) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum (BENQ x1 (BHD x1 bufMR) bufMR'') bufNL'')))) (id_op bufNR''))))"
          using that by force
        also have "step (Out (Inr (Inr (Inl x1))) (BHD x1 bufMR)) \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML (BTL x1 bufMR))) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          apply (rule step_comp_op_R_Out)
          apply (rule step_map_op)
          apply (rule step_comp_op_L_Out)
          apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
          using that apply auto
          done
        finally show ?thesis
          unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr (Inl x1)) (BHD x1 bufMR')) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> BTL x1 bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x1 \<notin> defaults"
          and "bufMR'' x1 = []"
          and "bufMR' x1 \<noteq> []"
        for x1 :: 'm
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))
     (comp_op Some (case_sum (case_sum bufML' (BTL x1 bufMR')) (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum (BENQ x1 (BHD x1 bufMR') bufMR'') bufNL'')))) (id_op bufNR''))))"
          using that by force
        also have "step (Out (Inr (Inr (Inl x1))) (BHD x1 bufMR')) \<dots>
     (comp_op Some (case_sum (case_sum bufML' (BTL x1 bufMR')) (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          apply (rule step_comp_op_R_Out)
          apply (rule step_map_op)
          apply (rule step_comp_op_L_Out)
          apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
          using that apply auto
          done
        finally show ?thesis
          unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr (Inl x1)) (BHD x1 bufMR'')) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> BTL x1 bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x1 \<notin> defaults"
          and "bufMR'' x1 \<noteq> []"
        for x1 :: 'm
        using that 
        unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      moreover have "\<exists>op2'. wstep (Out (Inr (Inr x2)) (BHD x2 bufNR)) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((BTL x2 bufNR >> bufNR') >> bufNR'')))) op2'"
        if "x2 \<notin> defaults"
          and "bufNR x2 \<noteq> []"
          and "bufNR'' x2 = []"
          and "bufNR' x2 = []"
        for x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' (BENQ x2 (BHD x2 bufNR) bufNR'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL (BTL x2 bufNR))))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by fastforce
        also have "step Tau \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL (BTL x2 bufNR))))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op (BENQ x2 (BHD x2 bufNR) bufNR'')))))"
          using that by fastforce
        also have "step (Out (Inr (Inr (Inr x2))) (BHD x2 bufNR)) \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL (BTL x2 bufNR))))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by force
        finally show ?thesis
          unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr (Inr x2)) (BHD x2 bufNR')) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> BTL x2 bufNR') >> bufNR'')))) op2'"
        if "x2 \<notin> defaults"
          and "bufNR'' x2 = []"
          and "bufNR' x2 \<noteq> []"
        for x2 :: 'n
        using that 
      proof -
        have "step Tau
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' (BTL x2 bufNR'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op (BENQ x2 (BHD x2 bufNR') bufNR'')))))"
          using that by fastforce
        also have "step (Out (Inr (Inr (Inr x2))) (BHD x2 bufNR')) \<dots>
     (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' (BTL x2 bufNR'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR)))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))"
          using that by force
        finally show ?thesis
          unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr (Inr x2)) (BHD x2 bufNR'')) (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR''))))) op2' \<and> wbisim_cong R (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> BTL x2 bufNR'')))) op2'"
        if "x2 \<notin> defaults"
          and "bufNR'' x2 \<noteq> []"
        for x2 :: 'n
        using that 
        unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      ultimately show ?thesis
        using SIM1 unfolding R_def[symmetric] by (elim step_transp_op_cases step_id_op_cases step_acopy_op_elim step_map_op_elim step_comp_op_elim exE conjE; clarsimp split: if_splits sum.splits)
    qed
  next
    case SIM2
    then show ?case 
    proof -
      have "\<exists>op2'. wstep (Inp (Inl pa) x) (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BENQ pa x bufML) (BENQ pa x bufMR))) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
        if "pa \<notin> defaults"
        for x :: 'd
          and pa :: 'm
        using that unfolding R_def by force
      moreover have "\<exists>op2'. wstep (Inp (Inr pa) x) (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum (BENQ pa x bufNL) (BENQ pa x bufNR)))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
        if "pa \<notin> defaults"
        for x :: 'd
          and pa :: 'n
        using that unfolding R_def by force
      moreover have "\<exists>op2'. wstep (Out (Inr (Inr pa)) (BHD pa bufNR'')) (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op (BTL pa bufNR''))))))"
        if "pa \<notin> defaults"
          and "bufNR'' pa \<noteq> []"
        for pa :: 'n
        using that unfolding R_def by force
      moreover have "\<exists>op2'. wstep (Out (Inl (Inr x1a)) (BHD x1a bufNL'')) (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' (BTL x1a bufNL''))))) (id_op bufNR'')))))"
        if "x1a \<notin> defaults"
          and "bufNL'' x1a \<noteq> []"
        for x1a :: 'n
        using that unfolding R_def by force
      moreover have "\<exists>op2'. wstep (Out (Inr (Inl x2)) (BHD x2 bufMR'')) (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum (BTL x2 bufMR'') bufNL'')))) (id_op bufNR'')))))"
        if "x2 \<notin> defaults"
          and "bufMR'' x2 \<noteq> []"
        for x2 :: 'm
        using that unfolding R_def by force
      moreover have "\<exists>op2'. wstep (Out (Inl (Inl pb)) (BHD pb bufML'')) (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pb bufML'')) (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
        if "pb \<notin> defaults"
          and "bufML'' pb \<noteq> []"
        for pb :: 'm
        using that unfolding R_def by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum (BENQ pb (BHD pb bufNL) bufNL') bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum (BTL pb bufNL) bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
        if "bufNL pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'n
        using that unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' (BENQ pb (BHD pb bufNR) bufNR'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL (BTL pb bufNR)))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
        if "bufNR pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'n
        using that unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ pb (BHD pb bufML) bufML') bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BTL pb bufML) bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
        if "bufML pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'm
        using that unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' (BENQ pb (BHD pb bufMR) bufMR')) (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML (BTL pb bufMR))) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
        if "bufMR pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'm
        using that unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1b bufML') bufMR') (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1b (BHD x1b bufML') bufML'')) (transp_op (case_sum bufMR'' bufNL'')))) (id_op bufNR'')))))"
        if "x1b \<notin> defaults"
          and "bufML' x1b \<noteq> []"
        for x1b :: 'm
        using that unfolding R_def
        apply (intro exI conjI[rotated,OF wbc_base])
        apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' (BTL x2 bufMR')) (case_sum bufNL' bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum (BENQ x2 (BHD x2 bufMR') bufMR'') bufNL'')))) (id_op bufNR'')))))"
        if "x2 \<notin> defaults"
          and "bufMR' x2 \<noteq> []"
        for x2 :: 'm
        using that unfolding R_def
        apply (intro exI conjI[rotated,OF wbc_base])
        apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum (BTL x1 bufNL') bufNR')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' (BENQ x1 (BHD x1 bufNL') bufNL''))))) (id_op bufNR'')))))"
        if "x1 \<notin> defaults"
          and "bufNL' x1 \<noteq> []"
        for x1 :: 'n
        using that unfolding R_def
        apply (intro exI conjI[rotated,OF wbc_base])
        apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum (case_sum ((bufML >> bufML') >> bufML'') ((bufNL >> bufNL') >> bufNL'')) (case_sum ((bufMR >> bufMR') >> bufMR'') ((bufNR >> bufNR') >> bufNR'')))) op2' \<and> wbisim_cong R op2' (map_op projl projr (comp_op Some (case_sum (case_sum bufML' bufMR') (case_sum bufNL' (BTL x2a bufNR'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum bufML bufMR)) (acopy_op (case_sum bufNL bufNR))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op bufML'') (transp_op (case_sum bufMR'' bufNL'')))) (id_op (BENQ x2a (BHD x2a bufNR') bufNR''))))))"
        if "x2a \<notin> defaults"
          and "bufNR' x2a \<noteq> []"
        for x2a :: 'n
        using that unfolding R_def
        apply (intro exI conjI[rotated,OF wbc_base])
        apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      ultimately show ?thesis
        apply -
        subgoal premises prems
          using SIM2 apply -
          unfolding R_def[symmetric] 
          apply (elim step_transp_op_cases step_id_op_cases step_acopy_op_elim step_map_op_elim step_comp_op_elim exE conjE; clarsimp split: if_splits sum.splits ; hypsubst_thin?)
          apply (rule prems; assumption)+
          done
        done
    qed
  qed
qed

lemma A19:
  assumes "Cmn = (\<C> :: ('m + 'n,('m :: {countable,defaults} + 'n ::{countable,defaults}) + 'm + 'n,  'd) op)"
    and "Cm = (\<C> :: ('m, 'm + 'm, 'd) op)"
    and "Cn = (\<C> :: ('n, 'n + 'n, 'd) op)"
    and "Imm = (\<I> :: ('m, 'm, 'd) op)"
    and "Inn = (\<I> :: ('n, 'n, 'd) op)"
    and "Xmn = (\<X> :: ('m + 'n, 'n + 'm, 'd) op)"
  shows "Cmn \<approx> (Cm \<parallel> Cn) \<bullet> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xmn) \<parallel> Inn)"
  using assms apply hypsubst_thin
  unfolding scomp_op_def pcomp_op_def
  using A19_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by simp

end