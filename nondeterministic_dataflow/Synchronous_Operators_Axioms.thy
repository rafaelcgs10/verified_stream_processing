\<comment> \<open>Axioms from Table 3 for equalitity test and acopy\<close>
theory Synchronous_Operators_Axioms

imports
  BNA_Operators
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom: A1: Equality test commutes with identity\<close>
lemma aeq_op_commutes_identity:
  "(\<Q> \<parallel> \<I>) \<bullet> \<Q> ~ map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>)"
  oops

  section \<open>Axiom: A2: Equality test transpose is equality test\<close>
lemma aeq_op_transp_op:
  "\<X> \<bullet> \<Q> \<approx> \<Q>"
  oops

  section \<open>Axiom: A3: Equality test dummy source and identity\<close>
lemma aeq_op_dummy_source_op:
  "map_op projr id (\<exclamdown> \<parallel> \<I>) \<bullet> \<Q> \<approx> \<I>"
  oops

  section \<open>Axiom: A4: Equality test to sink\<close>
lemma aeq_op_sink_op:
  "\<Q> \<bullet> ! ~ ! \<parallel> !"
  oops

  section \<open>Axiom: A5: Acopy to acopy and identity\<close>
lemma acopy_op_acopy_id:
  "\<C> \<bullet> (\<C> \<parallel> \<I>) ~ map_op id assoc (\<C> \<bullet> (\<I> \<parallel> \<C>))"
  oops

  section \<open>Axiom: A6: Acopy to transpose\<close>
lemma acopy_op_transp_op:
  "\<C> \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<C>"
  oops

  section \<open>Axiom: A7: Acopy to sink and identity\<close>
lemma acopy_op_acopy_sink:
  "map_op id projr (\<C> \<bullet> (! \<parallel> \<I>)) ~ \<I>"
  oops

  section \<open>Axiom: A8: Acopy dummy source\<close>

lemma acopy_op_dummy_source:
  \<open>\<exclamdown> \<bullet> \<C> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def
  apply (rule conjI)
  subgoal
    unfolding scomp_op_def pcomp_op_def
    apply (subst comp_op_code)
    apply (subst acopy_op_code)
    apply auto
    done
  subgoal
    apply (metis cempty_iff choices_pcomp_op_dummy_source step_choicesE)
    done
  done

section \<open>Axiom: A10: Equality test to acopy\<close>
lemma aeq_op_acopy:
  "\<Q> \<bullet> \<C> ~ (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q> \<parallel> \<Q>)"
  oops

  section \<open>Axiom: A11: Acopy to equality test\<close>

lemma acopy_op_aeq_op_id_op_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf buf) \<C> \<Q>) \<approx> id_op buf\<close>
  oops

lemma acopy_op_aeq:
  "\<C> \<bullet> \<Q> \<approx> \<I>"
  oops

  section \<open>Axiom A15: Transpose and equality test\<close>
lemma A15_gen:
  "(aeq_op (case_sum (case_sum (buf1M >> buf1M' >> buf1M'') (buf2N >> buf2N' >> buf2N'')) (case_sum (buf2M >> buf2M' >> buf2M'') (buf1N >> buf1N' >> buf1N''))) :: (('m :: {countable,defaults} + 'n ::{countable,defaults}) + 'm + 'n, 'm + 'n, 'd) op) \<approx>
   map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
   (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op (buf1N)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
proof (coinduction arbitrary: buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N'' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case 
    unfolding wsim_def
    sketch (intro allI impI conjI)
  proof (intro allI impI conjI)
    fix io :: "(('m + 'n) + 'm + 'n, 'm + 'n, 'd) IO"
      and op1' :: "(('m + 'n) + 'm + 'n, 'm + 'n, 'd) op"
    assume H: "step io (aeq_op (case_sum (case_sum (buf1M >> buf1M' >> buf1M'') (buf2N >> buf2N' >> buf2N'')) (case_sum (buf2M >> buf2M' >> buf2M'') (buf1N >> buf1N' >> buf1N'')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1M buf1M' buf1M'' buf1N buf1N' buf1N'' buf2M buf2M' buf2M'' buf2N buf2N' buf2N''. op1xx = aeq_op (case_sum (case_sum (buf1M >> buf1M' >> buf1M'') (buf2N >> buf2N' >> buf2N'')) (case_sum (buf2M >> buf2M' >> buf2M'') (buf1N >> buf1N' >> buf1N''))) \<and> op2xx = map_op projl projr (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1M) (transp_op (case_sum buf2N buf2M)))) (id_op buf1N))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))) op1' op2'"
      using H apply -
      explore (elim step_aeq_op_elim step_map_op_elim step_split_op_cases step_transp_op_cases step_comp_op_elim step_id_op_cases; simp split: sum.splits if_splits; hypsubst_thin?)
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
          using BISIM apply force+
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
        moreover have "step (Out (Inr (Inl x1)) (BHD x1 buf2M))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ x1 (BHD x1 buf1M) buf1M'') (BENQ x1 (BHD x1 buf2M) buf2M''))) (aeq_op (case_sum buf2N'' buf1N''))))
     (comp_op Some (case_sum (case_sum buf1M' buf2M') (case_sum buf2N' buf1N'))
       (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf1M)) (transp_op (case_sum buf2N (BTL x1 buf2M))))) (id_op buf1N)))
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1M'' buf2M'')) (aeq_op (case_sum buf2N'' buf1N''))))"
          using that by auto
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM apply force
          apply fast
          done
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
          using BISIM apply force
          apply force
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
          subgoal using prems by blast
          subgoal using prems by blast
          subgoal using prems by blast
          subgoal using prems by blast
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
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


lemma aeq_op_transp_aeq:
  assumes "Qmn = (\<Q> :: (('m :: {countable,defaults} + 'n ::{countable,defaults}) + 'm + 'n, 'm + 'n, 'd) op)"
    and "Qm = (\<Q> :: ('m + 'm, 'm, 'd) op)"
    and "Qn =  (\<Q> :: ('n + 'n, 'n, 'd) op)"
    and "Imm = (\<I> :: ('m, 'm, 'd) op)"
    and "Inn = (\<I> :: ('n, 'n, 'd) op)"
    and "Xnm = (\<X> :: ('n + 'm, 'm + 'n, 'd) op)"
  shows "Qmn \<approx> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xnm) \<parallel> Inn) \<bullet> (Qm \<parallel> Qn)"
  using assms unfolding scomp_op_def pcomp_op_def using A15_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by auto

section \<open>Axiom A19: Acopy and equality test\<close>
lemma acopy_op_transp_acopy:
  assumes "Cmn \<equiv> \<C> :: ('m + 'n,('m :: countable + 'n ::countable) + 'm + 'n,  'd) op"
    and "Cm \<equiv> \<C> :: ('m, 'm + 'm, 'd) op"
    and "Cn \<equiv> \<C> :: ('n, 'n + 'n, 'd) op"
    and "Imm \<equiv> \<I> :: ('m, 'm, 'd) op"
    and "Inn \<equiv> \<I> :: ('n, 'n, 'd) op"
    and "Xmn \<equiv> \<X> :: ('m + 'n, 'n + 'm, 'd) op"
  shows "Cmn \<approx> (Cm \<parallel> Cn) \<bullet> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xmn) \<parallel> Inn)"
  oops

  section \<open>Axiom F3: Loop equality test\<close>
lemma loop_op_aeq_sink:
  "map_op id Inr \<Q>\<up> ~ !"
  oops

  section \<open>Axiom F4: Loop acopy\<close>
lemma loop_op_acopy_dummy_source:
  "map_op Inr id \<C>\<up> ~ \<exclamdown>"
  oops

end