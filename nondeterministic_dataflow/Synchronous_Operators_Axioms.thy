\<comment> \<open>Axioms from Table 3 for equalitity test and acopy\<close>
theory Synchronous_Operators_Axioms

imports
  BNA_Operators
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A1: Equality test commutes with identity\<close>

lemma A1_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2') (aeq_op (case_sum buf1 buf1') \<parallel> id_op buf1'') (aeq_op (case_sum buf3 buf3')))
  ~ map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (id_op buf1'' \<parallel> aeq_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3' buf3))))\<close>
proof (coinduction arbitrary: buf1 buf1' buf1'' buf2 buf2' buf3 buf3' rule: bisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding sim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "(('a + 'a) + 'a, 'a, 'b) IO"
      and op1' :: "(('a + 'a) + 'a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op1'"
    show "\<exists>op2'. step io (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (Inl (Inl pb)) y) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ pb y buf1) buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'a
          and y :: 'b
        using that by (fastforce intro: bc_base)
      moreover have "\<exists>op2'. step (Inp (Inl (Inr pb)) y) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 (BENQ pb y buf1'))) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'a
          and y :: 'b
        using that by (fastforce intro: bc_base)
      moreover have "\<exists>op2'. step (Inp (Inr pb) xb) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op (BENQ pb xb buf1''))) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'a
          and xb :: 'b
        using that by (fastforce intro: bc_base)
      moreover have "\<exists>op2'. step (Out pa (BHD pa buf3')) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
        if "buf3 pa \<noteq> []"
          and "buf3' pa \<noteq> []"
          and "BHD pa buf3 = BHD pa buf3'"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce intro: bc_base)
      moreover have "\<exists>op2'. step Tau (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pb (BHD pb buf1'') buf2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op (BTL pb buf1''))) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "pb \<notin> defaults"
          and "buf1'' pb \<noteq> []"
        for pb :: 'a
        using that by (fastforce intro: bc_base)
      moreover have "\<exists>op2'. step Tau (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb buf1') buf2) buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb buf1) (BTL pb buf1'))) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "buf1 pb \<noteq> []"
          and "buf1' pb \<noteq> []"
          and "BHD pb buf1 = BHD pb buf1'"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that by (fastforce intro: bc_base)
      moreover have "\<exists>op2'. step Tau (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum (BENQ pa (BHD pa buf2) buf3) buf3')))) op2'"
        if "buf2 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce intro: bc_base)
      moreover have "\<exists>op2'. step Tau (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa buf2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 (BENQ pa (BHD pa buf2') buf3'))))) op2'"
        if "buf2' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce intro: bc_base)
      moreover have "\<exists>op2'. step Tau (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb buf1) (BTL pb buf1'))) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "buf1 pb \<noteq> []"
          and "buf1' pb \<noteq> []"
          and "BHD pb buf1 \<noteq> BHD pb buf1'"
          and "pb \<notin> defaults"
        for pb :: 'a
      proof -
        have \<open>step Tau
       (comp_op Some (case_sum buf2' buf2)
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1')))
         (aeq_op (case_sum buf3' buf3)))
       (comp_op Some (case_sum buf2' buf2)
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'')
           (aeq_op (case_sum (BTL pb buf1) (BTL pb buf1'))))
         (aeq_op (case_sum buf3' buf3))) \<close>
          using that by fastforce
        thus ?thesis by (fastforce intro: bc_base)
      qed
      moreover have "\<exists>op2'. step Tau (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
        if "buf3 pa \<noteq> []"
          and "buf3' pa \<noteq> []"
          and "BHD pa buf3 \<noteq> BHD pa buf3'"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (intro exI conjI[rotated, OF bc_base], auto)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_id_op_cases)
    qed
  next
    fix io :: "(('a + 'a) + 'a, 'a, 'b) IO"
      and op1' :: "(('a + 'a) + 'a, 'a, 'b) op"
    assume H: "step io (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op1'"
    show "\<exists>op2'. step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (Inr pb) xb) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pb xb buf1'')) (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'a
          and xb :: 'b
        using that by (fastforce intro: bc_sym[OF bc_base])
      moreover have "\<exists>op2'. step (Inp (Inl (Inl pb)) y) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum (BENQ pb y buf1) buf1'))) (aeq_op (case_sum buf3' buf3))))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'a
          and y :: 'b
        using that by (fastforce intro: bc_sym[OF bc_base])
      moreover have "\<exists>op2'. step (Inp (Inl (Inr pb)) y) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 (BENQ pb y buf1')))) (aeq_op (case_sum buf3' buf3))))) op2'"
        if "pb \<notin> defaults"
        for pb :: 'a
          and y :: 'b
        using that by (fastforce intro: bc_sym[OF bc_base])
      moreover have "\<exists>op2'. step (Out pa (BHD pa buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum (BTL pa buf3') (BTL pa buf3)))))) op2'"
        if "buf3' pa \<noteq> []"
          and "buf3 pa \<noteq> []"
          and "BHD pa buf3' = BHD pa buf3"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce intro: bc_sym[OF bc_base])
      moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' (BENQ pb (BHD pb buf1') buf2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum (BTL pb buf1) (BTL pb buf1')))) (aeq_op (case_sum buf3' buf3))))) op2'"
        if "buf1 pb \<noteq> []"
          and "buf1' pb \<noteq> []"
          and "BHD pb buf1 = BHD pb buf1'"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that by (fastforce intro: bc_sym[OF bc_base])
      moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb buf1'') buf2') buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pb buf1'')) (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2'"
        if "pb \<notin> defaults"
          and "buf1'' pb \<noteq> []"
        for pb :: 'a
        using that by (fastforce intro: bc_sym[OF bc_base])
      moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum (BTL pa buf2') buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum (BENQ pa (BHD pa buf2') buf3') buf3))))) op2'"
        if "buf2' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce intro: bc_sym[OF bc_base])
      moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' (BTL pa buf2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' (BENQ pa (BHD pa buf2) buf3)))))) op2'"
        if "buf2 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce intro: bc_sym[OF bc_base])
      moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum (BTL pb buf1) (BTL pb buf1')))) (aeq_op (case_sum buf3' buf3))))) op2'"
        if "buf1 pb \<noteq> []"
          and "buf1' pb \<noteq> []"
          and "BHD pb buf1 \<noteq> BHD pb buf1'"
          and "pb \<notin> defaults"
        for pb :: 'a
      proof -
        have \<open>step Tau
     (comp_op Some (case_sum buf2 buf2')
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1''))
       (aeq_op (case_sum buf3 buf3')))
     (comp_op Some (case_sum buf2 buf2')
       (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb buf1) (BTL pb buf1')))
         (id_op buf1''))
       (aeq_op (case_sum buf3 buf3')))\<close>
          using that by fastforce
        thus ?thesis by (fastforce intro: bc_sym[OF bc_base])
      qed
      moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum (BTL pa buf3') (BTL pa buf3)))))) op2'"
        if "buf3' pa \<noteq> []"
          and "buf3 pa \<noteq> []"
          and "BHD pa buf3' \<noteq> BHD pa buf3"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]], auto)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_id_op_cases)
    qed
  qed
qed

lemma A1:
  \<open>(\<Q> \<parallel> \<I>) \<bullet> \<Q> ~ map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>)\<close>
  unfolding scomp_op_def
  using A1_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A2: Equality test transpose is equality test\<close>

lemma A2_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))
  \<approx> map_op (case_sum Inr Inl) id (aeq_op (case_sum (buf1' >> buf2 >> buf3) (buf1 >> buf2' >> buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a + 'a, 'a, 'b) IO"
      and op1' :: "('a + 'a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op1'"
    show "\<exists>op2'. wstep io (map_op (case_sum Inr Inl) id (aeq_op (case_sum (buf1' >> buf2 >> buf3) (buf1 >> buf2' >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum (buf1' >> buf2 >> buf3) (buf1 >> buf2' >> buf3')))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp pa xa) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (BENQ pa xa (case_sum buf1 buf1'))) (aeq_op (case_sum buf3 buf3')))) op2'"
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
      moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3')) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
        if "buf3 pa \<noteq> []"
          and "buf3' pa \<noteq> []"
          and "BHD pa buf3 = BHD pa buf3'"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL x1 buf1'))) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1' x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1) buf2')) (transp_op (case_sum (BTL x2 buf1) buf1')) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "x2 \<notin> defaults"
          and "buf1 x2 \<noteq> []"
        for x2 :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum (BENQ pa (BHD pa buf2) buf3) buf3')))) op2'"
        if "buf2 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa buf2')) (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 (BENQ pa (BHD pa buf2') buf3'))))) op2'"
        if "buf2' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
        if "buf3 pa \<noteq> []"
          and "buf3' pa \<noteq> []"
          and "BHD pa buf3 \<noteq> BHD pa buf3'"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (intro exI conjI[rotated, OF wbc_base], auto)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_transp_op_cases step_aeq_op_elim split: sum.splits)
    qed
  next
    fix io :: "('a + 'a, 'a, 'b) IO"
      and op1' :: "('a + 'a, 'a, 'b) op"
    assume H: "step io (map_op (case_sum Inr Inl) id (aeq_op (case_sum (buf1' >> buf2 >> buf3) (buf1 >> buf2' >> buf3')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum (buf1' >> buf2 >> buf3) (buf1 >> buf2' >> buf3')))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inr p) y) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((BENQ p y buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and y :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Inp (Inl p) y) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((BENQ p y buf1 >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and y :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((BTL p buf1' >> buf2) >> buf3) ((BTL p buf1 >> buf2') >> buf3')))) op2'"
        if "buf1' p \<noteq> []"
          and "buf1 p \<noteq> []"
          and "BHD p buf1' = BHD p buf1"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p = []"
          and "buf2' p = []"
          and "buf2 p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out p (BHD p buf1)) \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> BTL p buf2) >> buf3) ((BTL p buf1 >> buf2') >> buf3')))) op2'"
        if "buf1 p \<noteq> []"
          and "BHD p buf2 = BHD p buf1"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p = []"
          and "buf2' p = []"
          and "buf2 p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out p (BHD p buf1)) \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((BTL p buf1' >> buf2) >> buf3) ((buf1 >> BTL p buf2') >> buf3')))) op2'"
        if "buf1' p \<noteq> []"
          and "BHD p buf1' = BHD p buf2'"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p = []"
          and "buf2' p \<noteq> []"
          and "buf2 p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out p (BHD p buf2')) \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> BTL p buf2) >> buf3) ((buf1 >> BTL p buf2') >> buf3')))) op2'"
        if "BHD p buf2 = BHD p buf2'"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p = []"
          and "buf2' p \<noteq> []"
          and "buf2 p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) (BTL p buf2')) (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out p (BHD p buf2')) \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) (BTL p buf2')) (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> BTL p buf3) ((BTL p buf1 >> buf2') >> buf3')))) op2'"
        if "buf1 p \<noteq> []"
          and "BHD p buf3 = BHD p buf1"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p \<noteq> []"
          and "buf2' p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 (BENQ p (BHD p buf1) buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out p (BHD p buf1)) \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum (BTL p buf3) buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> BTL p buf3) ((buf1 >> BTL p buf2') >> buf3')))) op2'"
        if "BHD p buf3 = BHD p buf2'"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p \<noteq> []"
          and "buf2' p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out p (BHD p buf2')) \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum (BTL p buf3) buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((BTL p buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> BTL p buf3')))) op2'"
        if "buf1' p \<noteq> []"
          and "BHD p buf1' = BHD p buf3'"
          and "p \<notin> defaults"
          and "buf3' p \<noteq> []"
          and "buf3 p = []"
          and "buf2 p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out p (BHD p buf3')) \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> BTL p buf2) >> buf3) ((buf1 >> buf2') >> BTL p buf3')))) op2'"
        if "BHD p buf2 = BHD p buf3'"
          and "p \<notin> defaults"
          and "buf3' p \<noteq> []"
          and "buf3 p = []"
          and "buf2 p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step (Out p (BHD p buf3')) \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> BTL p buf3) ((buf1 >> buf2') >> BTL p buf3')))) op2'"
        if "BHD p buf3 = BHD p buf3'"
          and "p \<notin> defaults"
          and "buf3' p \<noteq> []"
          and "buf3 p \<noteq> []"
        for p :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((BTL p buf1' >> buf2) >> buf3) ((BTL p buf1 >> buf2') >> buf3')))) op2'"
        if "buf1' p \<noteq> []"
          and "buf1 p \<noteq> []"
          and "BHD p buf1' \<noteq> BHD p buf1"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p = []"
          and "buf2' p = []"
          and "buf2 p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> BTL p buf2) >> buf3) ((BTL p buf1 >> buf2') >> buf3')))) op2'"
        if "buf1 p \<noteq> []"
          and "BHD p buf2 \<noteq> BHD p buf1"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p = []"
          and "buf2' p = []"
          and "buf2 p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((BTL p buf1' >> buf2) >> buf3) ((buf1 >> BTL p buf2') >> buf3')))) op2'"
        if "buf1' p \<noteq> []"
          and "BHD p buf1' \<noteq> BHD p buf2'"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p = []"
          and "buf2' p \<noteq> []"
          and "buf2 p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> BTL p buf2) >> buf3) ((buf1 >> BTL p buf2') >> buf3')))) op2'"
        if "BHD p buf2 \<noteq> BHD p buf2'"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p = []"
          and "buf2' p \<noteq> []"
          and "buf2 p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) (BTL p buf2')) (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) (BTL p buf2')) (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> BTL p buf3) ((BTL p buf1 >> buf2') >> buf3')))) op2'"
        if "buf1 p \<noteq> []"
          and "BHD p buf3 \<noteq> BHD p buf1"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p \<noteq> []"
          and "buf2' p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1) buf2')) (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inl_not_in_defaults case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum buf3 (BENQ p (BHD p buf1) buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum (BTL p buf1) buf1'))
         (aeq_op (case_sum (BTL p buf3) buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> BTL p buf3) ((buf1 >> BTL p buf2') >> buf3')))) op2'"
        if "BHD p buf3 \<noteq> BHD p buf2'"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf3 p \<noteq> []"
          and "buf2' p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 (BTL p buf2')) (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum (BTL p buf3) buf3'))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((BTL p buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> BTL p buf3')))) op2'"
        if "buf1' p \<noteq> []"
          and "BHD p buf1' \<noteq> BHD p buf3'"
          and "p \<notin> defaults"
          and "buf3' p \<noteq> []"
          and "buf3 p = []"
          and "buf2 p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum (BENQ p (BHD p buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum buf3 buf3'))))\<close>
          using that
          by (metis IO.simps(17) Inr_not_in_defaults case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R sum.simps(6) step_Tau_comp_op_L step_map_op step_transp_op_Write)
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum (BENQ p (BHD p buf1') buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 (BTL p buf1')))
         (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> BTL p buf2) >> buf3) ((buf1 >> buf2') >> BTL p buf3')))) op2'"
        if "BHD p buf2 \<noteq> BHD p buf3'"
          and "p \<notin> defaults"
          and "buf3' p \<noteq> []"
          and "buf3 p = []"
          and "buf2 p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr
       (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 buf3')))) (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr
       (comp_op Some (case_sum (BTL p buf2) buf2') (transp_op (case_sum buf1 buf1'))
         (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
          using that by auto
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> buf3) ((buf1 >> buf2') >> buf3')))) (map_op (case_sum Inr Inl) id (aeq_op (case_sum ((buf1' >> buf2) >> BTL p buf3) ((buf1 >> buf2') >> BTL p buf3')))) op2'"
        if "BHD p buf3 \<noteq> BHD p buf3'"
          and "p \<notin> defaults"
          and "buf3' p \<noteq> []"
          and "buf3 p \<noteq> []"
        for p :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], blast, fastforce)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_aeq_op_elim split: if_splits)
    qed
  qed
qed

lemma A2:
  \<open>\<X> \<bullet> \<Q> \<approx> map_op (case_sum Inr Inl) id \<Q>\<close>
  unfolding scomp_op_def
  using A2_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A3: Equality test dummy source and identity\<close>

lemma A3_gen:
  \<open>map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
    (map_op projr id (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>) \<parallel> id_op buf1))
    (aeq_op (case_sum (\<lambda>_. []) buf3)))
  \<approx> map_op projl projr (comp_op Some (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))\<close>
proof (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_aeq_op_elim) blast+
  next
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_sink_op step_id_op_cases) (fastforce intro: wbc_sym[OF wbc_base])
  qed
qed

lemma A3:
  \<open>map_op projr id (\<exclamdown> \<parallel> \<I>) \<bullet> \<Q> \<approx> ! \<bullet> \<exclamdown>\<close>
  unfolding scomp_op_def
  using A3_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A4: Equality test to sink\<close>

lemma A4_gen:
  \<open>map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) !) \<approx> ! \<parallel> !\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a + 'a, 'b + 'c, 'd) IO"
      and op1' :: "('a + 'a, 'b + 'c, 'd) op"
    assume H: "step io (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) !)) op1'"
    show "\<exists>op2'. wstep io (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_sink_op) (fastforce del: wbc_base intro: wbc_base)+
  next
    fix io :: "('a + 'a, 'b + 'c, 'd) IO"
      and op1' :: "('a + 'a, 'b + 'c, 'd) op"
    assume H: "step io (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1' op2'"
      using H by (auto elim !: step_comp_op_elim step_sink_op) (fastforce intro: wbc_sym[OF wbc_base])+
  qed
qed

lemma A4:
  \<open>\<Q> \<bullet> ! \<approx> ! \<parallel> !\<close>
  unfolding scomp_op_def
  using A4_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>  \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A5: Acopy to acopy and identity\<close>

lemma A5_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (acopy_op (case_sum buf3 buf3') \<parallel> id_op buf3''))
  ~ map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2)
    (acopy_op (case_sum buf1' buf1))
    (id_op buf3'' \<parallel> acopy_op (case_sum buf3 buf3'))))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' buf3'' rule: bisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding sim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a, ('a + 'a) + 'a, 'b) IO"
      and op1' :: "('a, ('a + 'a) + 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf3 buf3')) (id_op buf3'')))) op1'"
    show "\<exists>op2'. step io (map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2) (acopy_op (case_sum buf1' buf1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3'') (acopy_op (case_sum buf3 buf3')))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf2 buf2' buf3 buf3' buf3''. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf3 buf3')) (id_op buf3''))) \<and> t = map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2) (acopy_op (case_sum buf1' buf1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3'') (acopy_op (case_sum buf3 buf3')))))) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_id_op_cases) (fastforce intro: bc_base)+
  next
    fix io :: "('a, ('a + 'a) + 'a, 'b) IO"
      and op1' :: "('a, ('a + 'a) + 'a, 'b) op"
    assume H: "step io (map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2) (acopy_op (case_sum buf1' buf1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3'') (acopy_op (case_sum buf3 buf3')))))) op1'"
    show "\<exists>op2'. step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf3 buf3')) (id_op buf3'')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf2 buf2' buf3 buf3' buf3''. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf3 buf3')) (id_op buf3''))) \<and> t = map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2) (acopy_op (case_sum buf1' buf1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3'') (acopy_op (case_sum buf3 buf3')))))) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_id_op_cases) (fastforce intro: bc_sym[OF bc_base])+
  qed
qed

lemma A5:
  \<open>\<C> \<bullet> (\<C> \<parallel> \<I>) ~ map_op id (case_sum Inr Inl) (\<C> \<bullet> (\<I> \<parallel> \<C>))\<close>
  unfolding scomp_op_def
  using A5_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A6: Acopy to transpose\<close>

lemma A6_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))
  \<approx> map_op id (case_sum Inr Inl) (acopy_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'a + 'a, 'b) IO"
      and op1' :: "('a, 'a + 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op1'"
    show "\<exists>op2'. wstep io (map_op id (case_sum Inr Inl) (acopy_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp pa xa) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum (BENQ pa xa buf1) (BENQ pa xa buf1'))) (transp_op (case_sum buf3 buf3')))) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'b
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BTL x1 buf3'))))) op2'"
        if "x1 \<notin> defaults"
          and "buf3' x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3)) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum (BTL x2 buf3) buf3')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3 x2 \<noteq> []"
        for x2 :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf1) buf2) buf2') (acopy_op (case_sum (BTL pa buf1) buf1')) (transp_op (case_sum buf3 buf3')))) op2'"
        if "buf1 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa buf1') buf2')) (acopy_op (case_sum buf1 (BTL pa buf1'))) (transp_op (case_sum buf3 buf3')))) op2'"
        if "buf1' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3')))) op2'"
        if "x1 \<notin> defaults"
          and "buf2 x1 \<noteq> []"
        for x1 :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2')) (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BENQ x2 (BHD x2 buf2') buf3'))))) op2'"
        if "x2 \<notin> defaults"
          and "buf2' x2 \<noteq> []"
        for x2 :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_transp_op_cases split: sum.splits)
    qed
  next
    fix io :: "('a, 'a + 'a, 'b) IO"
      and op1' :: "('a, 'a + 'a, 'b) op"
    assume H: "step io (map_op id (case_sum Inr Inl) (acopy_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((BENQ p x buf1 >> buf2) >> buf3) ((BENQ p x buf1' >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that by force
      moreover have "\<exists>op2'. wstep (Out (Inr p) (BHD p buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((BTL p buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "buf1 p \<noteq> []"
          and "p \<notin> defaults"
          and "buf3 p = []"
          and "buf2 p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1) buf2) buf2')
      (acopy_op (case_sum (BTL p buf1) buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum (BTL p buf1) buf1')) (transp_op (case_sum (BENQ p (BHD p buf1) buf3) buf3'))))\<close>
          using that by auto
        also have \<open>step (Out (Inr p) (BHD p buf1)) \<dots> (map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum (BTL p buf1) buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inr p)) (BHD p buf1)\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr p) (BHD p buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> BTL p buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
          and "buf3 p = []"
          and "buf2 p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
      (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
          using that by auto
        also have \<open>step (Out (Inr p) (BHD p buf2)) \<dots> (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
      (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inr p)) (BHD p buf2)\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr p) (BHD p buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> BTL p buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
          and "buf3 p \<noteq> []"
        for p :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], force+)
      moreover have "\<exists>op2'. wstep (Out (Inl p) (BHD p buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((BTL p buf1' >> buf2') >> buf3')))) op2'"
        if "buf1' p \<noteq> []"
          and "p \<notin> defaults"
          and "buf3' p = []"
          and "buf2' p = []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum buf2 (BENQ p (BHD p buf1') buf2'))
      (acopy_op (case_sum buf1 (BTL p buf1'))) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by auto[1] fastforce
        also have \<open>step Tau \<dots> (map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum buf1 (BTL p buf1'))) (transp_op (case_sum buf3 (BENQ p (BHD p buf1') buf3')))))\<close>
          using that by auto
        also have \<open>step (Out (Inl p) (BHD p buf1')) \<dots> (map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum buf1 (BTL p buf1'))) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inl p)) (BHD p buf1')\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl p) (BHD p buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL p buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
          and "buf3' p = []"
          and "buf2' p \<noteq> []"
        for p :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
      (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BENQ p (BHD p buf2') buf3')))))\<close>
          using that by auto
        also have \<open>step (Out (Inl p) (BHD p buf2')) \<dots> (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
      (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inl p)) (BHD p buf2')\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl p) (BHD p buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> BTL p buf3')))) op2'"
        if "p \<notin> defaults"
          and "buf3' p \<noteq> []"
        for p :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], force+)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_acopy_op_elim split: sum.splits if_splits)
    qed
  qed
qed

lemma A6:
  \<open>\<C> \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<C>\<close>
  unfolding scomp_op_def
  using A6_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A7: Acopy to sink and identity\<close>

lemma A7_gen:
  \<open>map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1')) (! \<parallel> id_op buf3)))
  \<approx> id_op (buf1' >> buf2' >> buf3)\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op1'"
    show "\<exists>op2'. wstep io (id_op (buf1' >> buf2' >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op (buf1' >> buf2' >> buf3)) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp pa xa) (id_op ((buf1' >> buf2') >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum (BENQ pa xa buf1) (BENQ pa xa buf1'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'b
        using that by force
      moreover have "\<exists>op2'. wstep (Out pb (BHD pb buf3)) (id_op ((buf1' >> buf2') >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op (BTL pb buf3)))))) op2'"
        if "pb \<notin> defaults"
          and "buf3 pb \<noteq> []"
        for pb :: 'a
        using that by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (map_op id projr (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf1) buf2) buf2') (acopy_op (case_sum (BTL pa buf1) buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2'"
        if "buf1 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa buf1') buf2')) (acopy_op (case_sum buf1 (BTL pa buf1'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2'"
        if "buf1' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (map_op id projr (map_op projl projr (comp_op Some (case_sum (BTL pb buf2) buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2'"
        if "buf2 pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 (BTL pb buf2')) (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op (BENQ pb (BHD pb buf2') buf3)))))) op2'"
        if "buf2' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_sink_op step_id_op_cases)
    qed
  next
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (id_op (buf1' >> buf2' >> buf3)) op1'"
    show "\<exists>op2'. wstep io (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op (buf1' >> buf2' >> buf3)) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (id_op ((BENQ p x buf1' >> buf2') >> buf3)) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf1')) (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (id_op ((BTL p buf1' >> buf2') >> buf3)) op2'"
        if "buf1' p \<noteq> []"
          and "p \<notin> defaults"
          and "buf3 p = []"
          and "buf2' p = []"
        for p :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf2')) (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (id_op ((buf1' >> BTL p buf2') >> buf3)) op2'"
        if "p \<notin> defaults"
          and "buf3 p = []"
          and "buf2' p \<noteq> []"
        for p :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf3)) (map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op id projr (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('a, 'c, 'b) op) (id_op buf3)))) \<and> op2 = id_op ((buf1' >> buf2') >> buf3)) (id_op ((buf1' >> buf2') >> BTL p buf3)) op2'"
        if "p \<notin> defaults"
          and "buf3 p \<noteq> []"
        for p :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      ultimately show ?thesis
        using H by (elim step_id_op_cases ; simp split: if_splits)
    qed
  qed
qed

lemma A7:
  \<open>map_op id projr (\<C> \<bullet> (! \<parallel> \<I>)) \<approx> \<I>\<close>
  unfolding scomp_op_def
  using A7_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A8: Acopy dummy source\<close>

lemma A8:
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

section \<open>Axiom A10: Equality test to acopy\<close>

lemma same_prefix_prefix:
  "prefix ((ys >> xs) p) ((zs >> xs) p) = prefix (ys p) (zs p)"
  by (simp add: BULK_BENQ_def)

lemma suffix_BTL[simp]: 
 "buf p \<noteq> [] \<Longrightarrow> suffix ((BTL p buf) p) (buf p)"
  unfolding BTL_def by simp

definition nsuffix where
  "nsuffix n xs ys = (suffix xs ys \<and> n = length ys - length xs)"

lemma nsuffix_0[simp]: "nsuffix 0 xs ys \<longleftrightarrow> xs = ys"
  unfolding nsuffix_def using suffix_take by fastforce

definition nprefix where
  "nprefix n xs ys = (prefix xs ys \<and> n = length ys - length xs)"

lemma nprefix_0[simp]: "nprefix 0 xs ys \<longleftrightarrow> xs = ys"
  unfolding nprefix_def by (metis diff_is_0_eq prefix_length_le prefix_length_prefix prefix_order.eq_iff)

declare BULK_BENQ_left_empty[simp del] BULK_BENQ_right_empty[simp del] list_emb_Nil2[simp del]

definition "length_consumed n xs ys = length (filter (case_prod (=)) (zip (take n xs) (take n ys)))"

lemma length_consumed_0[simp]:
  "length_consumed 0 xs ys = 0"
  unfolding length_consumed_def by simp

lemma length_consumed_Suc[simp]:
  "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> hd xs \<noteq> hd ys \<Longrightarrow> length_consumed (Suc n) xs ys = length_consumed n (tl xs) (tl ys)"
  unfolding length_consumed_def by (simp add: take_Suc)

lemma length_consumed_leq:
  "length_consumed n xs ys \<le> n"
  unfolding length_consumed_def by (metis length_filter_le length_take length_zip min.bounded_iff)

definition "tested n xs ys = map fst (filter (case_prod (=)) (zip (take n xs) (take n ys)))"

lemma tested_Suc:
  "length xs > n \<Longrightarrow> length ys > n \<Longrightarrow> xs ! n \<noteq> ys ! n \<Longrightarrow> tested (Suc n) xs ys = tested n xs ys"
  unfolding tested_def
  apply (induct n arbitrary: xs ys)
   apply (auto simp: take_Suc hd_conv_nth)
  subgoal for n xs ys
    apply (cases xs; cases ys; simp)
    done
  done

lemma length_tested_0[simp]:
  "tested 0 xs ys = []"
  unfolding tested_def by simp

lemma
  assumes "A = A1 >> A2 >> A3 >> A4 >> A5"
  and "B = B1 >> B2 >> B3 >> B4 >> B5"
  and "C = C1 >> C2 >> C3 >> C4 >> C5"
  and "D = D1 >> D2 >> D3 >> D4 >> D5"
  and "AC = AC1 >> AC2"
  and "BD = BD1 >> BD2"
  and "\<forall> p. \<exists> m n. (m = 0 \<or> n = 0) \<and> (A p) = (drop n (X p)) \<and> (C p) = drop n (Y p) \<and> (B p) = drop m (X p) \<and> (D p) = drop m (Y p) \<and> 
        (AC p) = ((Z >> V) p) @ (tested n (X p) (Y p)) \<and> (BD p) = ((Z >> W) p) @ (tested m (X p) (Y p))"
  shows  "map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<approx>
   map_op projl projr
   (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
         (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
     (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))"
using assms proof (coinduction arbitrary: A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V A B C D AC BD  rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
(*     explore (auto 0 0 elim!: step_aeq_op_elim step_acopy_op_elim step_transp_op_cases step_map_op_elim step_comp_op_elim step_id_op_cases split: if_splits sum.splits; hypsubst_thin?)
 *)    sorry
next
  case SIM2
  then show ?case 
    apply -
    apply hypsubst_thin
    apply (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases)
    apply (simp_all only: IO.simps)
    apply (simp_all split!: sum.splits if_splits; hypsubst_thin?)
    prefer 55
    apply (simp_all split: sum.splits if_splits)[1]
    subgoal for io' op'' op2' op2'a io'a op''a op1'a pc
      apply hypsubst_thin
      apply (frule spec[of _ pc])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (cases "n = 0")
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          apply simp
          subgoal for pd
            apply (cases "pc = pd")
            subgoal
              apply simp
              apply (rule exI[of _ 1])
              apply (rule exI[of _ 0])
              apply simp
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access drop0 drop_Suc)
              subgoal
                by (metis BAPPEND_BTL BTL_access drop0 drop_Suc)
              subgoal
                unfolding tested_def
                apply (auto simp add: filter_empty_conv in_set_zip)
                apply (metis (mono_tags, lifting) BHD_BULK_BENQ_cases BHD_def hd_drop_conv_nth length_greater_0_conv)
                done
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m n
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                apply (intro conjI)
                subgoal
                  by (simp add: BTL_def BULK_BENQ_def)
                subgoal
                  by (simp add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        subgoal 
          apply (intro exI conjI)
          apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
          apply (rule step_comp_op_L_Tau)
          apply (rule step_aeq_op_Silent)
          apply assumption
          apply simp_all
          subgoal
            unfolding nsuffix_def
            by (metis BULK_BENQ_empty)
          subgoal
            unfolding nsuffix_def
            by (metis BULK_BENQ_empty)
          subgoal
            unfolding nsuffix_def
            by (metis (no_types, lifting) BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty self_append_conv2 suffix_take take0)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases "pc = pd")
              subgoal
                apply simp
                apply (rule exI[of _ 0])
                apply (rule exI[of _ "n - 1"])
                apply simp
                apply (intro conjI)
                subgoal
                  by (metis BTL_access Suc_pred drop_Suc)
                subgoal
                  by (metis BTL_access Suc_pred drop_Suc)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  apply (cases n)
                  apply simp_all
                  apply (subst tested_Suc)
                     apply force
                    apply force
                   apply (metis BHD_def BULK_BENQ_def hd_append2)
                  apply (metis BTL_access)
                  done
                done
 subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m n
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      done
    subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (cases "m = 0")
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          apply simp
          subgoal for pd
            apply (cases "pc = pd")
            subgoal
              apply simp
              apply (rule exI[of _ 1])
              apply (rule exI[of _ 0])
              apply simp
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access drop0 drop_Suc)
              subgoal
                by (metis BAPPEND_BTL BTL_access drop0 drop_Suc)
              subgoal
                unfolding tested_def
                apply (auto simp add: filter_empty_conv in_set_zip)
                apply (metis (mono_tags, lifting) BHD_BULK_BENQ_cases BHD_def hd_conv_nth)
                done
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m n
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                apply (intro conjI)
                subgoal
                  by (simp add: BTL_def BULK_BENQ_def)
                subgoal
                  by (simp add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        subgoal
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          apply simp
          subgoal for pd
            apply (cases "pc = pd")
            subgoal
              apply simp
              apply (rule exI[of _ "Suc m"])
              apply (rule exI[of _ 0])
              apply simp
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access drop_Suc drop_tl)
              subgoal
                by (metis BAPPEND_BTL BTL_access drop_Suc drop_tl)
              subgoal
                apply (cases m)
                 apply simp_all
   apply (subst tested_Suc)
                     apply force
                  apply force
                sledgehammer


                unfolding tested_def



end
                by (metis (no_types, lifting) BTL_access BULK_BENQ_def BULK_BENQ_empty One_nat_def Suc_pred add_diff_cancel_right' length_greater_0_conv length_tl plus_1_eq_Suc suffix_BTL tl_append2)
              subgoal
                unfolding nsuffix_def
                by (metis (no_types, lifting) BTL_access BULK_BENQ_def BULK_BENQ_empty One_nat_def Suc_pred add_diff_cancel_right' length_greater_0_conv length_tl plus_1_eq_Suc suffix_BTL tl_append2)
              subgoal
                apply hypsubst_thin
                apply (subst length_consumed_Suc)
                   apply force
                  apply force
                 apply (metis BHD_BULK_BENQ_right_not_empty BHD_def)
                apply simp
                done
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m n
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                apply (intro conjI)
                subgoal
                  by (simp add: BTL_def BULK_BENQ_def)
                subgoal
                  by (simp add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done

        subgoal 
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply simp_all
          subgoal
            unfolding nsuffix_def
            by (metis BULK_BENQ_empty suffix_bot.extremum_uniqueI)
          subgoal
            unfolding nsuffix_def
            by (metis BULK_BENQ_empty suffix_bot.extremum_uniqueI)
          subgoal
            unfolding nsuffix_def
end
            by (metis (no_types, lifting) BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty self_append_conv2 suffix_take take0)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases "pc = pd")
              subgoal
                apply simp
                apply (rule exI[of _ 0])
                apply (rule exI[of _ "n - 1"])
                apply simp
                apply (intro conjI)
                subgoal
                  unfolding nsuffix_def
                  apply (intro conjI)
                  apply (metis (no_types, lifting) BTL_access BULK_BENQ_empty One_nat_def Suc_pred length_greater_0_conv length_tl less_Suc_eq_le suffix_BTL suffix_length_suffix zero_less_diff)
                  apply (metis BTL_access One_nat_def diff_right_commute length_tl)
                  done
                subgoal
                  unfolding nsuffix_def
                  apply (intro conjI)
                  apply (metis (no_types, lifting) BTL_access BULK_BENQ_empty One_nat_def Suc_pred length_greater_0_conv length_tl less_Suc_eq_le suffix_BTL suffix_length_suffix zero_less_diff)
                  apply (metis BTL_access One_nat_def diff_right_commute length_tl)
                  done
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (metis BHD_BAPPEND_2_cases BHD_def BTL_access BULK_BENQ_empty Suc_pred length_consumed_Suc)          
                done
       subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m n
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply (simp add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done

end
          apply (rule rtranclp.intros(1))
   apply (rule wbc_base)
        apply (intro exI conjI)
           apply (rule refl)+
         apply (intro allI)
        subgoal for pd
              apply (cases "pc = pd")
          subgoal
 apply hypsubst_thin
            apply (rule disjI2)
            apply (rule disjI2)
            apply (intro conjI)
            apply assumption+
                subgoal 
                  unfolding ssuffix_def
                  apply clarsimp
                  apply safe
                  apply (metis BAPPEND_BTL BULK_BENQ_empty suffix_BTL)
                  apply (auto simp add: BHD_def BTL_def BULK_BENQ_def)
                  apply (metis Cons_eq_append_conv list.collapse list.discI self_append_conv2)
                  done
                subgoal 
                  unfolding ssuffix_def
                  apply clarsimp
                  apply safe
                  apply (metis BAPPEND_BTL BULK_BENQ_empty suffix_BTL)
                  apply (auto simp add: BHD_def BTL_def BULK_BENQ_def)
                  apply (metis Cons_eq_append_conv list.collapse list.discI self_append_conv2)
                  done
                done
              subgoal
                apply (drule spec[of _ pd])
                  apply (auto simp add: BHD_def BTL_def BULK_BENQ_def)
                done
              done
            subgoal sorry
            done
          subgoal
                apply (intro exI conjI)
      apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
      apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_aeq_op_Silent)
              apply assumption
                   apply simp_all
            apply force
              apply (metis BULK_BENQ_empty)
             apply (metis BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty)
   apply (rule wbc_base)
        apply (intro exI conjI)
           apply (rule refl)+
         apply (intro allI)
            subgoal for pd
              apply (cases "pc = pd")
          subgoal
            apply hypsubst_thin
            apply (cases "((((A1 >> A2) >> A3) >> A4) >> A5) pd = BTL pd X pd")
            subgoal



end
            apply (rule disjI2)
            apply (rule disjI2)
            apply (intro conjI)
            apply assumption+
                subgoal 
                  unfolding ssuffix_def
                  apply clarsimp
                  apply safe
                  apply (metis BAPPEND_BTL BULK_BENQ_empty suffix_BTL)
                  apply (auto simp add: BHD_def BTL_def BULK_BENQ_def)
                  apply (metis Cons_eq_append_conv list.collapse list.discI self_append_conv2)
                  done
                subgoal 
                  unfolding ssuffix_def
                  apply clarsimp
                  apply safe
                  apply (metis BAPPEND_BTL BULK_BENQ_empty suffix_BTL)
                  apply (auto simp add: BHD_def BTL_def BULK_BENQ_def)
                  apply (metis Cons_eq_append_conv list.collapse list.discI self_append_conv2)
                  done
                done
              subgoal
                apply (drule spec[of _ pd])
                  apply (auto simp add: BHD_def BTL_def BULK_BENQ_def)
                done
              done

end
        apply (cases "((((A1 >> A2) >> A3) >> A4) >> A5) pc = X pc")
        subgoal
      apply (intro exI conjI[rotated])
         apply (rule wbc_base)
        apply (intro exI conjI)
              apply (rule refl)+
        defer
          defer
          apply (rule rtranclp.intros(1))
                apply simp_all
        apply (cases "((((C1 >> C2) >> C3) >> C4) >> C5) pc = Y pc")
          subgoal
            apply simp
            apply (intro allI conjI)
            subgoal for pd
              apply (cases "pc = pd")
              subgoal
                apply hypsubst_thin
                apply (rule disjI2)
                apply (intro conjI)
                subgoal 
                  by (metis BAPPEND_BTL BULK_BENQ_empty suffix_BTL)
                subgoal
                  by (metis BAPPEND_BTL BULK_BENQ_empty suffix_BTL)
                 apply assumption+
                done
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE disjE)
                subgoal
                  apply (rule disjI1)
                  apply (auto simp add: BTL_def BULK_BENQ_def)
                  done
                subgoal
                  apply (rule disjI2)
                  apply (auto simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done

                  apply (rule same_prefix_prefix[THEN iffD2])

                  find_theorems BTL "_ >> _"


end
            apply force
           apply force
          apply (metis BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty)
         apply (intro allI conjI)
         apply (rule disjI1)
         apply (intro conjI)
        sledgehammer

end
        defer
        apply (smt (verit) BAPPEND_BTL BULK_BENQ_assoc BULK_BENQ_eq_right)
        apply (smt (verit) BAPPEND_BTL BULK_BENQ_assoc BULK_BENQ_eq_right)
          defer
          apply (rule disjI1)
          apply safe
        defer
    



end
    ultimately show ?thesis
      by (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases ; simp only: IO.simps ; simp split: sum.splits if_splits ; hypsubst_thin ?)
  qed
 

end
    ultimately show ?thesis
      by (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases ; simp only: IO.simps ; simp split: sum.splits if_splits ; hypsubst_thin ?)
  qed
 


end
    ultimately show ?thesis
      by (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases ; simp only: IO.simps ; simp split: sum.splits if_splits ; hypsubst_thin ?)
  qed
 
        

end
    ultimately show ?thesis
      by (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases ; simp only: IO.simps ; simp split: sum.splits if_splits)
  qed
 

end
    ultimately show ?thesis
      by (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases ; simp only: IO.simps ; simp split: sum.splits if_splits ; hypsubst_thin ?)
  qed
 


end
    ultimately show ?thesis

end
      by (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases ; simp only: IO.simps ; simp split: sum.splits if_splits ; hypsubst_thin ?)
  qed







end
      

lemma
  "map_op projl projr (comp_op Some A1 (aeq_op (case_sum (B1 >> B1' >> B1'' >> B1''') (B2 >> B2' >> B2'' >> B2'''))) (acopy_op (case_sum A2 A3))) \<approx>
   map_op projl projr
   (comp_op Some (case_sum (case_sum B1''' B2''') (case_sum (\<lambda> _. []) (\<lambda> _. [])))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum B1 (\<lambda> _. [])) (case_sum B2' (\<lambda> _. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum B1 (\<lambda> _. []))) (acopy_op (case_sum B2 (\<lambda> _. []))))
         (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (transp_op (case_sum (\<lambda> _. []) B2'')))) (id_op (\<lambda> _. []))))))
     (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (A1 >> A2) (A1 >> A3))) (aeq_op (case_sum (\<lambda>_. []) (\<lambda>_. [])))))"
  oops



end
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM2 apply -
        apply (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases ; simp only: IO.simps ; simp split: sum.splits if_splits ; hypsubst_thin ?)
                            apply (rule prems; assumption)+
        done
      done
  qed
qed

lemma A10:
  "\<Q> \<bullet> \<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q> \<parallel> \<Q>)"
  unfolding scomp_op_def pcomp_op_def
  oops

section \<open>Axiom A11: Acopy to equality test\<close>

lemma A11_gen:
  assumes \<open>buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3'\<close>
  shows \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3')))
  \<approx> id_op (buf1 >> buf2 >> buf3)\<close>
  using assms proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H1: "buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3'"
      and H2: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op1'"
    show "\<exists>op2'. wstep io (id_op (buf1 >> buf2 >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op (buf1 >> buf2 >> buf3) \<and> buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3') op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp pa xa) (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum (BENQ pa xa buf1) (BENQ pa xa buf1'))) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
          and "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'b
        using that
        apply (intro exI conjI[rotated, OF wbc_base])
         apply auto[1]
         apply (metis BAPPEND_BENQ)
        by (metis BAPPEND_BENQ step_id_op_Read step_wstep)
      moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3')) (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
        if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
          and "buf3 pa \<noteq> []"
          and "buf3' pa \<noteq> []"
          and "BHD pa buf3 = BHD pa buf3'"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that
        apply (intro exI conjI[rotated, OF wbc_base])
         apply auto[1]
         apply (metis BAPPEND_BTL)
        by (metis BAPPEND_BTL BHD_BULK_BENQ_right_not_empty BULK_BENQ_empty step_id_op_Write step_wstep)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf1) buf2) buf2') (acopy_op (case_sum (BTL pa buf1) buf1')) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
          and "buf1 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa buf1') buf2')) (acopy_op (case_sum buf1 (BTL pa buf1'))) (aeq_op (case_sum buf3 buf3')))) op2'"
        if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
          and "buf1' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum (BENQ pa (BHD pa buf2) buf3) buf3')))) op2'"
        if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
          and "buf2 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that
        apply (intro exI conjI[rotated, OF wbc_base])
         apply auto[1]
         apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
        by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa buf2')) (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 (BENQ pa (BHD pa buf2') buf3'))))) op2'"
        if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
          and "buf2' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that
        apply (intro exI conjI[rotated, OF wbc_base])
         apply auto[1]
         apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
        by simp
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf1' >> buf2') >> buf3')) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum (BTL pa buf3) (BTL pa buf3'))))) op2'"
        if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
          and "buf3 pa \<noteq> []"
          and "buf3' pa \<noteq> []"
          and "BHD pa buf3 \<noteq> BHD pa buf3'"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that
        apply (intro exI conjI[rotated, OF wbc_base])
         apply auto[1]
         apply (metis BAPPEND_BTL)
        by (metis BHD_BULK_BENQ_right_not_empty)
      ultimately show ?thesis
        using H1 H2 by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_aeq_op_elim)
    qed
  next
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H1: "buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3'"
      and H2: "step io (id_op (buf1 >> buf2 >> buf3)) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op (buf1 >> buf2 >> buf3) \<and> buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3') op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (id_op ((BENQ p x buf1' >> buf2') >> buf3')) op2'"
        if "(buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3'"
          and "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that
        apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
  (acopy_op (case_sum (BENQ p x buf1) (BENQ p x buf1')))
  (aeq_op (case_sum buf3 buf3')))\<close>])
        apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
         apply (metis BAPPEND_BENQ BULK_BENQ_assoc)
        by fastforce
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (id_op ((BTL p buf1' >> buf2') >> buf3')) op2'"
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
  (aeq_op (case_sum (BTL p buf3) buf3')))\<close>])
          apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
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
            using that by (auto del: step_Tau_comp_op_L intro!: step_Tau_comp_op_L)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf1') buf3')))))\<close>
            using that by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf1') buf3')))))\<close>
            using that True by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out p (BHD p buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum buf3 buf3'))))\<close>
            using that True False BHD_eq by auto
          ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
  (acopy_op (case_sum buf1 (BTL p buf1')))
  (aeq_op (case_sum buf3 buf3')))\<close>])
            apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
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
            using that by (auto del: step_Tau_comp_op_L intro!: step_Tau_comp_op_L)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 (BTL p buf1')))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf1') buf3')))))\<close>
            using that by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1) buf2) buf2')
    (acopy_op (case_sum (BTL p buf1) (BTL p buf1')))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf1') buf3')))))\<close>
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
            by (auto del: step_Tau_comp_op_L intro!: step_Tau_comp_op_L)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum (BTL p buf1) (BTL p buf1')))
    (aeq_op (case_sum (BENQ p (BHD p buf1) buf3) (BENQ p (BHD p buf1') buf3')))))\<close>
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
            by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out p (BHD p buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum (BTL p buf1) (BTL p buf1')))
    (aeq_op (case_sum buf3 buf3'))))\<close>
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty BHD_eq by auto
          ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
  (acopy_op (case_sum (BTL p buf1) (BTL p buf1')))
  (aeq_op (case_sum buf3 buf3')))\<close>])
            apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
             apply (metis (mono_tags, opaque_lifting) BAPPEND_BTL)
            by (meson wstep_trans(1))
        qed
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (id_op ((buf1' >> BTL p buf2') >> buf3')) op2'"
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
  (aeq_op (case_sum (BTL p buf3) buf3')))\<close>])
          apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
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
            using that by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) (BTL p buf2'))
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
            using that True by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out p (BHD p buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) (BTL p buf2'))
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 buf3'))))\<close>
            using that True False BHD_eq by auto
          ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf2) (BTL p buf2'))
  (acopy_op (case_sum buf1 buf1'))
  (aeq_op (case_sum buf3 buf3')))\<close>])
            apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
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
            using that by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1) buf2) (BTL p buf2'))
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum buf3 (BENQ p (BHD p buf2') buf3')))))\<close>
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
            by (auto del: step_Tau_comp_op_L intro!: step_Tau_comp_op_L)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum (BENQ p (BHD p buf1) buf3) (BENQ p (BHD p buf2') buf3')))))\<close>
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
            by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out p (BHD p buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum buf3 buf3'))))\<close>
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty BHD_eq by auto
          ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 (BTL p buf2'))
  (acopy_op (case_sum (BTL p buf1) buf1'))
  (aeq_op (case_sum buf3 buf3')))\<close>])
            apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
             apply (metis (mono_tags, opaque_lifting) BAPPEND_BTL)
            by (meson wstep_trans(1))
        qed
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (aeq_op (case_sum buf3 buf3'))) \<and> op2 = id_op ((buf1 >> buf2) >> buf3) \<and> (buf1 >> buf2) >> buf3 = (buf1' >> buf2') >> buf3') (id_op ((buf1' >> buf2') >> BTL p buf3')) op2'"
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
  (aeq_op (case_sum (BTL p buf3) (BTL p buf3'))))\<close>])
          apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
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
            using that True by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out p (BHD p buf3')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
    (acopy_op (case_sum buf1 buf1'))
    (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
            using that True False BHD_eq by auto
          ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf2) buf2')
  (acopy_op (case_sum buf1 buf1'))
  (aeq_op (case_sum buf3 (BTL p buf3'))))\<close>])
            apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
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
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
            by (auto del: step_Tau_comp_op_L intro!: step_Tau_comp_op_L)
          also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum (BENQ p (BHD p buf1) buf3) buf3'))))\<close>
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
            by (auto del: step_Tau_comp_op_R intro!: step_Tau_comp_op_R)
          also have \<open>step (Out p (BHD p buf3')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum (BTL p buf1) buf1'))
    (aeq_op (case_sum buf3 (BTL p buf3')))))\<close>
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty BHD_eq by auto
          ultimately show ?thesis
          apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
  (acopy_op (case_sum (BTL p buf1) buf1'))
  (aeq_op (case_sum buf3 (BTL p buf3'))))\<close>])
            apply (rule conjI[rotated, OF wbc_sym[OF wbc_base]])
            using that \<open>\<not> buf3 p \<noteq> []\<close> False buf1_not_empty
             apply (metis (mono_tags, opaque_lifting) BAPPEND_BTL)
            by (meson wstep_trans(1))
        qed
      qed
      ultimately show ?thesis
        using H1 H2 by (elim step_id_op_cases ; simp split: if_splits)
    qed
  qed
qed

lemma A11:
  \<open>\<C> \<bullet> \<Q> \<approx> \<I>\<close>
  unfolding scomp_op_def
  using A11_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A14: Equality test with 0 ports\<close>

lemma A14:
  \<open>(\<Q> :: (unit + unit, unit, 'd) op) ~ \<oslash>\<close>
  by (rule choices_Choice_bisim) (simp add: defaults_unit_def)

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

section \<open>Axiom A18: Acopy with 0 ports\<close>

lemma A18:
  \<open>(\<C> :: (unit, unit + unit, 'd) op) ~ \<oslash>\<close>
  by (rule choices_Choice_bisim) (simp add: defaults_unit_def)

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
        unfolding R_def by (intro exI conjI[rotated,OF wbc_base], force, force)
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


section \<open>Axiom F3: Loop equality test\<close>

lemma F3_gen:
  \<open>map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))
    (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1'))))
  \<approx> !\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1'))))) op1'"
    show "\<exists>op2'. wstep io sink_op op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1')))) \<and> op2 = sink_op) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_loop_op_elim step_aeq_op_elim) blast+
  next
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io sink_op op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op id Inr (aeq_op (case_sum buf1 buf1')))) \<and> op2 = sink_op) op1' op2'"
      using H by (elim step_sink_op) force
  qed
qed

lemma F3:
  \<open>map_op id Inr \<Q>\<up> \<approx> !\<close>
  unfolding feedback_op_def
  using F3_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom F4: Loop acopy\<close>

lemma F4:
  \<open>map_op Inr id \<C>\<up> ~ \<exclamdown>\<close>
proof (coinduction rule: bisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding sim_def feedback_op_def scomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<C>))) op1'"
    show "\<exists>op2'. step io (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op2' \<and> bisim_cong (\<lambda>s t. s = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<C>)) \<and> t = map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1' op2'"
      using H by (auto elim!: step_map_op_elim step_loop_op_elim step_acopy_op_elim)
  next
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<C>))) op2' \<and> bisim_cong (\<lambda>s t. s = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<C>)) \<and> t = map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1' op2'"
      using H by (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases)
  qed
qed

section \<open>Axiom F5\<close>

lemma F5_gen:
  "map_op projl projl
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. []))
       (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (case_sum buf4 (\<lambda> _. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda> _. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) ((id_op buf1) :: ('m :: {countable,defaults}, 'm,  'd) op) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda> _. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<approx>
    map_op projl projr (comp_op Some (\<lambda> _. []) (sink_buf_op (buf1 >> buf2>> buf3 >> buf4 >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))"
proof (coinduction arbitrary: buf1 buf2 buf3 buf4 buf5 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp pd x) (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pd x buf1)) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2'"
      if "pd \<notin> defaults"
      for x :: 'd
        and pd :: 'm
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum (BENQ x2 (BHD x2 buf3) buf4) (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum (BTL x2 buf3) (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2'"
      if "x2 \<notin> defaults"
        and "buf3 x2 \<noteq> []"
      for x2 :: 'm
      using that 
      using that 
      apply -
      apply (intro exI conjI[rotated, OF wbc_base])
      apply force
      apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum (BTL pb buf4) (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum (BENQ pb (BHD pb buf4) buf5) (\<lambda>_. [])))))))) op2'"
      if "buf4 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'm
      using that 
      apply -
      apply (intro exI conjI[rotated, OF wbc_base])
      apply force
      apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum (BENQ pc (BHD pc buf1) buf2) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pc buf1)) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2'"
      if "pc \<notin> defaults"
        and "buf1 pc \<noteq> []"
      for pc :: 'm
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2'"
      if "x1 \<notin> defaults"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'm
      using that 
      apply -
      apply (intro exI conjI[rotated, OF wbc_base])
      apply force
      apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
      done
    ultimately show ?thesis
      using SIM1 by (auto 0 0 elim !: step_aeq_op_elim step_acopy_op_elim step_transp_op_cases step_map_op_elim step_loop_op_elim step_comp_op_elim step_id_op_cases split: if_splits sum.splits)
  qed
next
  case SIM2
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp pa x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((BENQ pa x buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>))))"
      if "(pa::'m) \<notin> defaults"
      for io' :: "('m + 'a, 'a + 'm, 'd) IO"
        and op'' :: "('m + 'a, 'a + 'm, 'd) op"
        and p :: 'm
        and x :: 'd
        and op1' :: "('m, 'a, 'd) op"
        and pa :: 'm
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    then show ?thesis
      using SIM2 by (elim exE step_sink_buf_op conjE step_aeq_op_elim step_acopy_op_elim step_transp_op_cases step_map_op_elim step_loop_op_elim step_comp_op_elim step_id_op_cases ; simp split: if_splits sum.splits ; hypsubst_thin ?)
  qed
qed

lemma F5:
  "((\<I> \<parallel> \<C>) \<bullet> map_op reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Q>)) \<up> \<approx> ! \<bullet> \<exclamdown>"
  apply (rule wbisim_trans[rotated])
  apply (rule wbisim_scomp_op_cong)
  apply (rule bisim_wbisim)
  apply (rule sink_buf_op_sink)
  apply (rule wbisim_refl)
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using F5_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] apply force
  done

end