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
        using that by (fastforce intro: bc_base)+
      moreover have "\<exists>op2'. step Tau (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (aeq_op (case_sum buf1 buf1'))) (aeq_op (case_sum buf3' buf3))))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa buf2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1 buf1')) (id_op buf1'')) (aeq_op (case_sum buf3 (BENQ pa (BHD pa buf2') buf3'))))) op2'"
        if "buf2' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce intro: bc_base)+
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
            (* from this that show ?thesis by (intro exI conjI[rotated, OF wbc_base], fastforce+) *)
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
        using that
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) by auto[1] fastforce
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
  unfolding pcomp_op_def
proof (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op (BENQ p x buf1)))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that by blast
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ pb (BHD pb buf1) buf2)) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op (BTL pb buf1)))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2'"
        if "pb \<notin> defaults"
          and "buf1 pb \<noteq> []"
        for pb :: 'a
        using that by blast
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BTL pa buf2)) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) (BENQ pa (BHD pa buf2) buf3))))) op2'"
        if "buf2 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by blast
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_aeq_op_elim)
    qed
  next
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp pa xa) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (map_op projr id (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('c, 'a, 'b) op) \<I>)) (id_op buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2 = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) (\<lambda>_. []) sink_op (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      then show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_sink_op step_id_op_cases)
    qed
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
  unfolding pcomp_op_def
proof (coinduction arbitrary: buf1 buf1' buf2 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a + 'a, 'b + 'c, 'd) IO"
      and op1' :: "('a + 'a, 'b + 'c, 'd) op"
    assume H: "step io (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) !)) op1'"
    show "\<exists>op2'. wstep io (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl pa) y) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'd) op) (sink_op::('a, 'c, 'd) op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum (BENQ pa y buf1) buf1')) sink_op)) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and y :: 'd
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. wstep (Inp (Inr pa) y) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'd) op) (sink_op::('a, 'c, 'd) op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 (BENQ pa y buf1'))) sink_op)) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and y :: 'd
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'd) op) (sink_op::('a, 'c, 'd) op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) (map_op projl projr (comp_op Some (BENQ pa (BHD pa buf1') buf2) (aeq_op (case_sum (BTL pa buf1) (BTL pa buf1'))) sink_op)) op2'"
        if "buf1 pa \<noteq> []"
          and "buf1' pa \<noteq> []"
          and "BHD pa buf1 = BHD pa buf1'"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'd) op) (sink_op::('a, 'c, 'd) op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) (map_op projl projr (comp_op Some (BTL pa buf2) (aeq_op (case_sum buf1 buf1')) sink_op)) op2'"
        if "buf2 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'd) op) (sink_op::('a, 'c, 'd) op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum (BTL pa buf1) (BTL pa buf1'))) sink_op)) op2'"
        if "buf1 pa \<noteq> []"
          and "buf1' pa \<noteq> []"
          and "BHD pa buf1 \<noteq> BHD pa buf1'"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro: wbc_base)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_sink_op)
    qed
  next
    fix io :: "('a + 'a, 'b + 'c, 'd) IO"
      and op1' :: "('a + 'a, 'b + 'c, 'd) op"
    assume H: "step io (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl pa) xa) (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'd) op) (sink_op::('a, 'c, 'd) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'd
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Inp (Inr pa) xa) (map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) op2' \<and> wbisim_cong (\<lambda>op1 op2. (\<exists>buf1 buf1' buf2. op1 = map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) sink_op)) \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'd) op) (sink_op::('a, 'c, 'd) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'd
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      ultimately show ?thesis
        using H by (auto elim !: step_comp_op_elim step_sink_op)
    qed
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
        using that by (fastforce del: wbc_base intro!: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BTL x1 buf3'))))) op2'"
        if "x1 \<notin> defaults"
          and "buf3' x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3)) (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum (BTL x2 buf3) buf3')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3 x2 \<noteq> []"
        for x2 :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf1) buf2) buf2') (acopy_op (case_sum (BTL pa buf1) buf1')) (transp_op (case_sum buf3 buf3')))) op2'"
        if "buf1 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa buf1') buf2')) (acopy_op (case_sum buf1 (BTL pa buf1'))) (transp_op (case_sum buf3 buf3')))) op2'"
        if "buf1' pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base)
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
  unfolding pcomp_op_def
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
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

lemma aux:
  "map_op projl projr (comp_op Some buf2 (aeq_op (case_sum buf1 buf1')) (id_op buf3)) \<approx> (aeq_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2 >> buf3)))"
  sorry

lemma
  "map_op projl projr (comp_op Some K (aeq_op (case_sum buf1 buf2)) (acopy_op B)) \<approx>
   map_op projl projr
   (comp_op Some (case_sum (case_sum buf1''' buf2''') (case_sum buf1''' buf2'''))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum buf1' buf1') (case_sum buf2' buf2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf1 buf1)) (acopy_op (case_sum buf2 buf2)))
         (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (transp_op (case_sum buf1'' buf2'')))) (id_op buf2'')))))
     (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum buf1'''' buf2''')) (aeq_op (case_sum buf1'''' buf2''''))))"
  oops


lemma A10:
  "\<Q> \<bullet> \<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q> \<parallel> \<Q>)"
  unfolding scomp_op_def pcomp_op_def
  oops

  section \<open>Axiom: A11: Acopy to equality test\<close>

lemma acopy_op_aeq_op_id_op_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf buf) \<C> \<Q>) \<approx> id_op buf\<close>
  oops

lemma acopy_op_aeq:
  "\<C> \<bullet> \<Q> \<approx> \<I>"
  oops

section \<open>Axiom A14: Equality test with 0 ports\<close>

lemma A14:
  \<open>(\<Q> :: ((unit + unit) + unit + unit, unit + unit, 'd) op) ~ \<oslash>\<close>
proof -
  have \<open>choices (\<Q> :: ((unit + unit) + unit + unit, unit + unit, 'd) op) = {||}\<close>
    by (subst aeq_op_code, auto simp add: defaults_unit_def sum_in_defaults)
  also have \<open>{||} = choices \<oslash>\<close> by simp
  finally show ?thesis by (rule choices_Choice_bisim)
qed

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
  \<open>(\<C> :: (unit + unit, (unit + unit) + unit + unit, 'd) op) ~ \<oslash>\<close>
proof -
  have \<open>choices (\<C> :: (unit + unit, (unit + unit) + unit + unit, 'd) op) = {||}\<close>
    by (subst acopy_op_code, auto simp add: defaults_unit_def sum_in_defaults)
  also have \<open>{||} = choices \<oslash>\<close> by simp
  finally show ?thesis by (rule choices_Choice_bisim)
qed

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
  unfolding feedback_op_def scomp_op_def
proof (coinduction rule: bisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding sim_def
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