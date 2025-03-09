theory A1

imports
  "../BNA_Operators"
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


end