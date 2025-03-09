theory A7

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)


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

end