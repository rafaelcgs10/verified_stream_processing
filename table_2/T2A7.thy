theory T2A7

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)


section \<open>Axiom A7: Acopy to sink and identity\<close>

lemma A7_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1')) (! \<parallel> id_op buf3))
  \<approx> map_op id Inr (id_op (buf1' >> buf2' >> buf3))\<close>
  unfolding pcomp_op_def
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 rule: wbisim_coinduct)
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) op2' \<and> wbisim_R (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'c) op) (id_op buf3))) \<and> op2 = map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum (BENQ pa xa buf1) (BENQ pa xa buf1'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op (id_op buf3)))) op2'"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'c
      using that by force
    moreover have "\<exists>op2'. wstep (Out (Inr pb::'b + 'a) (BHD pb buf3)) (map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) op2' \<and> wbisim_R (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op (id_op buf3))) \<and> op2 = map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op (id_op (BTL pb buf3))))) op2'"
      if "pb \<notin> defaults"
        and "buf3 pb \<noteq> []"
      for pb :: 'a
      using that by (fastforce del: wbcr_base intro!: wbcr_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) op2' \<and> wbisim_R (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'c) op) (id_op buf3))) \<and> op2 = map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf1) buf2) buf2') (acopy_op (case_sum (BTL pa buf1) buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op (id_op buf3)))) op2'"
      if "buf1 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by force
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) op2' \<and> wbisim_R (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'c) op) (id_op buf3))) \<and> op2 = map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa buf1') buf2')) (acopy_op (case_sum buf1 (BTL pa buf1'))) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op (id_op buf3)))) op2'"
      if "buf1' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by force
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) op2' \<and> wbisim_R (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'c) op) (id_op buf3))) \<and> op2 = map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) (map_op projl projr (comp_op Some (case_sum (BTL pb buf2) buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op (id_op buf3)))) op2'"
      if "buf2 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that by force
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) op2' \<and> wbisim_R (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'b, 'c) op) (id_op buf3))) \<and> op2 = map_op id Inr (id_op ((buf1' >> buf2') >> buf3))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL pb buf2')) (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op (id_op (BENQ pb (BHD pb buf2') buf3))))) op2'"
      if "buf2' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that
      by (intro exI conjI[rotated, OF wbcr_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_sink_op step_id_op_cases)
  qed
next
  case SIM2
  then show ?case
    by (elim exE conjE step_map_op_elim step_id_op_cases; simp split: if_splits)
      (fastforce del: wbcr_base intro!: wbcr_base)+
qed

lemma A7:
  \<open>\<C> \<bullet> (! \<parallel> \<I>) \<approx> map_op id Inr \<I>\<close>
  unfolding scomp_op_def
  using A7_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end