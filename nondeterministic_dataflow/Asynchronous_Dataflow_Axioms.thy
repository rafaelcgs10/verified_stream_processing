\<comment> \<open>Axioms from Table 4 for merge test and split\<close>
theory Asynchronous_Dataflow_Axioms

imports
  BNA_Operators
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom: A1: Merge commutes with identity\<close>

lemma A1_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2') (merge_op (case_sum buf1 buf1') \<parallel> id_op buf1'') (merge_op (case_sum buf3 buf3')))
  ~ map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (id_op buf1'' \<parallel> merge_op (case_sum buf1 buf1')) (merge_op (case_sum buf3' buf3))))\<close>
proof (coinduction arbitrary: buf1 buf1' buf1'' buf2 buf2' buf3 buf3' rule: bisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding sim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "(('a + 'a) + 'a, 'a, 'b) IO"
      and op1' :: "(('a + 'a) + 'a, 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf1')) (id_op buf1'')) (merge_op (case_sum buf3 buf3')))) op1'"
    show "\<exists>op2'. step io (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (merge_op (case_sum buf1 buf1'))) (merge_op (case_sum buf3' buf3))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf1')) (id_op buf1'')) (merge_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (merge_op (case_sum buf1 buf1'))) (merge_op (case_sum buf3' buf3))))) op1' op2'"
      using H by (auto elim!: step_map_op_elim step_comp_op_elim step_merge_op_elim step_id_op_cases) (fastforce intro: bc_base)+
  next
    fix io :: "(('a + 'a) + 'a, 'a, 'b) IO"
      and op1' :: "(('a + 'a) + 'a, 'a, 'b) op"
    assume H: "step io (map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (merge_op (case_sum buf1 buf1'))) (merge_op (case_sum buf3' buf3))))) op1'"
    show "\<exists>op2'. step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf1')) (id_op buf1'')) (merge_op (case_sum buf3 buf3')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf1'' buf2 buf2' buf3 buf3'. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf1')) (id_op buf1'')) (merge_op (case_sum buf3 buf3'))) \<and> t = map_op (case_sum Inr Inl) id (map_op projl projr (comp_op Some (case_sum buf2' buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1'') (merge_op (case_sum buf1 buf1'))) (merge_op (case_sum buf3' buf3))))) op1' op2'"
      using H by (auto elim!: step_map_op_elim step_comp_op_elim step_merge_op_elim step_id_op_cases) (fastforce intro: bc_sym[OF bc_base])+
  qed
qed

lemma A1:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V> ~ map_op (case_sum Inr Inl) id ((\<I> \<parallel> \<V>) \<bullet> \<V>)\<close>
  unfolding scomp_op_def
  using A1_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom: A2: Merge transpose is merge\<close>
lemma merge_op_transp_op:
  "\<X> \<bullet> \<V> \<approx> \<V>"
  oops

section \<open>Axiom: A3: Merge dummy source and identity\<close>
lemma merge_op_dummy_source_op:
  "map_op projr id (\<exclamdown> \<parallel> \<I>) \<bullet> \<V> \<approx> \<I>"
  oops

section \<open>Axiom: A4: Merge to sink\<close>
lemma merge_op_sink_op:
   "\<V> \<bullet> ! ~ ! \<parallel> !"
  oops

section \<open>Axiom A6: Split to transpose\<close>

lemma A6_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))
  \<approx> map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'a + 'a, 'b) IO"
      and op1' :: "('a, 'a + 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op1'"
    show "\<exists>op2'. wstep io (map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp pa xa) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum (BENQ pa xa buf1) buf1')) (transp_op (case_sum buf3 buf3')))) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'b
        using that by (fastforce del: wbc_base intro!: wbc_base wstep_map_op[of \<open>Inp pa xa\<close>])
      moreover have "\<exists>op2'. wstep (Inp pa xa) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 (BENQ pa xa buf1'))) (transp_op (case_sum buf3 buf3')))) op2'"
        if "pa \<notin> defaults"
        for pa :: 'a
          and xa :: 'b
        using that by (fastforce del: wbc_base intro!: wbc_base wstep_map_op[of \<open>Inp pa xa\<close>])
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BTL x1 buf3'))))) op2'"
        if "x1 \<notin> defaults"
          and "buf3' x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base wstep_map_op[of \<open>Out (Inr x1) (BHD x1 buf3')\<close>])
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3)) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum (BTL x2 buf3) buf3')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3 x2 \<noteq> []"
        for x2 :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base wstep_map_op[of \<open>Out (Inl x2) (BHD x2 buf3)\<close>])
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (split_op (case_sum (BTL x1 buf1) buf1')) (transp_op (case_sum buf3 buf3')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1 x1 \<noteq> []"
        for x1 :: 'a
        using that by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1') buf2')) (split_op (case_sum buf1 (BTL x2 buf1'))) (transp_op (case_sum buf3 buf3')))) op2'"
        if "x2 \<notin> defaults"
          and "buf1' x2 \<noteq> []"
        for x2 :: 'a
        using that by force
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3')))) op2'"
        if "x1 \<notin> defaults"
          and "buf2 x1 \<noteq> []"
        for x1 :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2')) (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BENQ x2 (BHD x2 buf2') buf3'))))) op2'"
        if "x2 \<notin> defaults"
          and "buf2' x2 \<noteq> []"
        for x2 :: 'a
        using that
        by (intro exI conjI[rotated, OF wbc_base], simp, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_split_op_cases step_transp_op_cases split: sum.splits)
    qed
  next
    fix io :: "('a, 'a + 'a, 'b) IO"
      and op1' :: "('a, 'a + 'a, 'b) op"
    assume H: "step io (map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3')))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((BENQ p x buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that by force
      moreover have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((BENQ p x buf1' >> buf2') >> buf3')))) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that by (fastforce intro!: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inr x1a) (BHD x1a buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((BTL x1a buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "buf1 x1a \<noteq> []"
          and "x1a \<notin> defaults"
          and "buf2 x1a = []"
          and "buf3 x1a = []"
        for x1a :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum (BENQ x1a (BHD x1a buf1) buf2) buf2')
    (split_op (case_sum (BTL x1a buf1) buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        also have \<open>step Tau \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum (BTL x1a buf1) buf1')) (transp_op (case_sum (BENQ x1a (BHD x1a buf1) buf3) buf3'))))\<close>
          using that by auto
        also have \<open>step (Out (Inr x1a) (BHD x1a buf1)) \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum (BTL x1a buf1) buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inr x1a)) (BHD x1a buf1)\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x1a) (BHD x1a buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> BTL x1a buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "x1a \<notin> defaults"
          and "buf2 x1a \<noteq> []"
          and "buf3 x1a = []"
        for x1a :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum (BTL x1a buf2) buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum (BENQ x1a (BHD x1a buf2) buf3) buf3'))))\<close>
          using that by auto
        also have \<open>step (Out (Inr x1a) (BHD x1a buf2)) \<dots>
    (map_op projl projr (comp_op Some (case_sum (BTL x1a buf2) buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inr x1a)) (BHD x1a buf2)\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x1a) (BHD x1a buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> BTL x1a buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "x1a \<notin> defaults"
          and "buf2 x1a = []"
          and "buf3 x1a \<noteq> []"
        for x1a :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], force+)
      moreover have "\<exists>op2'. wstep (Out (Inr x1a) (BHD x1a buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> BTL x1a buf3) ((buf1' >> buf2') >> buf3')))) op2'"
        if "x1a \<notin> defaults"
          and "buf2 x1a \<noteq> []"
          and "buf3 x1a \<noteq> []"
        for x1a :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], force+)
      moreover have "\<exists>op2'. wstep (Out (Inl x2a) (BHD x2a buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2a buf1' >> buf2') >> buf3')))) op2'"
        if "buf1' x2a \<noteq> []"
          and "x2a \<notin> defaults"
          and "buf2' x2a = []"
          and "buf3' x2a = []"
        for x2a :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2a (BHD x2a buf1') buf2'))
    (split_op (case_sum buf1 (BTL x2a buf1'))) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by auto
        also have \<open>step Tau \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 (BTL x2a buf1'))) (transp_op (case_sum buf3 (BENQ x2a (BHD x2a buf1') buf3')))))\<close>
          using that by auto
        also have \<open>step (Out (Inl x2a) (BHD x2a buf1')) \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 (BTL x2a buf1'))) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inl x2a)) (BHD x2a buf1')\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x2a) (BHD x2a buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2a buf2') >> buf3')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2' x2a \<noteq> []"
          and "buf3' x2a = []"
        for x2a :: 'a
      proof -
        have \<open>step Tau (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))
    (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2a buf2'))
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BENQ x2a (BHD x2a buf2') buf3')))))\<close>
          using that by auto
        also have \<open>step (Out (Inl x2a) (BHD x2a buf2')) \<dots>
    (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2a buf2'))
    (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))))\<close>
          using that by (auto intro!: step_map_op[of \<open>Out (Inr (Inl x2a)) (BHD x2a buf2')\<close>])
        finally show ?thesis by (fastforce intro: wbc_sym[OF wbc_base])
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x2a) (BHD x2a buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> BTL x2a buf3')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2' x2a = []"
          and "buf3' x2a \<noteq> []"
        for x2a :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], force+)
      moreover have "\<exists>op2'. wstep (Out (Inl x2a) (BHD x2a buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3'))) \<and> op2 = map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) (map_op id (case_sum Inr Inl) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> BTL x2a buf3')))) op2'"
        if "x2a \<notin> defaults"
          and "buf2' x2a \<noteq> []"
          and "buf3' x2a \<noteq> []"
        for x2a :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]], force+)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_split_op_cases split: sum.splits if_splits)
    qed
  qed
qed

lemma A6:
  \<open>\<Lambda> \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<Lambda>\<close>
  unfolding scomp_op_def
  using A6_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom: A8: Split dummy source\<close>

lemma split_op_dummy_source:
  \<open>\<exclamdown> \<bullet> \<Lambda> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def
  apply (rule conjI)
  subgoal
    unfolding scomp_op_def pcomp_op_def
    apply (subst comp_op_code)
    apply (subst split_op_code)
    apply auto
    done
  subgoal
    apply (metis cempty_iff choices_pcomp_op_dummy_source step_choicesE)
    done
  done

section \<open>Axiom: A9\<close>

lemma dummy_source_op_sink_op:
  \<open>\<exclamdown> \<bullet> ! ~ \<oslash>\<close>
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def scomp_op_def
  apply auto
  apply (drule step_map_op_inv)
  apply auto
  apply (drule step_comp_op_cases)
  apply auto
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    done
  subgoal
    using no_step_sink_op_Out
    apply fastforce
    done
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    apply (drule step_id_op_Out)
     apply auto
    done
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    done
  subgoal
    using no_step_id_op_Tau no_step_sink_op_Tau
     apply blast+
    done
  done

section \<open>Axiom A12: Dummy source with 0 ports is end_op\<close>

lemma A12:
  \<open>(\<exclamdown> :: (unit, unit, 'd) op) ~ \<oslash>\<close>
proof -
  have \<open>choices (\<exclamdown> :: (unit, unit, 'd) op) = {||}\<close> by simp
  also have \<open>{||} = choices \<oslash>\<close> by simp
  finally show ?thesis by (rule choices_Choice_bisim)
qed

(*
lemma A12:
  \<open>\<exclamdown> ~ \<oslash>\<close>
proof -
  have \<open>choices \<exclamdown> = {||}\<close> by simp
  also have \<open>{||} = choices \<oslash>\<close> by simp
  finally show ?thesis by (rule choices_Choice_bisim)
qed
*)

section \<open>Axiom A13: Parallel dummy source\<close>

lemma dummy_source_op_pcomp_op:
  \<open>\<exclamdown> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply (rule choices_Choice_bisim)
  apply (simp add: choices_pcomp_op_dummy_source)
  done

section \<open>Axiom A15: Transpose and merge\<close>

lemma A15_gen:
  \<open>merge_op (case_sum
    (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3''))
    (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3''')))
  \<approx> map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
       (map_op reassoc reassoc (map_op assoc assoc
      (id_op buf1 \<parallel> transp_op (case_sum buf1' buf1'')) \<parallel> id_op buf1'''))
      (merge_op (case_sum buf3 buf3') \<parallel> merge_op (case_sum buf3'' buf3''')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3''' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding wsim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "(('a + 'b) + 'a + 'b, 'a + 'b, 'c) IO"
      and op1' :: "(('a + 'b) + 'a + 'b, 'a + 'b, 'c) op"
    assume H: "step io (merge_op (case_sum (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3'')) (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3''')))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3'')) (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl p) x) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (BENQ p x (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3''))) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "p \<notin> defaults"
        for p :: "'a + 'b"
          and x :: 'c
      proof (cases p)
        case (Inl a)
        from this that show ?thesis
          by (fastforce del: wbc_base intro!: wbc_base)
      next
        case (Inr b)
        from this that show ?thesis
          by (fastforce del: wbc_base intro!: wbc_base)
      qed
      moreover have "\<exists>op2'. wstep (Inp (Inr p) x) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (BENQ p x (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))))) op2'"
        if "p \<notin> defaults"
        for p :: "'a + 'b"
          and x :: 'c
      proof (cases p)
        case (Inl a)
        from this that show ?thesis
          by (fastforce del: wbc_base intro!: wbc_base)
      next
        case (Inr b)
        from this that show ?thesis
          by (fastforce del: wbc_base intro!: wbc_base)
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf1)) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1 x1 \<noteq> []"
          and "buf3 x1 = []"
          and "buf2 x1 = []"
        for x1 :: 'a
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op (BTL x1 buf1))
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op (BTL x1 buf1))
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step (Out (Inl x1) (BHD x1 buf1)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op (BTL x1 buf1))
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inl x1)) (BHD x1 buf1)\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_L)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply blast
          by (meson wstep_trans(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2)) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf3 x1 = []"
          and "buf2 x1 \<noteq> []"
        for x1 :: 'a
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step (Out (Inl x1) (BHD x1 buf2)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 buf2) buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inl x1)) (BHD x1 buf2)\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_L)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply blast
          by (meson wstep_trans_base(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3)) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf3 x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf1' x2 \<noteq> []"
          and "buf3'' x2 = []"
          and "buf2'' x2 = []"
        for x2 :: 'b
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
           apply (rule step_Tau_comp_op_L[of \<open>Inr (Inl x2)\<close> \<open>BHD x2 buf1'\<close>])
          using that
              apply force
          by auto
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum (BENQ x2 (BHD x2 buf1') buf3'') buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step (Out (Inr x2) (BHD x2 buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum (BTL x2 buf1') buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inr x2)) (BHD x2 buf1')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_L)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply blast
          by (meson wstep_trans(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf2'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3'' x2 = []"
          and "buf2'' x2 \<noteq> []"
        for x2 :: 'b
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum (BENQ x2 (BHD x2 buf2'') buf3'') buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step (Out (Inr x2) (BHD x2 buf2'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL x2 buf2'') buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inr x2)) (BHD x2 buf2'')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_L)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply blast
          by (meson wstep_trans_base(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> BTL x2 buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3'' x2 \<noteq> []"
        for x2 :: 'b
        using that by (fastforce del: wbc_base intro!: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf1'')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((BTL x1 buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf1'' x1 \<noteq> []"
          and "buf3' x1 = []"
          and "buf2' x1 = []"
        for x1 :: 'a
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
           apply (rule step_Tau_comp_op_L[of \<open>Inl (Inr x1)\<close> \<open>BHD x1 buf1''\<close>])
          using that
              apply force
          by auto
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 (BENQ x1 (BHD x1 buf1'') buf3')))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step (Out (Inl x1) (BHD x1 buf1'')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' (BTL x1 buf1'')))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inl x1)) (BHD x1 buf1'')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_R)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply blast
          by (meson wstep_trans(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> BTL x1 buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf3' x1 = []"
          and "buf2' x1 \<noteq> []"
        for x1 :: 'a
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 (BENQ x1 (BHD x1 buf2') buf3')))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step (Out (Inl x1) (BHD x1 buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL x1 buf2')) (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inl x1)) (BHD x1 buf2')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_R)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply blast
          by (meson wstep_trans_base(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> BTL x1 buf3') ((buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x1 \<notin> defaults"
          and "buf3' x1 \<noteq> []"
        for x1 :: 'a
        using that by (fastforce del: wbc_base intro!: wbc_base)
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((BTL x2 buf1''' >> buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf1''' x2 \<noteq> []"
          and "buf3''' x2 = []"
          and "buf2''' x2 = []"
        for x2 :: 'b
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ x2 (BHD x2 buf1''') buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' (BENQ x2 (BHD x2 buf1''') buf3'''))))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step (Out (Inr x2) (BHD x2 buf1''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op (BTL x2 buf1'''))))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inr x2)) (BHD x2 buf1''')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_R)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply blast
          by (meson wstep_trans(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf2''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> BTL x2 buf2''') >> buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3''' x2 = []"
          and "buf2''' x2 \<noteq> []"
        for x2 :: 'b
      proof -
        have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2'''))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' (BENQ x2 (BHD x2 buf2''') buf3'''))))))\<close>
          apply (rule step_map_op[of Tau])
          using that by fastforce+
        also have \<open>step (Out (Inr x2) (BHD x2 buf2''')) \<dots>
  (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL x2 buf2''')))
    (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (id_op buf1)
      (transp_op (case_sum buf1' buf1''))))
      (id_op buf1''')))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (merge_op (case_sum buf3 buf3'))
      (merge_op (case_sum buf3'' buf3''')))))\<close>
          apply (rule step_map_op[of \<open>Out (Inr (Inr x2)) (BHD x2 buf2''')\<close>])
          using that
          by (simp_all add: step_comp_op_L_Out step_comp_op_R_Out step_merge_op_Write_R)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply blast
          by (meson wstep_trans_base(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3''')) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> BTL x2 buf3''')))) op2'"
        if "x2 \<notin> defaults"
          and "buf3''' x2 \<noteq> []"
        for x2 :: 'b
        using that by (fastforce del: wbc_base intro!: wbc_base)
      ultimately show ?thesis
        using H by (auto elim !: step_merge_op_elim split: sum.splits if_splits)
    qed
  next
    fix io :: "(('a + 'b) + 'a + 'b, 'a + 'b, 'c) IO"
      and op1' :: "(('a + 'b) + 'a + 'b, 'a + 'b, 'c) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op1'"
    show "\<exists>op2'. wstep io (merge_op (case_sum (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3'')) (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2'' >> buf3'')) (case_sum (buf1'' >> buf2' >> buf3') (buf1''' >> buf2''' >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (Inl (Inl pc)) x) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pc x buf1)) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "pc \<notin> defaults"
        for x :: 'c
          and pc :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Inp (Inl (Inr x1a)) x) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum (BENQ x1a x buf1') buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "x1a \<notin> defaults"
        for x :: 'c
          and x1a :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Inp (Inr (Inl x2)) x) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' (BENQ x2 x buf1''))))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "x2 \<notin> defaults"
        for x :: 'c
          and x2 :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Inp (Inr (Inr pb)) x) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op (BENQ pb x buf1''')))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "pb \<notin> defaults"
        for x :: 'c
          and pb :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inr pb) (BHD pb buf3'')) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum (BTL pb buf3'') buf3'''))))) op2'"
        if "buf3'' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inr pb) (BHD pb buf3''')) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' (BTL pb buf3''')))))) op2'"
        if "buf3''' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'b
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inl pb) (BHD pb buf3)) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL pb buf3) buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "buf3 pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. wstep (Out (Inl pb) (BHD pb buf3')) (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 (BTL pb buf3'))) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "buf3' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that by (fastforce intro: wbc_sym[OF wbc_base])
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BENQ pb (BHD pb buf1''') buf2'''))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op (BTL pb buf1''')))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "pb \<notin> defaults"
          and "buf1''' pb \<noteq> []"
        for pb :: 'b
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) auto
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BENQ x1 (BHD x1 buf1'') buf2')) (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' (BTL x1 buf1''))))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf1'' x1 \<noteq> []"
        for x1 :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) auto
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BENQ x2 (BHD x2 buf1') buf2'') buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum (BTL x2 buf1') buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf1' x2 \<noteq> []"
        for x2 :: 'b
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) auto
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ pc (BHD pc buf1) buf2) buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pc buf1)) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "pc \<notin> defaults"
          and "buf1 pc \<noteq> []"
        for pc :: 'a
        using that by (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]]) auto
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum (BTL pb buf2) buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ pb (BHD pb buf2) buf3) buf3')) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "buf2 pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
         apply blast
        by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 (BTL pb buf2')) (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 (BENQ pb (BHD pb buf2') buf3'))) (merge_op (case_sum buf3'' buf3'''))))) op2'"
        if "buf2' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'a
        using that
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
         apply blast
        by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum (BTL pb buf2'') buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum (BENQ pb (BHD pb buf2'') buf3'') buf3'''))))) op2'"
        if "buf2'' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'b
        using that
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
         apply blast
        by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3''')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' buf3 buf3' buf3'' buf3'''. op1 = merge_op (case_sum (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2'') >> buf3'')) (case_sum ((buf1'' >> buf2') >> buf3') ((buf1''' >> buf2''') >> buf3'''))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' buf2''')) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' buf3'''))))) (map_op projl projr (comp_op Some (case_sum (case_sum buf2 buf2') (case_sum buf2'' (BTL pb buf2'''))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (transp_op (case_sum buf1' buf1'')))) (id_op buf1'''))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf3 buf3')) (merge_op (case_sum buf3'' (BENQ pb (BHD pb buf2''') buf3''')))))) op2'"
        if "buf2''' pb \<noteq> []"
          and "pb \<notin> defaults"
        for pb :: 'b
        using that
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
         apply blast
        by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      ultimately show ?thesis
        using H by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_transp_op_cases step_merge_op_elim split: sum.splits)
    qed
  qed
qed

lemma A15:
  assumes \<open>Vmn = (\<V> :: (('m :: {countable, defaults} + 'n :: {countable, defaults}) + 'm + 'n, 'm + 'n, 'd) op)\<close>
    and \<open>Vm = (\<V> :: ('m + 'm, 'm, 'd) op)\<close>
    and \<open>Vn = (\<V> :: ('n + 'n, 'n, 'd) op)\<close>
    and \<open>Imm = (\<I> :: ('m, 'm, 'd) op)\<close>
    and \<open>Inn = (\<I> :: ('n, 'n, 'd) op)\<close>
    and \<open>Xnm = (\<X> :: ('n + 'm, 'm + 'n, 'd) op)\<close>
  shows \<open>Vmn \<approx> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xnm) \<parallel> Inn) \<bullet> (Vm \<parallel> Vn)\<close>
  unfolding scomp_op_def
  using assms A15_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A16: Sink with 0 ports is end_op\<close>

lemma A16:
  \<open>(! :: (unit, unit, 'd) op) ~ \<oslash>\<close>
proof -
  have \<open>choices (! :: (unit, unit, 'd) op) = {||}\<close> by (auto simp add: defaults_unit_def sum_in_defaults)
  also have \<open>{||} = choices \<oslash>\<close> by simp
  finally show ?thesis by (rule choices_Choice_bisim)
qed

section \<open>Axiom A17: Parallel sink\<close>
lemma sink_op_pcomp_op_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf1' buf2') (id_op (case_sum buf1 buf2)) sink_op)
  ~ (map_op projl projr (comp_op Some buf1' (id_op buf1) sink_op)) \<parallel> (map_op projl projr (comp_op Some buf2' (id_op buf2) sink_op))\<close>
  apply (coinduction arbitrary: buf1 buf1' buf2 buf2' rule: bisim_coinduct_upto)
  subgoal for buf1 buf1' buf2 buf2'
    unfolding sim_def pcomp_op_def
    apply auto
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_id_op_Inp)
         apply simp
        apply (cases p)
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op (BENQ p' x buf1)) sink_op))
          (map_op projl projr (comp_op Some buf2' (id_op buf2) sink_op))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply auto
          done
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op buf1) sink_op))
          (map_op projl projr (comp_op Some buf2' (id_op (BENQ p' x buf2)) sink_op))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal
        using no_step_sink_op_Out
        apply meson
        done
      subgoal for p x
        apply (drule step_id_op_Out)
         apply (simp_all split: sum.splits)
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BENQ p' x buf1') (id_op (BTL p' buf1)) sink_op))
          (map_op projl projr (comp_op Some buf2' (id_op buf2) sink_op))\<close>])
          apply (rule conjI)
          apply safe
           apply hypsubst_thin
           apply (rule step_comp_op_L_Tau)
          apply auto
          apply (rule bc_base)
          apply auto
          done
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op buf1) sink_op))
          (map_op projl projr (comp_op Some (BENQ p' x buf2') (id_op (BTL p' buf2)) sink_op))\<close>])
          apply (rule conjI)
  apply (rule step_comp_op_R_Tau)
          apply auto
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal for p
        apply (erule step_sink_op_Inp)
        apply (auto split: sum.splits)
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BTL p' buf1') (id_op buf1) sink_op))
       (map_op projl projr (comp_op Some buf2' (id_op buf2) sink_op))\<close>])
          apply (rule conjI)
       apply (rule step_comp_op_L_Tau)
             apply auto
          apply (rule bc_base)
          apply fast
          done
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op buf1) sink_op))
       (map_op projl projr (comp_op Some (BTL p' buf2') (id_op buf2) sink_op))\<close>])
          apply (rule conjI)
           apply (rule step_comp_op_R_Tau)
          apply auto
          apply (rule bc_base)
          apply fast
          done
        done
      using no_step_id_op_Tau no_step_sink_op_Tau
       apply meson+
      done
    subgoal for io
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        apply (drule step_id_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf1' buf2') (id_op (case_sum (BENQ p x buf1) buf2)) sink_op)\<close>])
        apply (rule conjI)
        subgoal
          apply (rule step_map_op[of \<open>Inp (Inl (Inl p)) x\<close>])
           apply simp_all
          apply (rule step_comp_op_L_Inp)
          apply auto
          done
        subgoal
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        using no_step_sink_op_Out
        apply meson
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        using no_step_sink_op_Out
        apply meson
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        apply (drule step_id_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf1' buf2') (id_op (case_sum buf1 (BENQ p x buf2))) sink_op)\<close>])
        apply (rule conjI)
        subgoal
          apply (rule step_map_op[of \<open>Inp (Inl (Inr p)) x\<close>])
           apply simp_all
          apply (rule step_comp_op_L_Inp)
          apply auto
          done
        subgoal
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p x
          apply (drule step_id_op_Out)
           apply simp
          apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BENQ p x buf1') buf2') (id_op (case_sum (BTL p buf1) buf2)) sink_op)\<close>])
          apply (rule conjI)
              apply auto[1]
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        subgoal for p
          apply (erule step_sink_op_Inp)
           apply simp
          apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf1') buf2') (id_op (case_sum buf1 buf2)) sink_op)\<close>])
          apply (rule conjI)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
              apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        using no_step_id_op_Tau no_step_sink_op_Tau
         apply meson+
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p x
          apply (drule step_id_op_Out)
           apply simp
          apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf1' (BENQ p x buf2')) (id_op (case_sum buf1 (BTL p buf2))) sink_op)\<close>])
          apply (rule conjI)
          apply auto[1]
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        subgoal for p
          apply (erule step_sink_op_Inp)
           apply simp
          apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf1' (BTL p buf2')) (id_op (case_sum buf1 buf2)) sink_op)\<close>])
          apply (rule conjI)
          apply auto[1]
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        using no_step_id_op_Tau no_step_sink_op_Tau
         apply meson+
        done
      done
    done
  done 

lemma sink_op_pcomp_op:
  \<open>! ~ ! \<parallel> !\<close>
  unfolding pcomp_op_def
proof (coinduction rule: bisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. step io (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. op1xx = ! \<and> (op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)) op1' op2'"
      if "io = Inp p x"
        and "p \<notin> defaults"
        and "op1' = !"
      for p :: "'a + 'b"
        and x :: 'e
      using that 
    proof (cases p)
      case (Inl a)
      from this that show ?thesis 
        by (intro exI conjI[rotated, OF bc_base], force, force)
    next
      case (Inr b)
      from this that show ?thesis 
        by (intro exI conjI[rotated, OF bc_base], force, force)
    qed
    then show ?thesis
      using SIM1  by (elim step_sink_op)
  qed
next
  case SIM2
  then show ?case 
    explore (elim step_comp_op_elim step_sink_op; simp split: sum.splits; hypsubst_thin?)
  proof -
    have "\<exists>op2'. step (Inp (Inl pa) x) sink_op op2' \<and> bisim_cong (\<lambda>op1xx op2xx. op1xx = sink_op \<and> op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) op2' (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      if "(pa::'a) \<notin> defaults"
        and "step (Inp (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
        and "step (Inp (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      for p :: 'a
        and x :: 'e
        and op1' :: "('a, 'c, 'e) op"
        and pa :: 'a
      using that
      by (intro exI conjI[rotated, OF bc_base], force, force)
    moreover have "\<exists>op2'. step (Inp (Inr pa) x) sink_op op2' \<and> bisim_cong (\<lambda>op1xx op2xx. op1xx = sink_op \<and> op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) op2' (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      if "pa \<notin> defaults"
        and "step (Inp (Inr pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
        and "step (Inp (Inr pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      for p :: 'b
        and x :: 'e
        and op2' :: "('b, 'd, 'e) op"
        and pa :: 'b
      using that    
      by (intro exI conjI[rotated, OF bc_base], force, force)
    ultimately show ?thesis
      using SIM2 by (elim step_comp_op_elim step_sink_op ; simp split: sum.splits ; hypsubst_thin ?)
  qed
qed

section \<open>Axiom A18: Split with 0 ports\<close>

lemma A18:
  \<open>(\<Lambda> :: (unit + unit, (unit + unit) + unit + unit, 'd) op) ~ \<oslash>\<close>
proof -
  have \<open>choices (\<Lambda> :: (unit + unit, (unit + unit) + unit + unit, 'd) op) = {||}\<close>
    by (subst split_op_code, auto simp add: defaults_unit_def sum_in_defaults)
  also have \<open>{||} = choices \<oslash>\<close> by simp
  finally show ?thesis by (rule choices_Choice_bisim)
qed

section \<open>Axiom A19\<close>
lemma split_op_transp_split_gen:
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
          apply force
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
        apply force
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
        apply force
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
        using H by (auto 0 0 elim !: step_map_op_elim step_split_op_cases step_transp_op_cases step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
    qed
  qed
qed

lemma split_op_transp_split:
  assumes "Smn = (\<Lambda> :: ('m + 'n,('m :: {countable, defaults}+ 'n :: {countable, defaults}) + 'm + 'n,  'd) op)"
    and "Sm = (\<Lambda> :: ('m, 'm + 'm, 'd) op)"
    and "Sn = (\<Lambda> :: ('n, 'n + 'n, 'd) op)"
    and "Imm = (\<I> :: ('m, 'm, 'd) op)"
    and "Inn = (\<I> :: ('n, 'n, 'd) op)"
    and "Xmn = (\<X> :: ('m + 'n, 'n + 'm, 'd) op)"
  shows "Smn \<approx> (Sm \<parallel> Sn) \<bullet> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xmn) \<parallel> Inn)"
  unfolding scomp_op_def pcomp_op_def
  using assms split_op_transp_split_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by simp

section \<open>Axiom F3: Loop merge\<close>
lemma loop_op_merge_sink:
  "map_op id Inr \<V>\<up> ~ !"
  oops

section \<open>Axiom F4: Loop split\<close>

lemma F4:
  \<open>map_op Inr id \<Lambda>\<up> ~ \<exclamdown>\<close>
  unfolding feedback_op_def scomp_op_def
proof (coinduction rule: bisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding sim_def
  proof (intro allI conjI impI)
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<Lambda>))) op1'"
    show "\<exists>op2'. step io (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op2' \<and> bisim_cong (\<lambda>s t. s = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<Lambda>)) \<and> t = map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1' op2'"
      using H by (auto elim!: step_map_op_elim step_loop_op_elim step_split_op_cases)
  next
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume H: "step io (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<Lambda>))) op2' \<and> bisim_cong (\<lambda>s t. s = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op Inr id \<Lambda>)) \<and> t = map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) op1' op2'"
      using H by (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases)
  qed
qed

end