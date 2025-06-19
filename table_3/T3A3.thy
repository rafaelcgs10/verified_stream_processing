theory T3A3

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A3: Merge dummy source and identity\<close>

lemma A3_gen:
  \<open>map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>) \<parallel> id_op buf1)
    (merge_op (case_sum (\<lambda>_. []) buf3)))
  \<approx> map_op Inr id (id_op (buf1 >> buf2 >> buf3))\<close>
  unfolding pcomp_op_def
proof (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inr pb::'a + 'b) xb) (map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op (BENQ pb xb buf1))) (merge_op (case_sum (\<lambda>_. []) buf3)))) op2'"
      if "pb \<notin> defaults"
      for pb :: 'b
        and xb :: 'c
        using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3)) (map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'b, 'c) op) \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) (BTL pa buf3))))) op2'"
      if "buf3 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'b
        using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'b, 'c) op) \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ pb (BHD pb buf1) buf2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op (BTL pb buf1))) (merge_op (case_sum (\<lambda>_. []) buf3)))) op2'"
      if "pb \<notin> defaults"
        and "buf1 pb \<noteq> []"
      for pb :: 'b
        using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'b, 'c) op) \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BTL pa buf2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) (BENQ pa (BHD pa buf2) buf3))))) op2'"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'b
      using that
      by (intro exI conjI[rotated, OF wbc_base], blast, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inr p::'a + 'b) x) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) op2' (map_op Inr id (id_op ((BENQ p x buf1 >> buf2) >> buf3)))"
      if "p \<notin> defaults"
      for p :: 'b
        and x :: 'c
      using that by (fastforce intro: wbc_sym[OF wbc_base]  del: wstep_loop_Inp intro!: wstep_loop_Inp)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1)) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'b, 'c) op) \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) op2' (map_op Inr id (id_op ((BTL p buf1 >> buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "buf1 p \<noteq> []"
        and "buf3 p = []"
        and "buf2 p = []"
      for p :: 'b
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1))
    (merge_op (case_sum (\<lambda>_. []) buf3))))
  (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ p (BHD p buf1) buf2))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op (BTL p buf1)))
    (merge_op (case_sum (\<lambda>_. []) buf3))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op (BTL p buf1)))
    (merge_op (case_sum (\<lambda>_. []) (BENQ p (BHD p buf1) buf3)))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf1)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op (BTL p buf1)))
    (merge_op (case_sum (\<lambda>_. []) buf3))))\<close>
        using that by force
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2)) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'b, 'c) op) \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) op2' (map_op Inr id (id_op ((buf1 >> BTL p buf2) >> buf3)))"
      if "p \<notin> defaults"
        and "buf3 p = []"
        and "buf2 p \<noteq> []"
      for p :: 'b
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1))
    (merge_op (case_sum (\<lambda>_. []) buf3))))
  (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BTL p buf2))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1))
    (merge_op (case_sum (\<lambda>_. []) (BENQ p (BHD p buf2) buf3)))))\<close>
        using that by auto[1] fastforce
      also have \<open>step (Out p (BHD p buf2)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BTL p buf2))
    (comp_op (\<lambda>_. None) (\<lambda>_. [])
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1))
    (merge_op (case_sum (\<lambda>_. []) buf3))))\<close>
        using that by force
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3)) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'b, 'c) op) \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3. op1 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (merge_op (case_sum (\<lambda>_. []) buf3))) \<and> op2 = map_op Inr id (id_op ((buf1 >> buf2) >> buf3))) op2' (map_op Inr id (id_op ((buf1 >> buf2) >> BTL p buf3)))"
      if "p \<notin> defaults"
        and "buf3 p \<noteq> []"
      for p :: 'b
        using that by (fastforce del: wbc_base intro!: wbc_base)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_id_op_cases split: if_splits)
  qed
qed

lemma A3:
  \<open>(\<exclamdown> \<parallel> \<I>) \<bullet> \<V> \<approx> map_op Inr id \<I>\<close>
  unfolding scomp_op_def
  using A3_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

end