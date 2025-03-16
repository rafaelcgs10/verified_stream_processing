theory B7

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)


section \<open>Axiom B7: Transpose of transpose is identity\<close>

lemma comp_op_transp_transp_id_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3)))
  \<approx> id_op (case_sum (l1 >> l2 >> l3) (r1 >> r2 >> r3))\<close>
proof (coinduction arbitrary: l1 l2 l3 r1 r2 r3 rule: wbisim_coinduct)
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (BENQ pa xa (case_sum l1 r1))) (transp_op (case_sum r3 l3)))) op2'"
      if "pa \<notin> defaults"
      for pa :: "'a + 'b"
        and xa :: 'c
      using that 
    proof (cases pa)
      case (Inl a)
      from this that show ?thesis by (intro exI conjI[rotated] wbcr_base; force)
    next
      case (Inr b)
      from this that show ?thesis by (intro exI conjI[rotated] wbcr_base; force)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 l3)) (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 (BTL x1 l3))))) op2'"
      if "x1 \<notin> defaults"
        and "l3 x1 \<noteq> []"
      for x1 :: 'a
      using that by (intro exI conjI[rotated] wbcr_base; force)
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 r3)) (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum (BTL x2 r3) l3)))) op2'"
      if "x2 \<notin> defaults"
        and "r3 x2 \<noteq> []"
      for x2 :: 'b
      using that by (intro exI conjI[rotated] wbcr_base; force)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 r1) r2) l2) (transp_op (case_sum l1 (BTL x1 r1))) (transp_op (case_sum r3 l3)))) op2'"
      if "x1 \<notin> defaults"
        and "r1 x1 \<noteq> []"
      for x1 :: 'b
      using that by (intro exI conjI[rotated] wbcr_base; force)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) (map_op projl projr (comp_op Some (case_sum r2 (BENQ x2 (BHD x2 l1) l2)) (transp_op (case_sum (BTL x2 l1) r1)) (transp_op (case_sum r3 l3)))) op2'"
      if "x2 \<notin> defaults"
        and "l1 x2 \<noteq> []"
      for x2 :: 'a
      using that by (intro exI conjI[rotated] wbcr_base; force)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) (map_op projl projr (comp_op Some (case_sum (BTL x1 r2) l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum (BENQ x1 (BHD x1 r2) r3) l3)))) op2'"
      if "x1 \<notin> defaults"
        and "r2 x1 \<noteq> []"
      for x1 :: 'b
      using that 
      apply -
      apply (intro exI conjI[rotated] wbcr_base)
        apply (rule refl)+
      apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) (map_op projl projr (comp_op Some (case_sum r2 (BTL x2 l2)) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 (BENQ x2 (BHD x2 l2) l3))))) op2'"
      if "x2 \<notin> defaults"
        and "l2 x2 \<noteq> []"
      for x2 :: 'a
      using that 
      apply -
      apply (intro exI conjI[rotated] wbcr_base)
        apply (rule refl)+
      apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      done
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_transp_op_cases split: if_splits sum.splits)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_transp_op_cases split: if_splits sum.splits; hypsubst_thin)
  proof -
    have "\<exists>op1'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3)))) op1' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op1' (id_op (BENQ p x (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))))"
      if "p \<notin> defaults"
      for p :: "'a + 'b"
        and x :: 'c
      using that 
    proof (cases p)
      case (Inl a)
      from this that show ?thesis by (intro exI conjI[rotated] wbcr_base; force)
    next
      case (Inr b)
      from this that show ?thesis by (intro exI conjI[rotated] wbcr_base; force)
    qed
    moreover have "\<exists>op1'. wstep (Out (Inl x1) (BHD x1 l1)) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3)))) op1' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op1' (id_op (case_sum ((BTL x1 l1 >> l2) >> l3) ((r1 >> r2) >> r3)))"
      if "x1 \<notin> defaults"
        and "l1 x1 \<noteq> []"
        and "l3 x1 = []"
        and "l2 x1 = []"
      for x1 :: 'a
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))))
     (map_op projl projr (comp_op Some (case_sum r2 (BENQ x1 (BHD x1 l1) l2)) (transp_op (case_sum (BTL x1 l1) r1)) (transp_op (case_sum r3 l3))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply force
           apply auto
        done
      also have "step Tau \<dots> (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum (BTL x1 l1) r1)) (transp_op (case_sum r3 (BENQ x1 (BHD x1 l1) l3)))))"
        using that by auto
      also have "step (Out (Inl x1) (BHD x1 l1)) \<dots> (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum (BTL x1 l1) r1)) (transp_op (case_sum r3 l3))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply auto
        done
      ultimately show ?thesis
        using that apply -
        apply (intro exI conjI[rotated] wbcr_base)
          apply (rule refl)+
        apply (meson wstep_trans(1))
        done
    qed
    moreover have "\<exists>op1'. wstep (Out (Inl x1) (BHD x1 l2)) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3)))) op1' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op1' (id_op (case_sum ((l1 >> BTL x1 l2) >> l3) ((r1 >> r2) >> r3)))"
      if "x1 \<notin> defaults"
        and "l3 x1 = []"
        and "l2 x1 \<noteq> []"
      for x1 :: 'a
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))))
     (map_op projl projr (comp_op Some (case_sum r2 (BTL x1 l2)) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 (BENQ x1 (BHD x1 l2) l3)))))"
        using that by auto
      also have "step (Out (Inl x1) (BHD x1 l2)) \<dots> (map_op projl projr (comp_op Some (case_sum r2 (BTL x1 l2)) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply auto
        done
      ultimately show ?thesis
        using that apply -
        apply (intro exI conjI[rotated] wbcr_base)
          apply (rule refl)+
        apply (meson step_tau_step_io_wstep)
        done
    qed
    moreover have "\<exists>op1'. wstep (Out (Inl x1) (BHD x1 l3)) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3)))) op1' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op1' (id_op (case_sum ((l1 >> l2) >> BTL x1 l3) ((r1 >> r2) >> r3)))"
      if "x1 \<notin> defaults"
        and "l3 x1 \<noteq> []"
      for x1 :: 'a
      using that apply -
      apply (intro exI conjI[rotated] wbcr_base)
        apply (rule refl)+
      apply force
      done
    moreover have "\<exists>op1'. wstep (Out (Inr x2) (BHD x2 r1)) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3)))) op1' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op1' (id_op (case_sum ((l1 >> l2) >> l3) ((BTL x2 r1 >> r2) >> r3)))"
      if "x2 \<notin> defaults"
        and "r1 x2 \<noteq> []"
        and "r3 x2 = []"
        and "r2 x2 = []"
      for x2 :: 'b
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))))
     (map_op projl projr (comp_op Some (case_sum (BENQ x2 (BHD x2 r1) r2) l2) (transp_op (case_sum l1 (BTL x2 r1))) (transp_op (case_sum r3 l3))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply force
           apply auto
        done
      also have "step Tau \<dots> (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 (BTL x2 r1))) (transp_op (case_sum (BENQ x2 (BHD x2 r1) r3) l3))))"
        using that by auto
      also have "step (Out (Inr x2) (BHD x2 r1)) \<dots> (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 (BTL x2 r1))) (transp_op (case_sum r3 l3))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply auto
        done
      ultimately show ?thesis
        using that apply -
        apply (intro exI conjI[rotated] wbcr_base)
          apply (rule refl)+
        apply (meson wstep_trans(1))
        done
    qed
    moreover have "\<exists>op1'. wstep (Out (Inr x2) (BHD x2 r2)) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3)))) op1' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op1' (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> BTL x2 r2) >> r3)))"
      if "x2 \<notin> defaults"
        and "r3 x2 = []"
        and "r2 x2 \<noteq> []"
      for x2 :: 'b
      using that
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))))
     (map_op projl projr (comp_op Some (case_sum (BTL x2 r2) l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum (BENQ x2 (BHD x2 r2) r3) l3))))"
        using that by auto
      also have "step (Out (Inr x2) (BHD x2 r2)) \<dots> (map_op projl projr (comp_op Some (case_sum (BTL x2 r2) l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply auto
        done
      ultimately show ?thesis
        using that apply -
        apply (intro exI conjI[rotated] wbcr_base)
          apply (rule refl)+
        apply (meson wstep_trans_base(1))
        done
    qed
    moreover have "\<exists>op1'. wstep (Out (Inr x2) (BHD x2 r3)) (map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3)))) op1' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>l1 l2 l3 r1 r2 r3. op1xx = map_op projl projr (comp_op Some (case_sum r2 l2) (transp_op (case_sum l1 r1)) (transp_op (case_sum r3 l3))) \<and> op2xx = id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> r3))) op1' (id_op (case_sum ((l1 >> l2) >> l3) ((r1 >> r2) >> BTL x2 r3)))"
      if "x2 \<notin> defaults"
        and "r3 x2 \<noteq> []"
      for x2 :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbcr_base)
        apply (rule refl)+
      apply (rule step_wstep)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Out)
         apply auto
      done        
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_transp_op_cases split: if_splits sum.splits)
  qed
qed

lemma B7:
  \<open>\<X> \<bullet> \<X> \<approx> \<I>\<close>
  using comp_op_transp_transp_id_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  unfolding scomp_op_def
  by (auto simp: o_def)


end