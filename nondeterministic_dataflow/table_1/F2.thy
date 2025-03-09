theory F2

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom F2: Transpose looped is identity\<close>
lemma transp_op_loop_id_gen:
  "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<approx> id_op (buf >> buf' >> buf'')"
proof (coinduction arbitrary: buf buf' buf'' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case 
    unfolding wsim_def
    sketch (intro allI conjI impI)
  proof (intro allI conjI impI)
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op1'"
    show "\<exists>op2'. wstep io (id_op (buf >> buf' >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op (buf >> buf' >> buf'')) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p' xa) (id_op ((buf >> buf') >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum (BENQ p' xa buf) buf'')))) op2'"
        if "p' \<notin> defaults"
        for p' :: 'a
          and xa :: 'b
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'. wstep (Out x1 (BHD x1 buf'')) (id_op ((buf >> buf') >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf (BTL x1 buf''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf'' x1 \<noteq> []"
        for x1 :: 'a
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf >> buf') >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf')) (transp_op (case_sum buf (BENQ x2 (BHD x2 buf') buf''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf' x2 \<noteq> []"
        for x2 :: 'a
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf >> buf') >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2a (BHD x2a buf) buf')) (transp_op (case_sum (BTL x2a buf) buf'')))) op2'"
        if "x2a \<notin> defaults"
          and "buf x2a \<noteq> []"
        for x2a :: 'a
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
        done       
      ultimately show ?thesis
        using H apply - 
        apply (elim step_transp_op_cases  step_loop_op_elim step_map_op_elim step_comp_op_elim exE conjE; clarsimp split: if_splits sum.splits)
        apply (metis (no_types, lifting) case_sum_BENQ_L sum.collapse(1) sum.collapse(2) sum_in_defaults)
        done
    qed
  next
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (id_op (buf >> buf' >> buf'')) op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op (buf >> buf' >> buf'')) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (id_op ((BENQ p x buf >> buf') >> buf'')) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM step_inputs_outputs apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply auto
        done
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf)) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (id_op ((BTL p buf >> buf') >> buf'')) op2'"
        if "buf p \<noteq> []"
          and "p \<notin> defaults"
          and "buf'' p = []"
          and "buf' p = []"
        for p :: 'a
        using that 
      proof -
        have "step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))))
     (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ p (BHD p buf) buf')) (transp_op (case_sum (BTL p buf) buf''))))"
          apply (rule step_map_op)
           apply (rule step_Out_Tau_loop_op)
          using that  apply (auto split: sum.splits)
          done
        moreover have "step Tau 
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ p (BHD p buf) buf')) (transp_op (case_sum (BTL p buf) buf''))))
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum (BTL p buf) (BENQ p (BHD p buf)  buf'')))))"
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
          using that  apply (auto split: sum.splits)
          done
        moreover have "step (Out p (BHD p buf)) 
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum (BTL p buf) (BENQ p (BHD p buf) buf'')))))
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum (BTL p buf)  buf''))))"
          apply (rule step_map_op)
           apply (rule step_Out_loop_op)
          using that  apply (auto split: sum.splits)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
          using BISIM step_inputs_outputs apply force
          using wstep_trans_tau_1 step_wstep apply meson
          done
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (id_op ((buf >> BTL p buf') >> buf'')) op2'"
        if "p \<notin> defaults"
          and "buf'' p = []"
          and "buf' p \<noteq> []"
        for p :: 'a
        using that 
      proof -
        have "step Tau 
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))))
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL p buf')) (transp_op (case_sum buf (BENQ p (BHD p buf') buf'')))))"
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
          using that  apply (auto split: sum.splits)
          done
        moreover have "step (Out p (BHD p buf')) 
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL p buf')) (transp_op (case_sum buf (BENQ p (BHD p buf') buf'')))))
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL p buf')) (transp_op (case_sum buf  buf''))))"
          apply (rule step_map_op)
           apply (rule step_Out_loop_op)
          using that  apply (auto split: sum.splits)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
          using BISIM step_inputs_outputs apply force
          using wstep_trans_tau_1 step_wstep apply meson
          done
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (id_op ((buf >> buf') >> BTL p buf'')) op2'"
        if "p \<notin> defaults"
          and "buf'' p \<noteq> []"
        for p :: 'a
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM step_inputs_outputs apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Out_loop_op)
        using that  apply (auto split: sum.splits)
        done
      ultimately show ?thesis
        using H by (auto 0 0 elim !: step_id_op_cases step_transp_op_cases  step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  qed
qed

lemma transp_op_loop_id: \<open>\<X>\<up> \<approx> \<I>\<close>
  unfolding feedback_op_def 
  using transp_op_loop_id_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by auto

end