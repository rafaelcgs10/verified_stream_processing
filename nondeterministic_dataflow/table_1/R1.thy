theory R1

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

(* FIXME: move me *)
lemma rtranclp_intros_1':
  "a = b \<Longrightarrow> r\<^sup>*\<^sup>* a b"
  by auto

section \<open>Axiom R1\<close>
lemma loop_op_scomp_commute_gen:
  fixes op1 :: "('a + 'm :: {countable, defaults}, 'b + 'm, 'd) op"
    and op2 :: "('c, 'a, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
  shows "map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda> _. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1))) \<approx>
   map_op projl projl (loop_op (case_sum (\<lambda> _. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))"
  using assms
proof (coinduction arbitrary: op1 op2 buf2 lbuf1 lbuf2 lbuf3 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case 
    unfolding wsim_def
  proof (intro conjI allI impI)
    fix io :: "('c, 'b, 'd) IO"
      and op1' :: "('c, 'b, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and H: "step io (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)))) op1'"
    then show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Inp p x) op2 op1'"
        for p :: 'c
          and x :: 'd
          and op1' :: "('c, 'a, 'd) op"
        using that apply (auto del: wbc_base intro!: wbc_base exI)
         apply fastforce+
        done
      moreover have "\<exists>op2'. wstep (Out p x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if  "Inr -` inputs op1 \<inter> defaults = {}"
          and  "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out (Inl p) x) op1 op''b"
        for p :: 'b
          and x :: 'd
          and op''b :: "('a + 'm, 'b + 'm, 'd) op"
      proof -
        from that have "wstep (Out p x) (map_op projl projl
       (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
         (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))))
     (map_op projl projl
       (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
         (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op''b))))"
          by (auto del: step_wstep intro!: step_wstep)
        then show ?thesis
          using step_inputs_outputs that by (smt (z3) disjoint_iff subsetD vimage_mono wbisim_cong.intros(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (projl (Inr pa)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<in> defaults"
          and "step (Out (Inr pa) x) op1 op''b"
        for x :: 'd
          and pa :: 'm
          and op''b :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        by (metis (no_types, lifting) IO.distinct(1) IO.sel(4) IO.simps(8) disjoint_iff_not_equal op.set_intros(8) outputs_after_choices step_choicesE vimageI)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BENQ q x buf2) op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out q x) op2 op1'"
        for x :: 'd
          and op1' :: "('c, 'a, 'd) op"
          and q :: 'a
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum (BENQ q x buf2) lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)) op1)))"
          by (rule step_Tau_loop_op, auto intro!: that(3))
        from this that show ?thesis
          by (auto del: exI intro!: exI conjI[rotated, OF wbc_base])
      qed
      moreover have  H1: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BTL p buf2) op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "buf2 p \<noteq> []"
          and "step (Inp (Inl p) (BHD p buf2)) op1 op''b"
        for p :: 'a
          and op''b :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum (BTL p buf2) lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op''b)))"
          apply (rule step_Tau_loop_op)
          using that apply auto
          done
        from this that show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply (intro conjI)
              apply blast
             apply blast
          using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra_cancel.inf1 inf_bot_right le_iff_inf vimage_mono)
          using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra_cancel.inf1 inf_bot_right le_iff_inf vimage_mono)
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BTL (projl (Inr pa)) buf2) op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "buf2 (projl (Inr pa)) \<noteq> []"
          and "pa \<in> defaults"
          and "step (Inp (Inr pa) (BHD (projl (Inr pa)) buf2)) op1 op''b"
        for pa :: 'm
          and op''b :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        apply -
        apply (rule FalseE)
        apply (metis IO.inject(1) IO.simps(4) IO.simps(6) Read_choices_inputs disjoint_iff step_choicesE vimageI)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op2 op1'"
        for op1' :: "('c, 'a, 'd) op"
        using that
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)) op1)))"
          using that by (auto del: step_Tau_loop_op intro!: step_Tau_loop_op)
        from this that show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op1 op''b"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
        using that
        apply (intro exI conjI[rotated, OF wbc_base])
         apply (intro conjI)
            apply blast
           apply blast
        using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra_cancel.inf1 inf_bot_right le_iff_inf vimage_mono)
        using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra_cancel.inf1 inf_bot_right le_iff_inf vimage_mono)     
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have H2: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> BTL pa lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> defaults"
          and "step (Inp (Inr pa) (BHD pa lbuf2)) op1 op''b"
          and "lbuf2 pa \<noteq> []"
          and "lbuf3 pa = []"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
          and pa :: 'm
        using that
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf2)lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL pa lbuf2))) op1)))"
          apply (rule step_Tau_loop_op)
          using that apply auto
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf2)lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL pa lbuf2))) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL pa lbuf2))) op''b)))"
          apply (rule step_Tau_loop_op)
          using that apply auto
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply (intro conjI)
              apply blast
             apply blast
          using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra.conj_zero_right boolean_algebra_cancel.inf1 inf.orderE that(1) that(4) vimage_mono)
          using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra_cancel.inf1 inf.absorb_iff2 inf_bot_right inf_left_commute that(2) that(4) vimage_mono)
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> BTL pa lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> defaults"
          and "step (Inp (Inr pa) (BHD pa lbuf3)) op1 op''b"
          and "lbuf3 pa \<noteq> []"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
          and pa :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((BTL pa lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> defaults"
          and "step (Inp (Inr pa) (BHD pa lbuf1)) op1 op''b"
          and "lbuf1 pa \<noteq> []"
          and "lbuf2 pa = []"
          and "lbuf3 pa = []"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
          and pa :: 'm
        using that 
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ pa (BHD pa lbuf1) lbuf2))) op1)))"
          apply (rule step_Inp_Tau_loop_op)
          using that apply (auto simp add: ran_def split: sum.splits)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ pa (BHD pa lbuf1) lbuf2))) op1)))
          (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf1) lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))"
          using that by (auto del: step_Tau_loop_op step_Tau_comp_op_L intro!: step_Tau_loop_op step_Tau_comp_op_L)
        moreover have "step Tau
          (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf1) lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op''b)))"
          using that by (auto del: step_Tau_loop_op intro!: step_Tau_loop_op)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs that apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((BENQ pa xa lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> defaults"
          and "step (Out (Inr pa) xa) op1 op''b"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
          and pa :: 'm
          and xa :: 'd
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Out_Tau_loop_op)
           apply auto
        done
      ultimately show ?thesis
        using H BISIM by (auto 0 0 dest!: step_loop_op elim !:  step_map_op_elim step_comp_op_elim)
    qed
  next
    fix io :: "('c, 'b, 'd) IO"
      and op1' :: "('c, 'b, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op1'"
    then show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1'a (id_op lbuf2)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Inp p x) op2 op1'a"
        for p :: 'c
          and x :: 'd
          and op1'a :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply force
        done
      moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out (Inl p) x) op1 op2'"
        for p :: 'b
          and x :: 'd
          and op2' :: "('a + 'm, 'b + 'm, 'd) op"
        using that         
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that
         apply (intro conjI)
            apply blast
           apply blast
        using step_inputs_outputs apply (smt (verit, best) disjoint_iff subsetD vimage_mono)
        using step_inputs_outputs apply (smt (verit, best) disjoint_iff subsetD vimage_mono)
        apply (force del: step_wstep intro!: step_wstep)+
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf2) lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL pa lbuf2))) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf2 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp_intros_1')
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum (BENQ pa xa buf2) lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1'a (id_op lbuf2)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out pa xa) op2 op1'a"
        for pa :: 'a
          and xa :: 'd
          and op1'a :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "step (Inp (Inl x1) (BHD x1 buf2)) op1 op2'"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "buf2 x1 \<noteq> []"
        for op2' :: "('a + 'm, 'b + 'm, 'd) op"
          and x1 :: 'a
        using that 
      proof -
        have "step Tau (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))
     (comp_op Some (BTL x1 buf2) op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op2')))"
          apply (rule step_Tau_comp_op_R)
          using that apply auto
          done
        from this that show ?thesis
          apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
           apply (intro conjI)
              apply blast
             apply blast
          using step_inputs_outputs apply (smt (verit, best) disjoint_iff subsetD vimage_mono)
          using step_inputs_outputs apply (smt (verit, best) disjoint_iff subsetD vimage_mono)
          apply auto
          done
      qed
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "step (Inp (Inr x2) (BHD x2 lbuf3)) op1 op2'"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf3 x2 \<noteq> []"
        for op2' :: "('a + 'm, 'b + 'm, 'd) op"
          and x2 :: 'm
        using that 
      proof -
        have "step Tau (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))
     (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> BTL x2 lbuf3)) op2')))"
          using that apply -
          apply (rule step_comp_op_R_Tau)
            apply (rule step_map_op)
             apply simp_all
          apply (rule step_Inp_Tau_loop_op[where p="Inr x2"])
              apply simp_all
          using that apply (smt (verit, del_insts) IO.inject(1) IO.simps(4) IO.simps(6) Int_iff Read_choices_inputs case_sum_if empty_iff ranI step_choicesE vimageI)
          done
        from this that show ?thesis
          apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
           apply (intro conjI)
              apply blast
             apply blast
          using step_inputs_outputs apply (smt (verit, best) disjoint_iff subsetD vimage_mono)
          using step_inputs_outputs apply (smt (verit, best) disjoint_iff subsetD vimage_mono)
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1'a (id_op lbuf2)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op2 op1'a"
        for op1'a :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op2') op1)))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau (id_op lbuf2) op2'"
        for op2' :: "('m, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
         apply (intro conjI)
            apply blast+
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op1 op2'"
        for op2' :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply fast
        apply fast
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL p lbuf1)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ p (BHD p lbuf1) lbuf2))) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "p \<notin> defaults"
          and "lbuf1 p \<noteq> []"
        for p :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ p x lbuf1)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "p \<notin> defaults"
          and "step (Out (Inr p) x) op1 op2'"
        for p :: 'm
          and x :: 'd
          and op2' :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply fast
        apply force
        done
      moreover have "\<exists>op2'a. wstep (Out (projl (Inr p)) x) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "p \<in> defaults"
          and "step (Out (Inr p) x) op1 op2'"
        for p :: 'm
          and x :: 'd
          and op2' :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply fast
        apply (force del: step_wstep intro!: step_wstep)
        done
      ultimately show ?thesis
        using BISIM H apply (auto 0 0 dest!: step_loop_op elim !: step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim split: sum.splits)
        apply (metis (no_types, lifting) step_id_op_Out)
        done
    qed
  qed
qed

lemma R1:
  fixes op1 :: "('a + 'm :: {countable, defaults}, 'b + 'm, 'd) op"
    and op2 :: "('c, 'a, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
  shows "op2 \<bullet> (op1\<up>) \<approx> ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def comp_def
  using assms loop_op_scomp_commute_gen[of  op1  "\<lambda>_. []" op2 "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []", unfolded comp_def, simplified] by auto 

end