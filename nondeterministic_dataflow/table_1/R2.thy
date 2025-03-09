theory R2

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom R2: Loop distribute scomp_op\<close>
lemma R2_gen:
  fixes op1 :: "('b + 'm :: {defaults, countable}, 'c + 'm, 'd) op"
    and op2 :: "('c, 'a, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
  shows "map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2) \<approx>
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))"
  using assms proof (coinduction arbitrary: op1 op2 buf2 lbuf1 lbuf2 lbuf3 rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case 
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('b, 'a, 'd) IO"
      and op1' :: "('b, 'a, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and H: "step io (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2)) op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (projl pa) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> ran (case_sum ((\<lambda>_. None)::'c \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp pa x) op1 op''b"
        for x :: 'd
          and pa :: "'b + 'm"
          and op''b :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply fast
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Inp_loop_op)
          apply (auto simp add: ran_def split: sum.splits if_splits)
        done
      moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2')) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out p x) op2 op2'"
        for p :: 'a
          and x :: 'd
          and op2' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Out_loop_op)
           apply (auto simp add: ran_def split: sum.splits if_splits)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BENQ q x buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "step (Out (Inl q) x) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
        for x :: 'd
          and q :: 'c
          and op''b :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BENQ (projl (Inr x2)) x buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "step (Out (Inr x2) x) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "x2 \<in> defaults"
        for x :: 'd
          and op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that 
        apply -
        apply (rule FalseE)
        apply (metis IO.distinct(1) IO.sel(4) IO.simps(8) disjoint_iff_not_equal op.set_intros(8) outputs_after_choices step_choicesE vimageI)
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BTL p buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2')) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Inp p (BHD p buf2)) op2 op2'"
          and "buf2 p \<noteq> []"
        for p :: 'c
          and op2' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply simp_all
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op1 op''b"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply simp_all
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((BTL x2 lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'c \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 lbuf1)) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf1 x2 \<noteq> []"
          and "lbuf3 x2 = []"
          and "lbuf2 x2 = []"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that 
        using that 
      proof -
        have "step Tau (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ x2 (BHD x2 lbuf1) lbuf2))))))"
          using that apply -
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_comp_op_R_Inp)
                    apply (auto split: sum.splits dest: Read_choices_inputs elim: step_choicesE)
          done
        moreover have "step Tau 
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ x2 (BHD x2 lbuf1) lbuf2))))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (BENQ x2 (BHD x2 lbuf1) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))"
          using that apply -
          apply (rule step_Out_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Out[where p="Inr x2"])
               apply (auto split: sum.splits dest: Read_choices_inputs elim: step_choicesE)
          done
        moreover have "step Tau 
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (BENQ x2 (BHD x2 lbuf1) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op''b (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))"
          using that apply -
          apply (simp add: ran_def split: if_splits sum.splits)
          subgoal for p
            apply (cases p; simp)
            apply (rule step_Inp_Tau_loop_op)
                apply (rule step_map_op)
                 apply (auto simp add: ran_def split: sum.splits if_splits  dest: Write_choices_outputs elim: step_choicesE)
            done
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply (intro conjI)
              apply blast
             apply blast
          using step_inputs_outputs apply (metis (no_types, lifting) Int_empty_right boolean_algebra_cancel.inf1 le_iff_inf that(2) that(3) vimage_mono)
          using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra.conj_zero_right inf.commute inf_absorb2 inf_assoc that(2) that(4) vimage_mono)
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> BTL x2 lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'c \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 lbuf2)) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf3 x2 = []"
          and "lbuf2 x2 \<noteq> []"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that 
      proof -
        have 
          "step Tau (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))
            (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (BENQ x2 (BHD x2 lbuf2) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL x2 lbuf2))))))"
          using that apply -
          apply (rule step_Out_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Out[where p="Inr x2"])
               apply (auto split: sum.splits dest: Read_choices_inputs elim: step_choicesE)
          done
        moreover have  "step Tau (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (BENQ x2 (BHD x2 lbuf2) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL x2 lbuf2))))))
             (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op''b (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL x2 lbuf2))))))"
          using that apply -
          apply (simp add: ran_def split: sum.splits if_splits)
          subgoal for a
            apply (cases a; simp)
            apply (rule step_Inp_Tau_loop_op)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp[where p="Inr x2"])
                   apply (auto simp add: ran_def split: sum.splits dest: Write_choices_outputs elim: step_choicesE)
            done
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
           apply (intro conjI)
              apply blast
             apply blast
          using step_inputs_outputs apply (metis (no_types, lifting) Int_empty_right boolean_algebra_cancel.inf1 le_iff_inf that(2) that(3) vimage_mono)
          using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra.conj_zero_right inf.commute inf_absorb2 inf_assoc that(2) that(4) vimage_mono)
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> BTL x2 lbuf3)) op''b)) op2)) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'c \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 lbuf3)) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf3 x2 \<noteq> []"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that apply -
        apply (simp add: ran_def split: sum.splits if_splits)
        subgoal for p
          apply (cases p; simp)
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs that apply force
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
               apply (rule step_map_op)
                apply (auto simp add: ran_def split: sum.splits)
          done
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((BENQ x2 xa lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "step (Out (Inr x2) xa) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "x2 \<notin> defaults"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and xa :: 'd
          and x2 :: 'm
        using that 
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2')) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op2 op2'"
        for op2' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      ultimately show ?thesis
        using BISIM H by (auto 0 0 elim !: step_loop_op_elim step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  next
    fix io :: "('b, 'a, 'd) IO"
      and op1' :: "('b, 'a, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (projl (p::'b + 'm)) x) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "p \<notin> ran (case_sum ((\<lambda>_. None)::'a \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp p x) op1 op1'"
        for p :: "'b + 'm"
          and x :: 'd
          and op1' :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply fast
        apply (simp add: ran_def split: sum.splits if_splits)
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_map_op)
            apply (rule step_Inp_loop_op)
             apply (auto simp add: ran_def  split: sum.splits if_splits)
        done
      moreover have "\<exists>op2'. wstep (Out x1 x) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)))))) op2'"
        if "step (Out x1 x) op2 op1'"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
        for x :: 'd
          and op1' :: "('c, 'a, 'd) op"
          and x1 :: 'a
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (BENQ q x (case_sum buf2 lbuf1)) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out q x) op1 op1'"
        for x :: 'd
          and op1' :: "('b + 'm, 'c + 'm, 'd) op"
          and q :: "'c + 'm"
        using that 
      proof (cases q)
        case (Inl a)
        from this that show ?thesis 
          apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
           apply (intro conjI)
              apply blast
             apply auto[1]
          using step_inputs_outputs apply (metis (no_types, lifting) Int_empty_right boolean_algebra_cancel.inf1 le_iff_inf  that(3) vimage_mono)
          using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra.conj_zero_right inf.commute inf_absorb2 inf_assoc that(2) vimage_mono)
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply auto
          done
      next
        case (Inr b)
        from this that show ?thesis 
          apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
           apply (intro conjI)
              apply blast
             apply auto[1]
          using step_inputs_outputs apply (metis (no_types, lifting) Int_empty_right boolean_algebra_cancel.inf1 le_iff_inf  that(3) vimage_mono)
          using step_inputs_outputs apply (metis (no_types, lifting) boolean_algebra.conj_zero_right inf.commute inf_absorb2 inf_assoc that(2) vimage_mono)
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Out_Tau_loop_op)
                apply assumption
               apply (auto 3 3 dest: outputs_after_choices split: sum.splits elim!: step_choicesE)
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "buf2 pa \<noteq> []"
          and "step (Inp pa (BHD pa buf2)) op2 op1'"
        for pa :: 'c
          and op1' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ pa (BHD pa lbuf1) lbuf2))))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf1 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op1 op1'"
        for op1' :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply fast
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op2 op1'"
        for op1' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op2'a))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau (id_op lbuf2) op2'a"
        for op2'a :: "('m, 'm, 'd) op"
        using that apply -
        apply (rule FalseE)
        apply (meson no_step_id_op_Tau)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'a \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 lbuf3)) op1 op1'"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf3 x2 \<noteq> []"
        for op1' :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (simp add: ran_def split: if_splits sum.splits)
        subgoal for p
          apply (cases p; simp)
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Inp_Tau_loop_op[where p="Inr x2"])
                  apply (auto simp add: ran_def split: sum.splits)
          done
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 (BHD x2 lbuf2) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL x2 lbuf2))))))) op2'"
        if "lbuf2 x2 \<noteq> []"
          and "x2 \<notin> defaults"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
        done
      ultimately show ?thesis
        using H BISIM apply (auto 0 0 elim !: step_loop_op_elim step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
         apply (metis (no_types, lifting) step_id_op_Out)+
        done
    qed
  qed
qed

lemma R2:
  fixes op1 :: "('b + 'm :: {defaults, countable}, 'c + 'm, 'd) op"
    and op2 :: "('c, 'a, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
  shows  "(op1\<up>) \<bullet> op2 \<approx> (op1 \<bullet> (op2 \<parallel> \<I>))\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using R2_gen[of op1 "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []" op2, simplified, OF assms] by blast  

end