theory R4

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom R4: Loop commutes inner sequential composition\<close>
lemma R4_gen:
  fixes op1 :: "('k :: {countable,defaults} + 'm :: {countable,defaults}, 'l :: {countable,defaults} + 'n :: {countable,defaults}, 'd) op"
    and op2 :: "('n, 'm, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
    and "inputs op2 \<inter> defaults = {}"
    and "outputs op2 \<inter> defaults = {}"
  shows "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf1)
   (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<approx>
   map_op projl projl
  (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf2'')
   (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))"
  using assms proof (coinduction arbitrary: op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4' rule: wbisim_coinduct_upto)
  case BISIM
  then show ?case 
    unfolding wsim_def
  proof (intro conjI impI allI)
    fix io :: "('k, 'l, 'd) IO"
      and op1' :: "('k, 'l, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and "inputs op2 \<inter> defaults = {}"
      and "outputs op2 \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) op1' op2'"
proof -
      have "\<exists>op2'. wstep (Inp p' x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum (BENQ p' x buf4) buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "p' \<notin> defaults"
        for x :: 'd
          and p' :: 'k
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply auto
        done
      moreover have "\<exists>op2'. wstep (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step (Out x2 x) op2 op2'a"
          and "x2 \<in> defaults"
        for x :: 'd
          and op2'a :: "('n, 'm, 'd) op"
          and x2 :: 'm
        using that 
        apply-
        apply (rule FalseE)
        using BISIM 
        apply (metis IO.distinct(1) IO.inject(2) IO.simps(8) disjoint_iff op.set_intros(8) outputs_after_choices step_choicesE)
        done
      moreover have "\<exists>op2'. wstep (Out x1 (BHD x1 buf3')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf3')) op2))))) op2'"
        if "buf3' x1 \<noteq> []"
          and "x1 \<notin> defaults"
        for x1 :: 'l
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply (rule step_wstep)
        apply (rule step_map_op[where io= "Out (Inl x1) (BHD x1 buf3')"])
         apply simp_all
        apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (BENQ q x (case_sum buf3 ((buf2 >> buf2') >> buf2''))) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a"
        if "step (Out q x) op1 op2'"
        for x :: 'd
          and q :: "'l + 'n"
          and op2' :: "('k + 'm, 'l + 'n, 'd) op"
        using that 
      proof (cases q)
        case (Inl p)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
           apply (intro conjI exI)
          apply force
               apply force
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        using BISIM apply fast
          using BISIM apply fast
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)     
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Tau)
               apply auto
          done
      next
        case (Inr r)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
  apply (intro conjI exI)
          apply force
               apply force
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
                  using BISIM apply fast
        using BISIM apply fast
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)     
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Tau)
               apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum (BTL pa buf3) ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pa (BHD pa buf3) buf3')) op2))))) op2'"
        if "buf3 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'l
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)     
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Tau)
             apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((BTL pa buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "buf2 pa \<noteq> []"
          and "step (Inp pa (BHD pa buf2)) op2 op2'a"
          and "buf2'' pa = []"
          and "buf2' pa = []"
        for pa :: 'n
          and op2'a :: "('n, 'm, 'd) op"
        using that
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' (BENQ pa (BHD pa buf2) buf2'))))))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply simp_all
          apply (rule step_comp_op_R_Tau)
            apply (rule step_map_op)
             apply simp_all
          apply (rule step_Tau_comp_op_R[where p="Inr pa"])
          using BISIM that apply (auto split: sum.splits dest: Read_choices_inputs elim!: step_choicesE)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' (BENQ pa (BHD pa buf2) buf2'))))))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ pa (BHD pa buf2) buf2''))
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' buf2')))))))"
          apply (rule step_Out_Tau_loop_op[where q="Inr pa"])
            apply (rule step_map_op[of "Out (Inr (Inr pa)) (BHD pa buf2)"])
             apply simp_all
          using BISIM that apply (auto split: sum.splits dest!: Read_choices_inputs elim: step_choicesE)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ pa (BHD pa buf2) buf2''))
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' buf2')))))))
     ((loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
         (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2'a) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' buf2'))))))))"
          apply (rule step_Inp_Tau_loop_op[where p="Inr pa"])
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim: step_choicesE)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
                apply (intro conjI)
              apply blast
        apply auto[1]
        subgoal using BISIM(1) by force 
        subgoal using BISIM(2) by force
        subgoal by (meson BISIM(3) disjoint_iff step_inputs_outputs subsetD that(2))
        subgoal by (meson BISIM(4) disjoint_iff step_inputs_outputs subsetD that(2))
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> BTL pa buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step (Inp pa (BHD pa buf2')) op2 op2'a"
          and "buf2'' pa = []"
          and "buf2' pa \<noteq> []"
        for pa :: 'n
          and op2'a :: "('n, 'm, 'd) op"
        using that 
      proof -
        have "step Tau  (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ pa (BHD pa buf2') buf2''))
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' (BTL pa buf2'))))))))"
          apply (rule step_Out_Tau_loop_op[where q="Inr pa"])
            apply (rule step_map_op[of "Out (Inr (Inr pa)) (BHD pa buf2')"])
             apply simp_all
          using BISIM that apply (auto split: sum.splits dest!: Read_choices_inputs elim: step_choicesE)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ pa (BHD pa buf2') buf2''))
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' (BTL pa buf2'))))))))
     ((loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
         (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2'a) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' (BTL pa buf2')))))))))"
          apply (rule step_Inp_Tau_loop_op[where p="Inr pa"])
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim: step_choicesE)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
                          apply (intro conjI)
              apply blast
        apply auto[1]
        subgoal using BISIM(1) by force 
        subgoal using BISIM(2) by force
        subgoal by (meson BISIM disjoint_iff step_inputs_outputs subsetD that)
        subgoal by (meson BISIM disjoint_iff step_inputs_outputs subsetD that)
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> BTL pa buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step (Inp pa (BHD pa buf2'')) op2 op2'a"
          and "buf2'' pa \<noteq> []"
        for pa :: 'n
          and op2'a :: "('n, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
  apply (intro conjI exI)
          apply force
             apply force
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM apply safe
          done
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM apply safe
          done
        using that BISIM step_inputs_outputs apply fast
        using that BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Inp_Tau_loop_op[where p="Inr pa"])
        using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim: step_choicesE)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf4) buf4') buf1'') (id_op (case_sum (BTL x1 buf4) buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "x1 \<notin> defaults"
          and "buf4 x1 \<noteq> []"
        for x1 :: 'k
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1') buf1'')) (id_op (case_sum buf4 (BTL x2 buf1'))) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "x2 \<notin> defaults"
          and "buf1' x2 \<noteq> []"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf4') buf1'') (id_op (case_sum buf4 buf1')) op2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a"
        if "step (Inp (Inl x1) (BHD x1 buf4')) op1 op2'"
          and "buf4' x1 \<noteq> []"
        for op2' :: "('k + 'm, 'l + 'n, 'd) op"
          and x1 :: 'k
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
  apply (intro conjI exI)
          apply force
               apply force
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        using BISIM apply auto[1]
        using BISIM apply auto[1]
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BTL x2 buf1'')) (id_op (case_sum buf4 buf1')) op2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a"
        if "step (Inp (Inr x2) (BHD x2 buf1'')) op1 op2'"
          and "buf1'' x2 \<noteq> []"
        for op2' :: "('k + 'm, 'l + 'n, 'd) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
   apply (intro conjI exI)
          apply force
               apply force
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        using BISIM apply auto[1]
        using BISIM apply auto[1]
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') op1'a op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "step Tau (id_op (case_sum buf4 buf1')) op1'a"
        for op1'a :: "('k + 'm, 'k + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply blast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a"
        if "step Tau op1 op2'"
        for op2' :: "('k + 'm, 'l + 'n, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
      apply (intro conjI exI)
          apply force
               apply force
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        using BISIM apply auto[1]
        using BISIM apply auto[1]
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)     
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Tau)
             apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2))))) op2'"
        if "step Tau (id_op buf3') op1'"
        for op1' :: "('l, 'l, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply blast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)     
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Tau)
             apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step Tau op2 op2'a"
        for op2'a :: "('n, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)     
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1)) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 (BENQ x2 (BHD x2 buf1) buf1'))) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'l \<Rightarrow> ('k + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "x2 \<notin> defaults"
          and "buf1 x2 \<noteq> []"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply auto 
        done
      moreover have  H2: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf1)) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step (Out x2 x) op2 op2'a"
          and "x2 \<notin> defaults"
        for x :: 'd
          and op2'a :: "('n, 'm, 'd) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply simp_all
        apply (rule step_Tau_loop_op)     
         apply (rule step_map_op)
          apply auto
        done
      ultimately show ?thesis
        apply -
        subgoal premises prems
          using H apply -
          apply (elim step_loop_op_elim step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin?)
          subgoal for io' op'' p x op''a io'a op''b pa op1'a io'b op''c pb op1'aa
            apply (cases p)
            apply simp_all
            using prems(1) apply force
            done
          subgoal using prems by blast
          subgoal using prems by (smt (verit, ccfv_SIG) step_id_op_Out)
          subgoal using prems by blast
          subgoal using prems by blast
          subgoal using prems by blast
          subgoal using prems by blast
          subgoal using prems by (smt (verit, ccfv_SIG) step_id_op_Out)
          subgoal using prems 
            by (smt (z3) Inl_in_defaults Inr_in_defaults case_sum_BENQ_L case_sum_BENQ_R case_sum_BHD_L case_sum_BHD_R case_sum_BTL_L case_sum_BTL_R step_id_op_Out sum.case_eq_if sum.collapse(1) sum.collapse(2))
           subgoal using prems by force
          subgoal using prems by force
          subgoal using prems by force
          subgoal using prems by force
          subgoal using prems by force
          subgoal using prems by force
          subgoal using prems by force
          subgoal using prems by force
          done
        done
    qed
  next
    fix io :: "('k, 'l, 'd) IO"
      and op1' :: "('k, 'l, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and "inputs op2 \<inter> defaults = {}"
      and "outputs op2 \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) op1' op2'"
    proof -
      have False
        if "step (Inp pb x) op2 op2'"
          and "pb \<in> defaults"
        for x :: 'd
          and pb :: 'n
          and op2' :: "('n, 'm, 'd) op"
        using that BISIM by (metis IO.distinct(1) IO.distinct(3) IO.inject(1) IntI Read_choices_inputs emptyE step_choicesE)
      moreover have "\<exists>op2'. wstep (Inp p' x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p' x buf4)) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'"
        if "p' \<notin> defaults"
        for x :: 'd
          and p' :: 'k
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using BISIM apply blast
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Inp_loop_op)     
          apply (rule step_map_op)
           apply auto
        done
      moreover have "\<exists>op2'. wstep (Out x1 (BHD x1 buf3')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum (BTL x1 buf3') buf2')))))))) op2'"
        if "buf3' x1 \<noteq> []"
          and "x1 \<notin> defaults"
        for x1 :: 'l
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using BISIM apply blast
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Out_loop_op)     
           apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((BENQ pa x buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2') (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a"
        if "step (Out pa x) op2 op2'"
        for x :: 'd
          and pa :: 'm
          and op2' :: "('n, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Out_Tau_loop_op[where p="Inr pa"])
        using BISIM(4) apply (auto dest: outputs_after_choices elim!: step_choicesE)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf4) buf4') ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pa buf4)) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'"
        if "buf4 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'k
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using BISIM step_inputs_outputs apply blast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_L)
                 apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum (BTL x1 buf4') ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Inp (Inl x1) (BHD x1 buf4')) op1 op1'"
          and "buf4' x1 \<noteq> []"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and x1 :: 'k
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply (intro exI conjI)
              apply (rule refl)+
        using BISIM step_inputs_outputs apply (metis Int_empty_right boolean_algebra_cancel.inf1 inf.orderE vimage_mono)
        using BISIM step_inputs_outputs apply (metis Int_empty_right boolean_algebra_cancel.inf1 inf.orderE vimage_mono)
        using BISIM step_inputs_outputs apply force
        using BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((BTL x2 buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Inp (Inr x2) (BHD x2 buf1)) op1 op1'"
          and "buf1 x2 \<noteq> []"
          and "buf1'' x2 = []"
          and "buf1' x2 = []"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and x2 :: 'm
        using that 
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 (BENQ x2 (BHD x2 buf1) buf1'))) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Inp_Tau_loop_op[where p="Inr x2" and x="BHD x2 buf1"])
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Inp[where p="Inr x2" ])
                 apply (rule step_map_op)
                  apply (rule step_comp_op_L_Inp)
                    apply auto[1]
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 (BENQ x2 (BHD x2 buf1) buf1'))) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
      (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1) buf1'')) (id_op (case_sum buf4 buf1')) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        moreover have "step Tau
      (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1) buf1'')) (id_op (case_sum buf4 buf1')) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
      (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4'  buf1'') (id_op (case_sum buf4 buf1')) op1'))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_R)
          using BISIM that apply blast
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (intro exI conjI)
                apply (rule refl)+
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> BTL x2 buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Inp (Inr x2) (BHD x2 buf1')) op1 op1'"
          and "buf1'' x2 = []"
          and "buf1' x2 \<noteq> []"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and x2 :: 'm
        using that 
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1') buf1'')) (id_op (case_sum buf4 (BTL x2 buf1'))) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        moreover have "step Tau
(loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1') buf1'')) (id_op (case_sum buf4 (BTL x2 buf1'))) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 (BTL x2 buf1'))) op1'))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_R)
          using BISIM that apply blast
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (intro exI conjI)
                apply (rule refl)+
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> BTL x2 buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Inp (Inr x2) (BHD x2 buf1'')) op1 op1'"
          and "buf1'' x2 \<noteq> []"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply (intro exI conjI)
              apply (rule refl)+
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_R)
        using BISIM that apply blast
        using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1'a op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step Tau (id_op buf4) op1'a"
        for op1'a :: "('k, 'k, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2') (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a"
        if "step Tau op2 op2'"
        for op2' :: "('n, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (BENQ q xa (case_sum buf3 buf2)) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Out q xa) op1 op1'"
        for xa :: 'd
          and op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and q :: "'l + 'n"
        using that 
      proof (cases q)
        case (Inl a)
        from this that show ?thesis 
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (intro exI conjI)
                apply (rule refl)+
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply blast
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply auto
          done
      next
        case (Inr b)
        from this that  show ?thesis 
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (intro exI conjI)
                apply (rule refl)+
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply blast
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_L)
                apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf3) buf2) op1 (id_op (case_sum (BENQ x1 (BHD x1 buf3) buf3') buf2')))))))) op2'"
        if "x1 \<notin> defaults"
          and "buf3 x1 \<noteq> []"
        for x1 :: 'l
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply blast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL x2 buf2)) op1 (id_op (case_sum buf3' (BENQ x2 (BHD x2 buf2) buf2'))))))))) op2'"
        if "x2 \<notin> defaults"
          and "buf2 x2 \<noteq> []"
        for x2 :: 'n
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply blast
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step Tau op1 op1'"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply (intro exI conjI)
              apply (rule refl)+
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 op2'a)))))) op2'"
        if "step Tau (id_op (case_sum buf3' buf2')) op2'a"
        for op2'a :: "('l + 'n, 'l + 'n, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply blast
        apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2') (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'l \<Rightarrow> ('k + 'n) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp x2 (BHD x2 buf2'')) op2 op2'"
          and "buf2'' x2 \<noteq> []"
        for op2' :: "('n, 'm, 'd) op"
          and x2 :: 'n
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R[where p="Inr x2"])
                apply simp_all
        apply (rule step_comp_op_R_Inp)
           apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 (BHD x2 buf2') buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' (BTL x2 buf2'))))))))) op2'"
        if "buf2' x2 \<noteq> []"
          and "x2 \<notin> defaults"
        for x2 :: 'n
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply blast
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      ultimately show ?thesis
        apply -
        subgoal premises prems
          using H apply (elim  step_loop_op_elim step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim exE conjE disjE; clarsimp split: if_splits sum.splits; hypsubst_thin?)
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems 
            by (smt (verit, best) Inl_in_defaults case_sum_BHD_L case_sum_BTL_L old.sum.simps(5) step_id_op_Out)
          subgoal using prems 
            by (meson Inr_in_defaults step_id_op_Out) 
          subgoal using prems by meson
          subgoal using prems  
            by (smt (verit, best) step_id_op_Out) 
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by fastforce
          subgoal using prems  
            by (smt (verit) in_feedback_wire) 
          subgoal using prems 
            by (smt (verit, ccfv_SIG) case_sum_BHD_R case_sum_BTL_R old.sum.simps(6) step_id_op_Out) 
          done
        done
    qed
  qed
qed

lemma R4:
  fixes op1 :: "('k :: {countable,defaults} + 'm :: {countable,defaults}, 'l :: {countable,defaults} + 'n :: {countable,defaults}, 'd) op"
    and op2 :: "('n, 'm, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
    and "inputs op2 \<inter> defaults = {}"
    and "outputs op2 \<inter> defaults = {}"
  shows  "(\<stileturn>op1 \<bullet> (\<I> \<parallel> op2))\<up> \<approx> ((\<I> \<parallel> op2) \<bullet> op1\<turnstile>)\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using R4_gen[OF assms, of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" ] by force 

end