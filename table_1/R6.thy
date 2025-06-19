theory R6

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom R6: Loop absorb\<close>
lemma loop_op_absorb_gen:
  fixes op :: "(('a + 'l) + 'k, ('b + 'l :: defaults) + 'k :: defaults, 'c) op"
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
    and "Inr -` Inl -`  inputs op \<inter> defaults = {}"
    and "Inr -` Inl -`  outputs op \<inter> defaults = {}"
  shows "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf1) op))) ~
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))"
  using assms proof (coinduction arbitrary: op buf1 buf2 rule: bisim_coinduct_upto)
  case BISIM
  then show ?case 
    apply -
    unfolding sim_def
  proof (intro allI impI conjI)
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume "Inr -` inputs op \<inter> defaults = {}"
      and "Inr -` outputs op \<inter> defaults = {}"
      and "Inr -` Inl -` inputs op \<inter> defaults = {}"
      and "Inr -` Inl -` outputs op \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (projl (projl pa)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "projl pa \<notin> ran (case_sum ((\<lambda>_. None)::'b \<Rightarrow> ('a + 'l) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "pa \<notin> ran (case_sum ((\<lambda>_. None)::'b + 'l \<Rightarrow> (('a + 'l) + 'k) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp pa x) op op''c"
        for x :: 'c
          and pa :: "('a + 'l) + 'k"
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
        using that 
      proof (cases pa)
        case (Inl a)
        from this that show ?thesis 
          apply simp
          apply (intro exI conjI[rotated,OF bc_base])
           apply (intro conjI)
                apply blast
               apply auto[1]
          using step_inputs_outputs apply (metis (no_types, lifting) BISIM(1) boolean_algebra_cancel.inf1 inf.absorb2 inf.commute inf_bot_right vimage_mono)
          subgoal by (meson BISIM(2) disjoint_iff step_inputs_outputs subsetD vimage_mono)
          subgoal by (smt (verit) BISIM(3) disjoint_iff step_inputs_outputs subset_eq vimageE vimageI) 
          subgoal
            apply (drule step_inputs_outputs)
            using BISIM  apply safe
            apply (rule FalseE)
            unfolding vimage_def
            apply auto
            done
          apply (rule step_map_op)
           apply (rule step_Inp_loop_op)
            apply (rule step_map_op)
             apply assumption
          using BISIM apply (auto 4 4 simp add: ran_def split:  if_splits sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
      next
        case (Inr b)
        from this that show ?thesis 
          using BISIM by (auto simp add: ran_def split: if_splits sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
      qed
      moreover have "\<exists>op2'. step (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "step (Out (Inl (Inl x1)) x) op op''c"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x1 :: 'b
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal by (smt (verit, ccfv_SIG) BISIM(1) disjoint_iff mem_Collect_eq step_inputs_outputs subset_eq vimage_def)
        subgoal by (metis BISIM(2) Int_empty_right boolean_algebra_cancel.inf1 inf.absorb1 step_inputs_outputs vimage_mono)
        subgoal by (metis BISIM(3) Int_empty_right boolean_algebra_cancel.inf1 inf.absorb1 step_inputs_outputs vimage_mono)
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        apply auto
        done
      moreover have "\<exists>op2'. step (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "projl (Inr x2) = (Inl x1::'b + 'l)"
          and "step (Out (Inr x2) x) op op''c"
          and "x2 \<in> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x1 :: 'b
          and x2 :: 'k
        using that BISIM
        apply -
        apply (rule FalseE)
        apply (subgoal_tac "Inr x2 \<in> outputs op")
         apply auto[1]
        apply (metis IO.distinct(1) IO.distinct(5) IO.inject(2) op.set_intros(8) outputs_after_choices step_choicesE)
        done
      moreover have "\<exists>op2'. step (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "step (Out (Inl (Inr x2)) x) op op''c"
          and "x2 \<in> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
        using that BISIM
        apply -
        apply (rule FalseE)
        apply (subgoal_tac "Inl (Inr x2) \<in> outputs op")
         apply auto[1]
        apply (metis IO.distinct(1) IO.distinct(5) IO.inject(2) op.set_intros(8) outputs_after_choices step_choicesE)
        done
      moreover have "\<exists>op2'. step (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "projl (Inr x2a) = (Inr x2::'b + 'l)"
          and "step (Out (Inr x2a) x) op op''c"
          and "x2 \<in> defaults"
          and "x2a \<in> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
          and x2a :: 'k
        using that BISIM
        apply -
        apply (rule FalseE)
        apply (subgoal_tac "Inl (Inr x2) \<in> outputs op")
         apply auto[1]
        apply (metis IO.sel(4) IO.simps(4) IO.simps(8) disjoint_iff op.set_intros(8) outputs_after_choices step_choicesE vimageI)
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "step Tau op op''c"
        for op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal by (smt (verit, ccfv_SIG) BISIM(1) disjoint_iff mem_Collect_eq step_inputs_outputs subset_eq vimage_def)
        subgoal by (metis BISIM(2) Int_empty_right boolean_algebra_cancel.inf1 inf.absorb1 step_inputs_outputs vimage_mono)
        subgoal by (metis BISIM(3) Int_empty_right boolean_algebra_cancel.inf1 inf.absorb1 step_inputs_outputs vimage_mono)
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1)) op''c)))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'b + 'l \<Rightarrow> (('a + 'l) + 'k) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 buf1)) op op''c"
          and "buf1 x2 \<noteq> []"
        for op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'k
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal by (smt (verit, ccfv_SIG) BISIM(1) disjoint_iff mem_Collect_eq step_inputs_outputs subset_eq vimage_def)
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
        subgoal
          apply (drule step_inputs_outputs)
          using BISIM  apply safe
          apply (rule FalseE)
          unfolding vimage_def
          apply auto
          done
        apply (rule step_map_op)
         apply (rule step_Inp_Tau_loop_op)
             apply (rule step_map_op)
              apply assumption
        using BISIM apply (auto 4 4 simp add: ran_def split:  if_splits sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf1)) op''c)))) op2'"
        if "step (Out (Inr x2) x) op op''c"
          and "x2 \<notin> defaults"
        for op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x :: 'c
          and x2 :: 'k
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply (rule step_map_op)
         apply (rule step_Out_Tau_loop_op)
           apply (rule step_map_op)
            apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf2)) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'b \<Rightarrow> ('a + 'l) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "projl pa = Inr x2"
          and "pa \<notin> ran (case_sum ((\<lambda>_. None)::'b + 'l \<Rightarrow> (('a + 'l) + 'k) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp pa (BHD x2 buf2)) op op''c"
          and "buf2 x2 \<noteq> []"
        for pa :: "('a + 'l) + 'k"
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply (cases pa)
         apply simp_all
        subgoal for lp
          apply (cases lp)
           apply simp_all
          apply hypsubst_thin
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op[where p="Inr (Inl x2)"])
               apply (rule step_map_op)
                apply assumption
               apply simp_all
          done
        subgoal for rp
          apply (rule FalseE)
          using  BISIM apply (smt (verit, best) IO.distinct(1) IO.inject(1) IO.simps(6) Read_choices_inputs disjoint_iff mem_Collect_eq step_choicesE vimage_def)
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf2)) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "step (Out (Inl (Inr x2)) x) op op''c"
          and "x2 \<notin> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf2)) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "projl (Inr x2a) = (Inr x2::'b + 'l)"
          and "step (Out (Inr x2a) x) op op''c"
          and "x2 \<notin> defaults"
          and "x2a \<in> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
          and x2a :: 'k
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply (rule step_map_op)
         apply (rule step_Out_Tau_loop_op[where p="Inr (Inr x2a)" and x=x and q="Inr (Inr x2a)"])
           apply simp_all
        using BISIM apply (metis IO.sel(4) IO.simps(4) IO.simps(8) disjoint_iff op.set_intros(8) outputs_after_choices step_choicesE vimageI)+
        done      
      ultimately show ?thesis
        using H by (auto 0 0 elim !:  step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  next
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume "Inr -` inputs op \<inter> defaults = {}"
      and "Inr -` outputs op \<inter> defaults = {}"
      and "Inr -` Inl -` inputs op \<inter> defaults = {}"
      and "Inr -` Inl -` outputs op \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (projl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "\<forall>p'. p = Inr p' \<longrightarrow> p' \<in> defaults"
          and "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Inp p x"
        for p :: "'a + 'l + 'k"
          and x :: 'c
          and io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
        using that 
      proof (cases p)
        case (Inl a)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
           apply (intro conjI)
                apply blast
               apply auto[1]
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          apply (cases io'a; simp)
          apply hypsubst_thin
          subgoal for p
            apply (cases p; simp)
            apply (rule step_map_op[of "Inp _ x"])
             apply simp_all
             apply (rule step_Inp_loop_op)
              apply simp_all
              apply (rule step_map_op[of "Inp _ x"])
               apply (rule step_Inp_loop_op)
                apply assumption
               apply (auto split: sum.splits)
            done
          done
      next
        case (Inr b)
        from this that show ?thesis 
          using BISIM by (smt (verit, ccfv_threshold) IO.inject(1) IO.simps(15) IO.simps(16) IO.simps(17) IO.simps(4) IO.simps(6) Inl_in_defaults Inr_in_defaults Read_choices_inputs disjoint_iff reassoc.elims step_choicesE sum.simps(4) vimageI)
      qed
      moreover have "\<exists>op2'. step (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Out (Inl x1) x"
        for x :: 'c
          and io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x1 :: 'b
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply (cases io'a; simp)
        subgoal for p
          apply (cases p; simp split: sum.splits)
          apply (rule step_map_op)
           apply (rule step_Out_loop_op)
             apply auto
          done
        done
      moreover have "\<exists>op2'. step (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Out (Inr x2) x"
          and "x2 \<in> defaults"
        for x :: 'c
          and io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: "'l + 'k"
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply (cases io'a; simp)
        apply hypsubst_thin
        subgoal for p
          apply (cases p; simp split: sum.splits)
          subgoal for _ p
            apply (rule FalseE)
            apply hypsubst_thin
            using BISIM apply -
            apply (subgoal_tac "Inl (Inr p) \<in> outputs op")
             apply auto[1]
            apply (metis IO.distinct(1) IO.distinct(5) IO.inject(2) op.set_intros(8) outputs_after_choices step_choicesE)
            done
          subgoal for p
            apply (rule FalseE)
            apply hypsubst_thin
            using BISIM apply -
            apply (subgoal_tac "Inr p \<in> outputs op")
             apply auto[1]
            apply (metis IO.distinct(1) IO.distinct(5) IO.inject(2) op.set_intros(8) outputs_after_choices step_choicesE)
            done
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "step Tau op op''b"
        for op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum (BTL x1 buf2) buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Inp (Inr (Inl x1)) (BHD x1 buf2)"
          and "x1 \<notin> defaults"
          and "buf2 x1 \<noteq> []"
        for io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x1 :: 'l
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply (cases io'a; simp)
        subgoal for p
          apply (cases p; simp split: sum.splits)
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
               apply auto
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 (BTL x2a buf1))) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Inp (Inr (Inr x2a)) (BHD x2a buf1)"
          and "x2a \<notin> defaults"
          and "buf1 x2a \<noteq> []"
        for io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2a :: 'k
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
         apply (intro conjI)
              apply blast
             apply auto[1]
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
        apply (cases io'a; simp)
        subgoal for p
          apply (cases p; simp split: sum.splits)
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply auto
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x (case_sum buf2 buf1))) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Out (Inr x2) x"
          and "x2 \<notin> defaults"
        for x :: 'c
          and io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: "'l + 'k"
        using that 
      proof (cases x2)
        case (Inl a)
        from this that show ?thesis 
          apply -
          apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
           apply (intro conjI)
                apply blast
               apply auto[1]
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          apply (cases io'a; simp)
          subgoal for p
            apply (cases p; simp split: sum.splits)
            apply (rule step_map_op)
             apply (rule step_Out_Tau_loop_op)
               apply auto
            done
          done
      next
        case (Inr b)
        from this that show ?thesis 
          apply -
          apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
           apply (intro conjI)
                apply blast
               apply auto[1]
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          subgoal apply (drule step_inputs_outputs) using BISIM apply safe apply (rule FalseE) unfolding vimage_def apply auto done
          apply (cases io'a; simp)
          apply (cases io'a; simp)
          subgoal for p
            apply (cases p; simp split: sum.splits; hypsubst_thin?)
            apply (rule step_map_op)
             apply (rule step_Tau_loop_op)
              apply auto
            done
          done
      qed
      ultimately show ?thesis
        using H by (auto 0 0 elim !:  step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  qed
qed

lemma R6:
  fixes op :: "(('a + 'l) + 'k, ('b + 'l :: defaults) + 'k :: defaults, 'c) op"
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
    and "Inr -` Inl -`  inputs op \<inter> defaults = {}"
    and "Inr -` Inl -`  outputs op \<inter> defaults = {}"
  shows  "(op\<up>)\<up> ~ (map_op reassoc reassoc op)\<up>"
  unfolding feedback_op_def
  using loop_op_absorb_gen[OF assms, of "\<lambda> _. []" "\<lambda> _. []"] by auto

end