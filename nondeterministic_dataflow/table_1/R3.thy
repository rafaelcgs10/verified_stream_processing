theory R3

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom R3: Loop parallel composition\<close>

lemma R3_gen:
  fixes op1 :: "('b + 'a, 'c + 'd, 'e) op"
    and op2 :: "('f + 'm :: defaults, 'g + 'm, 'e) op"
  assumes "Inr -` inputs op2 \<inter> defaults = {}"
    and "Inr -` outputs op2 \<inter> defaults = {}"
  shows  "comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf1) op2)) ~
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf1) (map_op BNA_Operators.assoc BNA_Operators.assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2)))"
  using assms proof (coinduction arbitrary: op1 op2 buf1 rule: bisim_coinduct_upto)
  case BISIM
  then show ?case 
    apply -
    unfolding sim_def
  proof (intro allI conjI impI)
    fix io :: "(('b + 'a) + 'f, ('c + 'd) + 'g, 'e) IO"
      and op1' :: "(('b + 'a) + 'f, ('c + 'd) + 'g, 'e) op"
    assume "Inr -` inputs op2a \<inter> defaults = {}"
      and "Inr -` outputs op2a \<inter> defaults = {}"
      and H: "step io (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (Inl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step (Inp p x) op1a op1'"
        for p :: "'b + 'a"
          and x :: 'e
          and op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that by (intro conjI[rotated, OF bc_base] exI; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'. step (Out (Inr p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''a))) op2'"
        if "step (Out (Inl p) x) op2a op''a"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for p :: 'g
          and x :: 'e
          and op''a :: "('f + 'm, 'g + 'm, 'e) op"
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'. step (Out (Inr (projl (Inr x2))) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''a))) op2'"
        if "step (Out (Inr x2) x) op2a op''a"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "x2 \<in> defaults"
        for x :: 'e
          and op''a :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply -
        apply (rule FalseE)
        apply (metis (no_types, lifting) IO.distinct(1) IO.sel(4) IO.simps(8) disjoint_iff_not_equal op.set_intros(8) outputs_after_choices step_choicesE vimageI)
        done
      moreover have "\<exists>op2'. step (Out (Inl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step (Out p x) op1a op1'"
        for p :: "'c + 'd"
          and x :: 'e
          and op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'. step (Inp (Inr (projl pa)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "pa \<notin> ran (case_sum ((\<lambda>_. None)::'g \<Rightarrow> ('f + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp pa x) op2a op''a"
        for x :: 'e
          and pa :: "'f + 'm"
          and op''a :: "('f + 'm, 'g + 'm, 'e) op"
        using that 
      proof (cases pa)
        case (Inl a)
        from this that show ?thesis 
          apply (intro conjI[rotated] exI)
           apply (rule bc_base)
          using step_inputs_outputs apply fast
          apply auto
          done
      next
        case (Inr b)
        from this that show ?thesis 
          apply (intro conjI[rotated] exI)
           apply (rule bc_base)
          using step_inputs_outputs apply fast
          apply (simp add: ran_def split: if_splits sum.splits)
          apply (metis (no_types, lifting) IO.distinct(3) IO.inject(1) IO.simps(4) Read_choices_inputs disjoint_iff_not_equal step_choicesE vimageI2)
          done
      qed
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step Tau op1a op1'"
        for op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step Tau op2a op''a"
        for op''a :: "('f + 'm, 'g + 'm, 'e) op"
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1)) op''a))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'g \<Rightarrow> ('f + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 buf1)) op2a op''a"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "buf1 x2 \<noteq> []"
        for op''a :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply (simp add: ran_def split: sum.splits if_splits)
        subgoal for p
          apply (cases p; simp)
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
               apply (auto simp add: ran_def split: if_splits sum.splits)
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 xa buf1)) op''a))) op2'"
        if "step (Out (Inr x2) xa) op2a op''a"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "x2 \<notin> defaults"
        for op''a :: "('f + 'm, 'g + 'm, 'e) op"
          and xa :: 'e
          and x2 :: 'm
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      ultimately show ?thesis
        using H BISIM by (auto 0 0 elim !: step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  next
    fix io :: "(('b + 'a) + 'f, ('c + 'd) + 'g, 'e) IO"
      and op1' :: "(('b + 'a) + 'f, ('c + 'd) + 'g, 'e) op"
    assume "Inr -` inputs op2a \<inter> defaults = {}"
      and "Inr -` outputs op2a \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op1'"
    show "\<exists>op2'. step io (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2a)))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step (Inp pa x) op1a op1'"
        for x :: 'e
          and pa :: "'b + 'a"
          and op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; fast)
      moreover have "\<exists>op2'a. step (Inp (Inr x1) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "step (Inp (Inl x1) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x1 :: 'f
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'a. step (Inp (projl (Inr x2)) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "Inr x2 \<notin> ran (case_sum ((\<lambda>_. None)::('c + 'd) + 'g \<Rightarrow> ((('b + 'a) + 'f) + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply -
        apply (rule FalseE)
        apply (simp add: ran_def split: sum.splits if_splits)
        apply (metis IO.distinct(1) IO.inject(1) IO.simps(6) Read_choices_inputs disjoint_iff_not_equal step_choicesE vimageI)
        done
      moreover have "\<exists>op2'a. step (Out (Inr x1a) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "step (Out (Inl x1a) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x1a :: 'g
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'a. step (Out (projl (Inr x2)) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "step (Out (Inr x2) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "x2 \<in> defaults"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply -
        apply (rule FalseE)
        apply (metis IO.distinct(1) IO.sel(4) IO.simps(8) disjoint_iff_not_equal op.set_intros(8) outputs_after_choices step_choicesE vimageI)
        done
      moreover have "\<exists>op2'. step (Out (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2a)))) op2'"
        if "step (Out pa x) op1a op1'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for x :: 'e
          and pa :: "'c + 'd"
          and op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'. step Tau (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2a)))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step Tau op1a op1'"
        for op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that 
        apply (intro exI conjI[rotated, OF bc_sym[OF bc_base]])
        apply force
        apply force
        done
      moreover have "\<exists>op2'a. step Tau (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step Tau op2a op2'"
        for op2' :: "('f + 'm, 'g + 'm, 'e) op"
        using that 
        apply (intro exI conjI[rotated, OF bc_sym[OF bc_base]])
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'a. step Tau (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1)) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::('c + 'd) + 'g \<Rightarrow> ((('b + 'a) + 'f) + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 buf1)) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "buf1 x2 \<noteq> []"
        for op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated, OF bc_sym[OF bc_base]])
        using step_inputs_outputs apply fast
        apply (rule step_comp_op_R_Tau)
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op[where p="Inr x2"])
               apply assumption
              apply (auto simp add: ran_def split: sum.splits if_splits dest!: Read_choices_inputs elim!: step_choicesE)
        done
      moreover have "\<exists>op2'a. step Tau (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf1)) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "step (Out (Inr x2) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "x2 \<notin> defaults"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated, OF bc_sym[OF bc_base]])
        using step_inputs_outputs apply fast
        apply (rule step_comp_op_R_Tau)
          apply (rule step_map_op)
           apply auto
        done
      ultimately show ?thesis
        using BISIM H by (auto 0 0 elim !: step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  qed
qed

lemma R3:
  fixes op1 :: "('b + 'a, 'c + 'd, 'e) op"
    and op2 :: "('f + 'm :: defaults, 'g + 'm, 'e) op"
  assumes "Inr -` inputs op2 \<inter> defaults = {}"
    and "Inr -` outputs op2 \<inter> defaults = {}"
  shows  "op1 \<parallel> (op2\<up>) ~ (map_op assoc assoc (op1 \<parallel> op2))\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using assms R3_gen[OF assms, of op1 "\<lambda> _. []"] by auto 

end