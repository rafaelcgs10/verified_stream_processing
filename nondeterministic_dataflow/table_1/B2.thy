theory B2

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B2: Neutral element of parallel composition\<close>

lemma B2_1:
  \<open>(op \<parallel> (\<I> :: (0, 0, 'd) op)) ~ map_op Inl Inl op\<close>
  unfolding pcomp_op_def
proof (coinduction arbitrary: op rule: bisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
    explore (auto elim!: step_comp_op_elim step_id_op_cases; hypsubst_thin?)
  proof -
    have "\<exists>op2'. step (Inp (Inl p) x) (map_op Inl Inl op) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>op. op1xx = comp_op (\<lambda>_. None::0 option) (\<lambda>_. []) op \<I> \<and> op2xx = map_op Inl Inl op) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' \<I>) op2'"
      if "step (Inp p x) op op1'"
      for p :: 'a
        and x :: 'd
        and op1' :: "('a, 'b, 'd) op"
      using that 
      apply -
      apply (intro conjI[rotated] bc_base exI)
        apply force+
      done
    moreover have "\<exists>op2'. step (Out (Inl p) x) (map_op Inl Inl op) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>op. op1xx = comp_op (\<lambda>_. None::0 option) (\<lambda>_. []) op \<I> \<and> op2xx = map_op Inl Inl op) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' \<I>) op2'"
      if "step (Out p x) op op1'"
      for p :: 'b
        and x :: 'd
        and op1' :: "('a, 'b, 'd) op"
      using that 
      apply -
      apply (intro conjI[rotated] bc_base exI)
        apply force+
      done
    moreover have "\<exists>op2'. step Tau (map_op Inl Inl op) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>op. op1xx = comp_op (\<lambda>_. None::0 option) (\<lambda>_. []) op \<I> \<and> op2xx = map_op Inl Inl op) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' \<I>) op2'"
      if "step Tau op op1'"
      for op1' :: "('a, 'b, 'd) op"
      using that 
      apply -
      apply (intro conjI[rotated] bc_base exI)
        apply force+
      done
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_comp_op_elim step_id_op_cases)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases; hypsubst_thin?)
  proof -
    have "\<exists>op2'. step (map_IO Inl Inl id io') (comp_op (\<lambda>_. None::0 option) (\<lambda>_. []) op \<I>) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>op. op1xx = comp_op (\<lambda>_. None) (\<lambda>_. []) op \<I> \<and> op2xx = map_op Inl Inl op) op2' (map_op Inl Inl op'')"
      if "step io' op op''"
      for io' :: "('a, 'b, 'd) IO"
        and op'' :: "('a, 'b, 'd) op"
      using that 
      apply -
      apply (intro conjI[rotated] bc_base exI)
      apply force+
      apply (smt (verit, del_insts) IO.map(1) IO.map(3) IO.simps(16) dom_empty empty_iff id_def step_choicesE step_comp_op_L_Inp step_comp_op_L_Out step_comp_op_L_Tau)
      done
    then show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases)
  qed
qed


lemma B2_2:
  \<open>(\<I> :: (0, 0, 'd) op) \<parallel> op ~ map_op Inr Inr op\<close>
  unfolding pcomp_op_def
proof (coinduction arbitrary: op rule: bisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
    explore (auto elim!: step_comp_op_elim step_id_op_cases; hypsubst_thin?)
  proof -
    have "\<exists>op2'a. step (Out (Inr p::0 + 'b) x) (map_op Inr Inr op) op2'a \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>op. op1xx = comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> op \<and> op2xx = map_op Inr Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> op2') op2'a"
      if "step (Out p x) op op2'"
      for p :: 'b
        and x :: 'd
        and op2' :: "('a, 'b, 'd) op"
     using that 
      apply -
      apply (intro conjI[rotated] bc_base exI)
        apply force+
     done
    moreover have "\<exists>op2'a. step (Inp (Inr p::0 + 'a) x) (map_op Inr Inr op) op2'a \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>op. op1xx = comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> op \<and> op2xx = map_op Inr Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> op2') op2'a"
      if "step (Inp p x) op op2'"
      for p :: 'a
        and x :: 'd
        and op2' :: "('a, 'b, 'd) op"
     using that 
      apply -
      apply (intro conjI[rotated] bc_base exI)
        apply force+
     done
   moreover have "\<exists>op2'a. step Tau (map_op Inr Inr op) op2'a \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>op. op1xx = comp_op (\<lambda>_. None) (\<lambda>_. []) (\<I>::(0, _, 'd) op) op \<and> op2xx = map_op Inr Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> op2') op2'a"
      if "step Tau op op2'"
      for op2' :: "('a, 'b, 'd) op"
     using that 
      apply -
      apply (intro conjI[rotated] bc_base exI)
        apply force+
     done
   ultimately show ?thesis
     using SIM1 by (auto elim !: step_comp_op_elim step_id_op_cases)
 qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases; hypsubst_thin?)
  proof -
    have "\<exists>op2'. step (map_IO Inr Inr id io') (comp_op (\<lambda>_. None) (\<lambda>_. []) (\<I>::(0, _, 'd) op) op) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>op. op1xx = comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> op \<and> op2xx = map_op Inr Inr op) op2' (map_op Inr Inr op'')"
      if "step io' op op''"
      for io' :: "('a, 'b, 'd) IO"
        and op'' :: "('a, 'b, 'd) op"
      using that 
      apply -
      apply (intro conjI[rotated] bc_base exI)
      apply force+
      apply (cases io'; simp)
      subgoal
        by force
      subgoal
        by force
      subgoal
        by force
      done
    then show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases ; hypsubst_thin ?)
  qed
qed

lemma B2_1':
  \<open>map_op projl projl (op \<parallel> (\<I> :: (0, 0, 'd) op)) ~ op\<close>
  sorry

end