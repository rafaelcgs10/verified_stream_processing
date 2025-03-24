theory T3A17

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A17: Parallel sink\<close>

lemma A17:
  \<open>! ~ ! \<parallel> !\<close>
  unfolding pcomp_op_def
proof (coinduction rule: bisim_coinduct)
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. step io (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) op2' \<and> bisim_R (\<lambda>op1xx op2xx. op1xx = ! \<and> (op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)) op1' op2'"
      if "io = Inp p x"
        and "p \<notin> defaults"
        and "op1' = !"
      for p :: "'a + 'b"
        and x :: 'e
      using that 
    proof (cases p)
      case (Inl a)
      from this that show ?thesis 
        by (intro exI conjI[rotated, OF b_base], force, force)
    next
      case (Inr b)
      from this that show ?thesis 
        by (intro exI conjI[rotated, OF b_base], force, force)
    qed
    then show ?thesis
      using SIM1  by (elim step_sink_op)
  qed
next
  case SIM2
  then show ?case 
  proof -
    have "\<exists>op2'. step (Inp (Inl pa) x) sink_op op2' \<and> bisim_R (\<lambda>op1xx op2xx. op1xx = sink_op \<and> op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) op2' (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      if "(pa::'a) \<notin> defaults"
        and "step (Inp (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
        and "step (Inp (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      for p :: 'a
        and x :: 'e
        and op1' :: "('a, 'c, 'e) op"
        and pa :: 'a
      using that
      by (intro exI conjI[rotated, OF b_base], force, force)
    moreover have "\<exists>op2'. step (Inp (Inr pa) x) sink_op op2' \<and> bisim_R (\<lambda>op1xx op2xx. op1xx = sink_op \<and> op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) op2' (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      if "pa \<notin> defaults"
        and "step (Inp (Inr pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
        and "step (Inp (Inr pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      for p :: 'b
        and x :: 'e
        and op2' :: "('b, 'd, 'e) op"
        and pa :: 'b
      using that    
      by (intro exI conjI[rotated, OF b_base], force, force)
    ultimately show ?thesis
      using SIM2 by (elim step_comp_op_elim step_sink_op ; simp split: sum.splits ; hypsubst_thin ?)
  qed
qed

end