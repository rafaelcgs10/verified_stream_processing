theory A17

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A17: Parallel sink\<close>

lemma A17:
  \<open>map_op id Inl ! ~ ! \<parallel> !\<close>
  unfolding pcomp_op_def
proof (coinduction rule: bisim_coinduct)
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. step (Inp p x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) op2' \<and> bisim_R (\<lambda>op1 op2. op1 = map_op id Inl sink_op \<and> op2 = comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op) (map_op id Inl sink_op) op2'"
      if "p \<notin> defaults"
        and "io = Inp p x"
        and "op1' = map_op id Inl sink_op"
      for p :: "'a + 'b"
        and x :: 'e
    proof (cases p)
      case (Inl a)
      from this that show ?thesis
        by (intro exI conjI[rotated, OF b_base], fastforce+)
    next
      case (Inr b)
      from this that show ?thesis
        by (intro exI conjI[rotated, OF b_base], fastforce+)
    qed
    then show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_sink_op)
  qed
next
  case SIM2
  then show ?case
    by (auto elim!: step_comp_op_elim step_sink_op; intro exI conjI[rotated, OF b_base], force+)
qed

end