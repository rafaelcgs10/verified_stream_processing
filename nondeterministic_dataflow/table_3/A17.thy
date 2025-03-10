theory A17

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A17: Parallel sink\<close>

lemma A17:
  \<open>map_op Inr Inr ! ~ ! \<parallel> (! :: ('a :: {countable, defaults}, 0, 'b) op)\<close>
  unfolding pcomp_op_def
proof (coinduction rule: bisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
    explore (auto elim!: step_map_op_elim step_sink_op; hypsubst_thin)
  proof -
    have "\<exists>op2'. step (Inp (Inr p) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('c, 'd, 'b) op) (!::('a, 0, 'b) op)) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. op1xx = map_op Inr Inr ! \<and> op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) ! !) (map_op Inr Inr !) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'b
      using that 
      apply -
      apply (intro exI conjI[rotated] bc_base)
        apply blast+
      apply (simp add: step_comp_op_R_Inp step_sink_op_Read)
      done
    then show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_sink_op ; hypsubst_thin)
  qed
next
  case SIM2
  then show ?case 
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_sink_op split: sum.splits if_splits; hypsubst_thin?)

    thm step_map_op_elim
  qed
  proof -
    have "\<exists>op2'. step (Inp (Inl pa) x) sink_op op2' \<and> bisim_cong (\<lambda>op1xx op2xx. op1xx = sink_op \<and> op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) op2' (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      if "(pa::'a) \<notin> defaults"
        and "step (Inp (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
        and "step (Inp (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, _) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      for p :: 'a
        and x :: 'e
        and op1' :: "('a, 'c, 'e) op"
        and pa :: 'a
      using that
      by (intro exI conjI[rotated, OF bc_base], force, force)
    moreover have "\<exists>op2'. step (Inp (Inr pa) x) sink_op op2' \<and> bisim_cong (\<lambda>op1xx op2xx. op1xx = sink_op \<and> op2xx = comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) op2' (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      if "pa \<notin> defaults"
        and "step (Inp (Inr pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
        and "step (Inp (Inr pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) (sink_op::('a, 'c, 'e) op) (sink_op::('b, 'd, 'e) op)) (comp_op (\<lambda>_. None) (\<lambda>_. []) sink_op sink_op)"
      for p :: 'b
        and x :: 'e
        and op2' :: "('b, 'd, 'e) op"
        and pa :: 'b
      using that    
      by (intro exI conjI[rotated, OF bc_base], force, force)
    ultimately show ?thesis
      using SIM2 by (elim step_comp_op_elim step_sink_op ; simp split: sum.splits ; hypsubst_thin ?)
  qed
qed

end