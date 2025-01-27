\<comment> \<open>Axioms from Table 4 for merge test and split\<close>
theory Asynchronous_Dataflow_Axioms

imports
  BNA_Operators
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom: A1: Merge commutes with identity\<close>
lemma merge_op_commutes_identity:
  "(\<V> \<parallel> \<I>) \<bullet> \<V> ~ map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>)"
  oops

section \<open>Axiom: A2: Merge transpose is merge\<close>
lemma merge_op_transp_op:
  "\<X> \<bullet> \<V> \<approx> \<V>"
  oops

section \<open>Axiom: A3: Merge dummy source and identity\<close>
lemma merge_op_dummy_source_op:
  "map_op projr id (\<exclamdown> \<parallel> \<I>) \<bullet> \<V> \<approx> \<I>"
  oops

section \<open>Axiom: A4: Merge to sink\<close>
lemma merge_op_sink_op:
   "\<V> \<bullet> ! ~ ! \<parallel> !"
  oops

section \<open>Axiom: A6: Split to transpose\<close>
lemma split_op_transp_op:
 "\<Lambda> \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<Lambda>"
  oops

section \<open>Axiom: A8: Split dummy source\<close>
lemma split_op_dummy_source:
  "\<exclamdown> \<bullet> \<Lambda> \<approx> \<exclamdown> \<parallel> \<exclamdown>"
  oops

section \<open>Axiom: A9\<close>
lemma dummy_source_op_sink_op:
  "\<exclamdown> \<bullet> ! = \<otimes>"
  oops

section \<open>Axiom A13: Parallel dummy source\<close>

lemma choices_pcomp_op_dummy_source:
  \<open>choices (\<exclamdown> \<parallel> \<exclamdown>) = {||}\<close>
  unfolding pcomp_op_def
  apply (subst comp_op_code)
  apply simp
  done

lemma dummy_source_op_pcomp_op:
  \<open>\<exclamdown> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply (rule choices_Choice_bisim)
  apply (simp add: choices_pcomp_op_dummy_source)
  done

section \<open>Axiom A15: Transpose and merge\<close>
lemma merge_op_transp_merge:
  assumes "Vmn \<equiv> \<V> :: (('m :: countable + 'n ::countable) + 'm + 'n, 'm + 'n, 'd) op"
    and "Vm \<equiv> \<V> :: ('m + 'm, 'm, 'd) op"
    and "Vn \<equiv>  \<V> :: ('n + 'n, 'n, 'd) op"
    and "Imm \<equiv> \<I> :: ('m, 'm, 'd) op"
    and "Inn \<equiv> \<I> :: ('n, 'n, 'd) op"
    and "Xnm \<equiv> \<X> :: ('n + 'm, 'm + 'n, 'd) op"
  shows "Vmn \<approx> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xnm) \<parallel> Inn) \<bullet> (Vm \<parallel> Vn)"
  oops

section \<open>Axiom A17: Parallel sink\<close>
lemma sink_op_pcomp_op:
  "! ~ ! \<parallel> !"
  oops

section \<open>Axiom A19: Split and merge\<close>
lemma split_op_transp_split:
  assumes "Smn \<equiv> \<Lambda> :: ('m + 'n,('m :: countable + 'n ::countable) + 'm + 'n,  'd) op"
    and "Sm \<equiv> \<Lambda> :: ('m, 'm + 'm, 'd) op"
    and "Sn \<equiv> \<Lambda> :: ('n, 'n + 'n, 'd) op"
    and "Imm \<equiv> \<I> :: ('m, 'm, 'd) op"
    and "Inn \<equiv> \<I> :: ('n, 'n, 'd) op"
    and "Xmn \<equiv> \<X> :: ('m + 'n, 'n + 'm, 'd) op"
  shows "Smn \<approx> (Sm \<parallel> Sn) \<bullet> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xmn) \<parallel> Inn)"
  oops

section \<open>Axiom F3: Loop merge\<close>
lemma loop_op_merge_sink:
  "map_op id Inr \<V>\<up> ~ !"
  oops

section \<open>Axiom F4: Loop split\<close>
lemma loop_op_split_dummy_source:
  "map_op Inr id \<Lambda>\<up> ~ \<exclamdown>"
  oops

end