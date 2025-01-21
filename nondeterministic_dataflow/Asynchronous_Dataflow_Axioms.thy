section \<open>The BNA Axioms\<close>
  \<comment> \<open>The basic operators - except compositions, loop and fair merge- from the BNA book "Network Algebra for Synchronous and Asynchronous Dataflow" (https://staff.fnwi.uva.nl/c.a.middelburg/papers/P9508.pdf) \<close>
  \<comment> \<open>Here we list most of the axioms from Table 1, and Table 4\<close>
theory Asynchronous_Dataflow_Axioms

imports
  BNA_Operators
  Loop
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom: A1: Merge commutes with identity\<close>
lemma merge_op_commutes_identity:
  "(\<V> \<parallel> \<I>) \<bullet> \<V> ~ map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>)"
  oops

subsection \<open>Axiom A6\<close>
lemma
  "split_op \<bullet> (transp_op buf) \<approx> map_op id (case_sum Inr Inl) split_op"
  oops