theory Collatz_Nop_Invariant

imports
  Collatz_Op
  "../../Timely/Tree_Nop_Invariant"
begin

section ‹The Optimized and Plain Compiled Collatz Programs are Equivalent›

lemma builder_tree_dt:
  "builder_tree dt"
  unfolding input_dt_def concat_dt_def collatz_dt_def branch_dt_def
    increment_dt_def
  by (auto intro: nop_leaf_ooo_input_op nop_leaf_concat_op nop_leaf_tmap_op
      nop_leaf_branch_op nop_leaf_increment_op)

lemma distinct_tree_ids_dt:
  "distinct (fst (tree_ids (0 :: 5) dt))"
  unfolding input_dt_def concat_dt_def collatz_dt_def branch_dt_def
    increment_dt_def
  by simp

theorem compiled_collatz_wbisim:
  "compiled ≈ compile_dataflow (λ _. []) dt"
  by (rule compile_dataflow_opt_wbisim_generic[OF builder_tree_dt distinct_tree_ids_dt])

theorem compiled_collatz_wtraces:
  "compiled ≡⇩t compile_dataflow (λ _. []) dt"
  by (rule wbisim_wtraces[OF compiled_collatz_wbisim])

end
