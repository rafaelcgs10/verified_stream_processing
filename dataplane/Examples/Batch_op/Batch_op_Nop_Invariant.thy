theory Batch_op_Nop_Invariant

imports
  Batch_op
  "../../Timely/Tree_Nop_Invariant"
begin

section ‹The Optimized and Plain Compiled Batch Programs are Equivalent›

text ‹Both leaves are @{const builder_op} instances, so
@{thm [source] compile_dataflow_opt_wbisim_generic} applies.›

lemma builder_tree_G:
  "builder_tree (G f ips bt)"
  by (auto intro: nop_leaf_ooo_input_op nop_leaf_batch_op)

lemma distinct_tree_ids_G:
  "distinct (fst (tree_ids (0 :: 2) (G f ips bt)))"
  by simp

theorem compiled_batch_op_opt_wbisim:
  "compiled_batch_op_opt inps f ≈ compiled_batch_op inps f"
  by (rule compile_dataflow_opt_wbisim_generic[OF builder_tree_G distinct_tree_ids_G])

theorem compiled_batch_op_opt_wtraces:
  "compiled_batch_op_opt inps f ≡⇩t compiled_batch_op inps f"
  by (rule wbisim_wtraces[OF compiled_batch_op_opt_wbisim])

end
