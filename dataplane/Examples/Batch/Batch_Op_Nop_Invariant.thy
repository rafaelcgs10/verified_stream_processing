theory Batch_Op_Nop_Invariant

imports
  Batch_Op
  "../../Timely/Tree_Nop_Invariant"
begin

section \<open>The Optimized and Plain Compiled Batch Programs are Equivalent\<close>

text \<open>Both leaves are @{const builder_op} instances, so
@{thm [source] compile_dataflow_opt_wbisim_generic} applies.\<close>

lemma builder_tree_G_dt:
  "builder_tree (G_dt f ips bt)"
  by (auto intro: nop_leaf_ooo_input_op nop_leaf_batch_op)

lemma distinct_tree_ids_G_dt:
  "distinct (fst (tree_ids (0 :: 2) (G_dt f ips bt)))"
  by simp

theorem compiled_batch_op_opt_wbisim:
  "compile_dataflow_opt (\<lambda> _. []) (batch_tree ins f) \<approx> compiled_batch_op ins f"
  by (rule compile_dataflow_opt_wbisim_generic[OF builder_tree_G_dt distinct_tree_ids_G_dt])

theorem compiled_batch_op_opt_wtraces:
  "compile_dataflow_opt (\<lambda> _. []) (batch_tree ins f) \<equiv>\<^sub>t compiled_batch_op ins f"
  by (rule wbisim_wtraces[OF compiled_batch_op_opt_wbisim])

end
