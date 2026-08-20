theory Label_Propagation_Nop_Invariant

imports
  Label_Propagation_Op_Correctness_Extras
  "../../Timely/Tree_Nop_Invariant"
begin

section ‹The Optimized and Plain Compiled Label Propagation Programs are Equivalent›

lemma builder_tree_G:
  "builder_tree (G inp_state label_state incr_state)"
  by (auto intro: nop_leaf_ooo_input_op nop_leaf_label_propagation_op
      nop_leaf_increment_op)

lemma distinct_tree_ids_G:
  "distinct (fst (tree_ids (0 :: 3) (G inp_state label_state incr_state)))"
  by simp

theorem compiled_label_propagation_wbisim:
  "compiled inp ≈ compile_dataflow (λ _. [])
     (G (initial_state_input inp) initial_state_label_prop
        (initial_state_increment (MyPair 0 1)))"
  by (rule compile_dataflow_opt_wbisim_generic[OF builder_tree_G distinct_tree_ids_G])

theorem compiled_label_propagation_wtraces:
  "compiled inp ≡⇩t compile_dataflow (λ _. [])
     (G (initial_state_input inp) initial_state_label_prop
        (initial_state_increment (MyPair 0 1)))"
  by (rule wbisim_wtraces[OF compiled_label_propagation_wbisim])

end
