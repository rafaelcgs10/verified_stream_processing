theory Batch_op_Nop_Invariant

imports
  Batch_op
  "../../Timely/Tree_Nop_Invariant"
begin

section ‹The Optimized and Plain Compiled Batch Programs are Equivalent›

text ‹The batch dataflow is a @{const builder_tree}: both of its leaves are
@{const builder_op} instances whose logics never touch the @{const front}
and @{const initia} fields. Hence the generic theorem
@{thm [source] compile_dataflow_opt_wbisim_generic} applies and the
optimized and plain compilations are weakly bisimilar, so they have the
same weak traces.›

lemma logic_frontier_stable_ooo_input_op_logic:
  "logic_frontier_stable (ooo_input_op_logic ops)"
  unfolding logic_frontier_stable_def
proof (intro allI impI)
  fix os os'
  assume "os' |∈| ooo_input_op_logic ops os"
  then obtain p where "os' = (case es os p of
      LNil ⇒ drop_caps os (map (λ t. Cap t p) (ocaps os p))
    | LCons (Data t d) lxs ⇒ produces (os⦇es := (es os)(p := lxs)⦈) [(en1 os d, Cap t p)]
    | LCons (Drop t) lxs ⇒ drop_caps (os⦇es := (es os)(p := lxs)⦈) [Cap t p]
    | LCons (Mint t) lxs ⇒ add_caps (os⦇es := (es os)(p := lxs)⦈) [Cap t p])"
    unfolding ooo_input_op_logic_def by (auto simp flip: cin.rep_eq)
  then show "front os' = front os ∧ initia os' = initia os"
    by (auto split: llist.splits event.splits)
qed

lemma nop_leaf_ooo_input_op:
  "nop_leaf None (ooo_input_op ops os)"
  unfolding ooo_input_op_def
  by (rule nop_leaf_builder_op[OF logic_frontier_stable_ooo_input_op_logic]) simp

lemma nop_leaf_batch_op:
  "nop_leaf None (batch_op os f)"
  unfolding batch_op_def batch_op_logic_def notifier_op_def
  apply (rule nop_leaf_builder_op)
  subgoal
    unfolding logic_frontier_stable_def
    by (auto simp add: Let_def split: prod.splits if_splits simp flip: cin.rep_eq)
  subgoal by simp
  done

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
