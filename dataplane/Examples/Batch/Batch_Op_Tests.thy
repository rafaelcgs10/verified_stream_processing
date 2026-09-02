theory Batch_Op_Tests

imports
  Batch_Op_Nop_Invariant
begin

section ‹Executable Tests for the Batch Program›

abbreviation "t0 ≡ MyPair (0 :: nat) (0 :: nat)"
abbreviation "t_1_0 ≡ MyPair (Suc 0) (0 :: nat)"
abbreviation "t_0_1 ≡ MyPair (0 :: nat) (Suc 0)"
abbreviation "t_1_1 ≡ MyPair (Suc 0) (Suc 0)"

abbreviation "batch_outputs op ≡ lmap (λ io. case io of VOut p (x, t) ⇒ (projr x, t)) (trace_exec op)"

abbreviation "list_inps_test ≡ 
 [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"
abbreviation "inps_test ≡ llist_of list_inps_test"

value [GHC] "unit_test (check_prefix 5500 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] (compile_dataflow_opt (λ _. []) (batch_tree (λ _. inps_test) batch_max))) True"
value [GHC] "unit_test (batch_outputs (compile_dataflow_opt (λ _. []) (batch_tree (λ _. inps_test) batch_max))) (llist_of [(7, MyPair 0 1), (10, MyPair 1 1), (3, MyPair 1 0)])"

abbreviation "list_inps_test2 ≡ 
 [ Mint t_1_0, Data t_1_0 10, Data t0 (7 :: nat), Drop t0, Drop t_1_0]"
abbreviation "inps_test2 ≡ llist_of list_inps_test2"

section ‹Trace-Nondeterminism Demonstrated on the Optimized Wrapper›

text ‹Pruning the nops keeps the choice tree finite, so the search below
  terminates. It is evidence about @{const dataflow_op} by
  @{thm [source] dataflow_opt_op_wbisim_start}, whose @{term nop_invar}
  hypothesis is discharged in theory Batch_op_Nop_Invariant.›

value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 7, MyPair 0 0))] (compile_dataflow_opt (λ _. []) (batch_tree (λ _. inps_test2) batch_max))) True"
value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 10, MyPair 1 0))] (compile_dataflow_opt (λ _. []) (batch_tree (λ _. inps_test2) batch_max))) True"

value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 7, MyPair 0 0)), ((1, 1), (Inr 10, MyPair 1 0))] (compile_dataflow_opt (λ _. []) (batch_tree (λ _. inps_test2) batch_max))) True"
value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 10, MyPair 1 0)), ((1, 1), (Inr 7, MyPair 0 0))] (compile_dataflow_opt (λ _. []) (batch_tree (λ _. inps_test2) batch_max))) True"

value [GHC] "unit_test (check_prefix 5500 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] (compile_dataflow_opt (λ _. []) (batch_tree (λ _. inps_test) batch_max))) True"

section ‹Trace-Nondeterminism on Two Incomparable Timestamps›

text ‹The stream ‹inps› and the program ‹prog› below are defined at the
  end of theory ‹Batch_Op›, and they are the ones drawn in the thesis
  figure.›

text ‹Frontier-driven order.›
value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 0))] prog) True"
(* WARNING: the check above takes about twelve minutes. The schedule it looks
   for pauses the input operator between its two drops, and the depth-first
   search of check_prefix only reaches it after exploring every schedule that
   keeps draining the input first. Every other check in this file answers in
   under a minute. *)

text ‹Consumption-driven order.›

value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 10, MyPair 1 0)), ((1, 1), (Inr 7, MyPair 0 1))] prog) True"

(* No schedule pairs the batch of t_1_0 with the timestamp t_0_1. Answering
   that negatively means ruling out every schedule, which explores the whole
   choice tree, so this check is left disabled. 
value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 10, MyPair 0 1))] prog) False"
 *)

text ‹The single schedule of @{const trace_exec}, without any search.›

value [GHC] "unit_test (batch_outputs prog) (llist_of [(10, MyPair 1 0), (7, MyPair 0 1)])"

end
