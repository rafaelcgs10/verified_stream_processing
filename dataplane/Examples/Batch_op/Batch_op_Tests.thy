theory Batch_op_Tests

imports
  Batch_op_Nop_Invariant
begin

section ‹Executable Tests for the Batch Program›

abbreviation "t0 ≡ MyPair (0 :: nat) (0 :: nat)"
abbreviation "t_1_0 ≡ MyPair (Suc 0) (0 :: nat)"
abbreviation "t_0_1 ≡ MyPair (0 :: nat) (Suc 0)"
abbreviation "t_1_1 ≡ MyPair (Suc 0) (Suc 0)"

abbreviation "batch_max ≡ (λ b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)])"

abbreviation "batch_prog inps ≡ compiled_batch_op_opt (λ _. inps) batch_max"

abbreviation "batch_outputs op ≡ lmap (λ io. case io of VOut p (x, t) ⇒ (projr x, t)) (trace_exec op)"

abbreviation "list_inps_test ≡ 
 [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"
abbreviation "inps_test ≡ llist_of list_inps_test"

value [GHC] "unit_test (check_prefix 5500 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] (batch_prog inps_test)) True"
value [GHC] "unit_test (batch_outputs (batch_prog inps_test)) (llist_of [(7, MyPair 0 1), (10, MyPair 1 1), (3, MyPair 1 0)])"

abbreviation "list_inps_test2 ≡ 
 [ Mint t_1_0, Data t_1_0 10, Data t0 (7 :: nat), Drop t0, Drop t_1_0]"
abbreviation "inps_test2 ≡ llist_of list_inps_test2"

section ‹Trace-Nondeterminism Demonstrated on the Optimized Wrapper›

text ‹The stuttering options that defeat the search above are exactly the ones
  classified as nops by @{term not_nop}: frontier reads that deliver what the
  node already knows, and progress writes with nothing to report. The operator
  @{const dataflow_opt_op} filters them out of every choice set, which makes
  the choice tree finite for finite inputs, so the search terminates and can
  answer both positively and negatively.

  This is sound as evidence about the real semantics because
  @{thm [source] dataflow_opt_op_wbisim_start} states that the optimized
  wrapper is weakly bisimilar to @{const dataflow_op}, and weakly bisimilar
  operators have the same weak traces.

  The @{term nop_invariant} hypothesis of that corollary is discharged for
  all builder-compiled dataflow trees by the generic theorem in theory
  Tree_Nop_Invariant, instantiated for this example in theory
  Batch_op_Nop_Invariant. The checks below therefore carry no pending
  hypotheses.›

text ‹On @{term inps_test2} both orders are possible. Outputting 7 first is the
  schedule where the input operator reports progress after @{term "Drop t0"}
  but before consuming @{term "Drop t_1_0"}, so only @{term t0} is complete and
  the notifier fires for it alone.›

value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 7, MyPair 0 0))] (batch_prog inps_test2)) True"
value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 10, MyPair 1 0))] (batch_prog inps_test2)) True"

text ‹The whole second trace, not only its first element.›

value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 7, MyPair 0 0)), ((1, 1), (Inr 10, MyPair 1 0))] (batch_prog inps_test2)) True"
value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 10, MyPair 1 0)), ((1, 1), (Inr 7, MyPair 0 0))] (batch_prog inps_test2)) True"

text ‹The same phenomenon on the richer input @{term inps_test}: the elements
  at @{term t_1_1} and @{term t_0_1} can also come out in the order reversed
  with respect to the check at the start of the example.›

value [GHC] "unit_test (check_prefix 5500 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] (batch_prog inps_test)) True"

section ‹Trace-Nondeterminism on Two Incomparable Timestamps›

text ‹The stream below is the one drawn in the thesis figure. The operator
  @{const ooo_input_op} starts holding the capability of the bottom timestamp
  @{term t0}, mints the two incomparable timestamps @{term t_1_0} and
  @{term t_0_1}, drops @{term t0}, sends one data item at each of the two
  minted timestamps, and finally drops @{term t_0_1} and then @{term t_1_0}.
  Neither of the two data timestamps is below the other, so nothing in the
  order on timestamps decides which of the two batches is emitted first.›

abbreviation "list_inps_test3 ≡
 [Mint t_1_0, Mint t_0_1, Drop t0, Data t_1_0 (10 :: nat), Data t_0_1 7,
  Drop t_0_1, Drop t_1_0]"
abbreviation "inps_test3 ≡ llist_of list_inps_test3"

text ‹Frontier-driven order. The notifier of @{const batch_op} fires as soon as
  the drop of @{term t_0_1} has been propagated, so the batch of
  @{term t_0_1} leaves first and the batch of @{term t_1_0} follows only after
  the drop of @{term t_1_0}. This schedule requires the input operator to pause
  between its two drops, which the depth-first search of @{const check_prefix}
  only reaches after exploring every schedule that keeps draining the input, so
  this check takes about twelve minutes. The check below it, whose order is the
  one a greedy schedule produces, answers in twenty seconds.›
value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 0))] (batch_prog inps_test3)) True"
(* WARNING: the check above takes about twelve minutes. The schedule it looks
   for pauses the input operator between its two drops, and the depth-first
   search of check_prefix only reaches it after exploring every schedule that
   keeps draining the input first. Every other check in this file answers in
   under a minute. *)

text ‹Consumption-driven order. Here @{const batch_op} delays its logic until
  both drops have happened, and then its own bookkeeping decides the order:
  the timestamps are emitted in the order in which they were first consumed,
  which is @{term t_1_0} before @{term t_0_1}.›

value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 10, MyPair 1 0)), ((1, 1), (Inr 7, MyPair 0 1))] (batch_prog inps_test3)) True"

text ‹The order is open but the pairing of data with timestamps is not: no
  schedule pairs the batch of @{term t_1_0} with the timestamp @{term t_0_1},
  so the check below answers negatively. A negative answer has to rule out
  every schedule, so the search explores the whole choice tree and the check
  is left commented out.›
(* 
value [GHC] "unit_test (check_prefix 55500 [((1, 1), (Inr 10, MyPair 0 1))] (batch_prog inps_test3)) False"
 *)

text ‹The single schedule followed by @{const trace_exec} exhibits one of the
  two orders without any search. Its whole trace has two elements, so the
  batch of @{term t_1_0} really does leave before the batch of @{term t_0_1}
  in this schedule.›

value [GHC] "unit_test (batch_outputs (batch_prog inps_test3)) (llist_of [(10, MyPair 1 0), (7, MyPair 0 1)])"

text ‹One cannot isolate the other order by truncating the stream before the
  last drop: when the event stream of @{const ooo_input_op} reaches
  @{const LNil} its logic gives up every capability it still holds, so the
  truncated stream also ends with both timestamps complete and produces the
  same two outputs. Only a schedule that leaves the last drop unconsumed keeps
  the capability of @{term t_1_0} alive, which is what the first check above
  searches for.›

end
