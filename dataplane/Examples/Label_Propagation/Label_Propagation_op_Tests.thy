theory Label_Propagation_op_Tests

imports
  Label_Propagation_op_Correctness_Extras
begin

section ‹Executable Tests for the Label Propagation Program›

text ‹Each test runs the optimized compilation of the label propagation
  program on a finite input stream and compares the outputs it produces with
  the expected ones. The traces are finite, so @{const trace_exec} returns the
  whole trace and no prefix has to be taken. The comparison is between
  @{const lset} of the trace and a set of expected outputs: the schedule
  followed by @{const trace_exec} fixes one order of the outputs, but that
  order is an artifact of the schedule rather than a property of the program,
  so the tests deliberately do not constrain it.›

abbreviation ‹test_input1 ≡ llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data ⊥ (0, 1), Data (MyPair 1 0) (3, 4), Data ⊥ (1, 2), Data (MyPair 2 0) (4, 5)]›

value "list_connections (dataflow_tree_to_graph (G (initial_state_input test_input1) initial_state_label_prop (initial_state_increment (MyPair 0 1))))"

value [GHC] "unit_test (lset (lmap show_Outs (trace_exec (compiled test_input1))))
 (set [(Loc 1 (Src 0), Inr {{1, 2, 0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr {{3, 4}, {1, 2, 0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0), Inr {{4, 5, 3, 4}, {1, 2, 0, 1}}, MyPair 2 0)])"

abbreviation ‹test_input2 ≡ llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data ⊥ (1, 2), Data ⊥ (0, 1), Data (MyPair 1 0) (3, 4), Data (MyPair 2 0) (4, 5), Mint (MyPair 3 0), Data (MyPair 3 0) (2, 3)]›
value [GHC] ‹unit_test (lset (lmap show_Outs (trace_exec (compiled test_input2))))
 (set [(Loc 1 (Src 0), Inr {{1, 1, 0, 2}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr {{3, 4}, {1, 1, 0, 2}}, MyPair 1 0),
  (Loc 1 (Src 0), Inr {{4, 5, 3, 4}, {1, 1, 0, 2}}, MyPair 2 0),
  (Loc 1 (Src 0),
   Inr {{4, 5, 3, 4, 2, 1, 3, 1, 0, 2}},
   MyPair 3 0)])›

abbreviation ‹test_input3 ≡
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data ⊥ (0, 1), Data (MyPair 1 0) (2, 3),
  Mint (MyPair 3 0), Data (MyPair 3 0) (1, 2), Mint (MyPair 4 0), Data (MyPair 4 0) (4, 5), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5)]›
value [GHC] ‹unit_test (lset (lmap show_Outs (trace_exec (compiled test_input3))))
 (set [(Loc 1 (Src 0), Inr {{0, 1}, {0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr { {2, 1, 3, 1, 0, 2}}, MyPair 3 0),
  (Loc 1 (Src 0), Inr {{2, 1, 3, 1, 0, 2}, {4, 5}}, MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {2, 3}, {0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 1, 3, 4, 0}},
   MyPair 5 0)])›

abbreviation ‹test_input4 ≡
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0),Mint (MyPair 3 0),Mint (MyPair 4 0), Mint (MyPair 5 0),
   Data (MyPair 5 0) (3, 5), Data (MyPair 4 0) (4, 5), Data (MyPair 3 0) (1, 2), Data (MyPair 1 0) (2, 3), Data ⊥ (0, 1)]›
value [GHC] ‹unit_test (lset (lmap show_Outs (trace_exec (compiled test_input4))))
 (set [(Loc 1 (Src 0), Inr {{0, 1}, {0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr { {2, 1, 3, 1, 0, 2}}, MyPair 3 0),
  (Loc 1 (Src 0), Inr {{2, 1, 3, 1, 0, 2}, {4, 5}}, MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {2, 3}, {0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 1, 3, 4, 0}},
   MyPair 5 0)])›

abbreviation ‹test_input5 ≡
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data ⊥ (0, 1), Drop ⊥, Data (MyPair 1 0) (2, 3), Drop (MyPair 1 0),
  Mint (MyPair 3 0), Drop (MyPair 2 0), Data (MyPair 3 0) (1, 2), Mint (MyPair 4 0), Drop (MyPair 3 0), Data (MyPair 4 0) (4, 5), Mint (MyPair 5 0),  Drop (MyPair 4 0), Data (MyPair 5 0) (3, 5)]›
value [GHC] ‹unit_test (lset (lmap show_Outs (trace_exec (compiled test_input5))))
 (set [(Loc 1 (Src 0), Inr {{0, 1}, {0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr { {2, 1, 3, 1, 0, 2}}, MyPair 3 0),
  (Loc 1 (Src 0), Inr {{2, 1, 3, 1, 0, 2}, {4, 5}}, MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {2, 3}, {0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 1, 3, 4, 0}},
   MyPair 5 0)])›

abbreviation ‹test_input6 ≡
  llist_of [Mint (MyPair 1 0), Mint (MyPair 4 0), Mint (MyPair 3 0),
   Data (MyPair 3 0) (1, 2), Data (MyPair 4 0) (4, 5), Mint (MyPair 2 0),
   Data ⊥ (0, 1), Data (MyPair 1 0) (2, 3), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5)]›
value [GHC] ‹unit_test (lset (lmap show_Outs (trace_exec (compiled test_input6))))
 (set [(Loc 1 (Src 0), Inr {{0, 1}, {0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr { {2, 1, 3, 1, 0, 2}}, MyPair 3 0),
  (Loc 1 (Src 0), Inr {{2, 1, 3, 1, 0, 2}, {4, 5}}, MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {2, 3}, {0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 1, 3, 4, 0}},
   MyPair 5 0)])›

abbreviation ‹test_input7 ≡
  llist_of [ Data ⊥ (0, 6), Mint (MyPair 1 0), Mint (MyPair 4 0), Mint (MyPair 3 0),
   Data (MyPair 3 0) (1, 2), Data (MyPair 4 0) (4, 5), Mint (MyPair 2 0),
   Data ⊥ (0, 1), Data (MyPair 1 0) (2, 3), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5), Data (MyPair 5 0) (6, 5)]›
value [GHC] ‹unit_test (lset (lmap show_Outs (trace_exec (compiled test_input7))))
 (set [(Loc 1 (Src 0), Inr {{0, 0, 1, 6}}, MyPair 0 0),
  (Loc 1 (Src 0),
   Inr {{2, 3, 1, 2, 0, 0, 1, 6}},
   MyPair 3 0),
  (Loc 1 (Src 0),
   Inr {{4, 5}, {2, 3, 1, 2, 0, 0, 1, 6}},
   MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {0, 0, 1, 6}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 3, 4, 6, 1, 0}},
   MyPair 5 0)])›

abbreviation ‹test_input8 ≡
  llist_of [Data ⊥ (0, 6), Mint (MyPair 3 0), Data (MyPair 3 0) (1, 2), Data ⊥ (0, 1)]›
value [GHC] ‹unit_test (lset (lmap show_Outs (trace_exec (compiled test_input8))))
 (set [(Loc 1 (Src 0), Inr {{0, 1, 6}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr {{1, 2, 0, 6}}, MyPair 3 0)])›

abbreviation ‹test_input9 ≡
  llist_of [ Data ⊥ (0, 6), Data ⊥ (0, 1), Data (MyPair 1 0) (2, 3)]›
value [GHC] "unit_test (lset (lmap show_Outs (trace_exec (compiled test_input9))))
 (set [(Loc 1 (Src 0), Inr {{0, 1, 6}}, MyPair 0 0), (Loc 1 (Src 0), Inr {{2, 3}, {0, 1, 6}}, MyPair 1 0)])"

end
