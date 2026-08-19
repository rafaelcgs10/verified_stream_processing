theory Collatz_Tests

imports
  Collatz_Nop_Invariant
begin

section ‹Executable Tests for the Collatz Program›

value "list_connections (dataflow_tree_to_graph dt)"

value [GHC] "unit_test (lmap show_Outs (trace_exec compiled)) (llist_of
  [(Loc 3 (Src 0), (2, 1), 0), (Loc 3 (Src 0), (6, 1), 7), (Loc 3 (Src 0), (12, 1), 8),
   (Loc 3 (Src 0), (11, 1), 13), (Loc 3 (Src 0), (7, 1), 15), (Loc 3 (Src 0), (15, 1), 16),
   (Loc 3 (Src 0), (9, 1), 18), (Loc 3 (Src 0), (18, 1), 19)])"

end
