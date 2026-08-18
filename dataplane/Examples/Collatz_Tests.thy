theory Collatz_Tests

imports
  Collatz
begin

section ‹Executable Tests for the Collatz Program›

value "list_connections (dataflow_tree_to_graph dt)"

text ‹The input stream is finite and every number reaches @{term 1}, so the
  trace is finite and @{const trace_exec} returns all of it. The outputs are
  compared as a lazy list, which fixes their order as well: the schedule
  followed by @{const trace_exec} emits them in increasing iteration count.›

value [GHC] "unit_test (lmap show_Outs (trace_exec compiled)) (llist_of
  [(Loc 3 (Src 0), (2, 1), 0), (Loc 3 (Src 0), (6, 1), 7), (Loc 3 (Src 0), (12, 1), 8),
   (Loc 3 (Src 0), (11, 1), 13), (Loc 3 (Src 0), (7, 1), 15), (Loc 3 (Src 0), (15, 1), 16),
   (Loc 3 (Src 0), (9, 1), 18), (Loc 3 (Src 0), (18, 1), 19)])"

end
