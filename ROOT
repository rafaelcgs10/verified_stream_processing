session Nondeterministic_Dataflow in nondeterministic_dataflow = Coinductive +
  options [timeout = 600]
  theories
    "Operator"
    "BNA_Operators"
    "Cset_Setup"
    "Defaults"
    "CSet_LList_Impl"
    "Coinductive_List_Auxiliary"
    "Eval"
    Numeral_Auxiliary
    Debug_Utils

session Dataplane in dataplane = Nondeterministic_Dataflow +
  options [timeout = 6000]
  sessions
    DFS_Framework
    Progress_Tracking
  theories
    DFS_Framework.Cyc_Check
    Progress_Tracking.Propagate
    Progress_Tracking.Auxiliary
(*     Zero_Cyc_Check  *)