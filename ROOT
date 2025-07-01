session Nondeterministic_Dataflow in nondeterministic_dataflow = Coinductive +
  options [timeout = 600]
  theories
    "Operator"
    "BNA_Operators"
    "Cset_Setup"
    "Defaults"
    "CSet_LList_Impl"
    "Coinductive_List_Auxiliary"

session Propagation_Extras in propagation_extras = Progress_Tracking +
  options [timeout = 6000]
  theories
    Progress_Tracking.Propagate
    Progress_Tracking.Auxiliary

session Dataplane in dataplane = Nondeterministic_Dataflow + 
  options [timeout = 6000]
  sessions
    DFS_Framework
    Propagation_Extras
  theories
    DFS_Framework.Cyc_Check