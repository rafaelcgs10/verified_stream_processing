(* Session setup for the complete formalization.

   Nondeterministic_Dataflow  the operator model of Chapters 4 and 5,
                              including the algebra tables
   Dataplane                  everything built on top of it, Chapters 6 to 11

   Build both with:  isabelle build -d . -v Dataplane
   Browse them with: isabelle jedit -d . -R Dataplane                       *)

session Nondeterministic_Dataflow in nondeterministic_dataflow = Coinductive +
  options [timeout = 12000]
  directories
    "table_1"
    "table_2"
    "table_3"
  theories
    BNA_Operators
    CSet_LList_Impl
    Coinductive_List_Auxiliary
    Cset_Setup
    Debug_Utils
    Defaults
    Eval
    Eval_Examples
    Lifted
    Lifted_Table_1
    Lifted_Table_2
    Lifted_Table_3
    Numeral_Auxiliary
    Operator
    Wstep_Composition
    Wstep_Composition_Left_Right
    "table_1/B1"
    "table_1/B10"
    "table_1/B2"
    "table_1/B3"
    "table_1/B4"
    "table_1/B5"
    "table_1/B6"
    "table_1/B7"
    "table_1/B8"
    "table_1/B9"
    "table_1/F1"
    "table_1/F2"
    "table_1/R1"
    "table_1/R2"
    "table_1/R3"
    "table_1/R4"
    "table_1/R5"
    "table_1/R6"
    "table_2/T2A1"
    "table_2/T2A10"
    "table_2/T2A11"
    "table_2/T2A12"
    "table_2/T2A13"
    "table_2/T2A14"
    "table_2/T2A15"
    "table_2/T2A16"
    "table_2/T2A17"
    "table_2/T2A18"
    "table_2/T2A19"
    "table_2/T2A2"
    "table_2/T2A3"
    "table_2/T2A4"
    "table_2/T2A5"
    "table_2/T2A6"
    "table_2/T2A7"
    "table_2/T2A8"
    "table_2/T2A9"
    "table_2/T2F3"
    "table_2/T2F4"
    "table_2/T2F5"
    "table_3/T3A1"
    "table_3/T3A12"
    "table_3/T3A13"
    "table_3/T3A14"
    "table_3/T3A15"
    "table_3/T3A16"
    "table_3/T3A17"
    "table_3/T3A18"
    "table_3/T3A19"
    "table_3/T3A2"
    "table_3/T3A3"
    "table_3/T3A4"
    "table_3/T3A6"
    "table_3/T3A8"
    "table_3/T3A9"
    "table_3/T3F3"
    "table_3/T3F4"

(* Everything the data plane imports from outside its own directory, gathered
   into one heap image.  Without this, "isabelle jedit -R" cannot reuse the
   parent heap: it would synthesise and build a "Dataplane_requirements(...)"
   session first.  Keep in sync with dataplane/Base/Dataplane_Base.thy. *)
session Dataplane_Base in "dataplane/Base" = Nondeterministic_Dataflow +
  options [timeout = 12000]
  sessions
    "HOL-Eisbach"
    Automatic_Refinement
    Refine_Monadic
    Collections
    Containers
    DFS_Framework
    Progress_Tracking
  theories
    Dataplane_Base

(* The infrastructure: libraries, the data plane, the progress tracker and the
   reusable correctness theories.  Everything the case studies build on lives
   here, so that opening a case study in the editor takes all of it from this
   session's heap instead of replaying it. *)
session Dataplane_Core in dataplane = Dataplane_Base +
  options [timeout = 12000]
  sessions
    "HOL-Eisbach"
    Automatic_Refinement
    Refine_Monadic
    Collections
    Containers
    DFS_Framework
    Progress_Tracking
  directories
    "Common_Operators"
    "Correctness"
    "Lib"
    "Timely"
  theories
    "Common_Operators/Accumulator"
    "Common_Operators/Branch_Op"
    "Common_Operators/Concat_Op"
    "Common_Operators/Increment_Op"
    "Common_Operators/Increment_Op_Correctness"
    "Common_Operators/Ooo_Input_Op"
    "Common_Operators/Ooo_Input_Op_Correctness"
    "Common_Operators/Set_Op"
    "Common_Operators/Source_Op"
    "Common_Operators/Tmap_Op"
    "Correctness/Consumes"
    "Correctness/General"
    "Correctness/Ifrontier"
    "Correctness/Init"
    "Correctness/Mints"
    "Correctness/OCapsReorder"
    "Correctness/Outputs"
    "Correctness/Produces"
    "Correctness/Progress"
    "Correctness/Progress_Extraction"
    "Correctness/Propagates"
    "Correctness/Propagation_Properties"
    "Correctness/Timely_Collections"
    "Lib/AntichainOrder"
    "Lib/Bots"
    "Lib/CsetUtils"
    "Lib/DataplaneUtils"
    "Lib/Executable"
    "Lib/LList_Haskell_Setup"
    "Lib/ListUtils"
    "Lib/Locations"
    "Lib/MyMisc"
    "Lib/MyProduct_Instances"
    "Lib/Numeral_Conversion"
    "Lib/Operators_Utils"
    "Lib/SimulationProofMethods"
    "Lib/Termination"
    "Lib/Zero_Cyc_Check"
    "Lib/ZmsetUtils"
    "Timely/Builder_Op"
    "Timely/Dataflow_Op"
    "Timely/Dataflow_Opt_Op"
    "Timely/Nop_Step_Lemmas"
    "Timely/Operator_State"
    "Timely/Propagation_Exec"
    "Timely/Propagation_Idempotence"
    "Timely/Tree_Compile"
    "Timely/Tree_Nop_Invariant"
    Timely_Stream

(* The case studies, kept as the leaf session so that
   "isabelle jedit -d . -R Dataplane" puts only these on the editable source
   path.  Building Dataplane still checks the whole formalization, through its
   parents. *)
session Dataplane in "dataplane/Examples" = Dataplane_Core +
  options [timeout = 12000]
  sessions
    "HOL-Eisbach"
    Automatic_Refinement
    Refine_Monadic
    Collections
    Containers
    DFS_Framework
    Progress_Tracking
  directories
    "Batch"
    "Collatz"
    "Weakly_Connected_Components"
  theories
    "Batch/Batch_Op"
    "Batch/Batch_Op_Correctness"
    "Batch/Batch_Op_Nop_Invariant"
    "Batch/Batch_Op_Tests"
    "Collatz/Collatz_Nop_Invariant"
    "Collatz/Collatz_Op"
    "Collatz/Collatz_Tests"
    "Weakly_Connected_Components/Dataplane_Inv"
    "Weakly_Connected_Components/Imperative_Wcc"
    "Weakly_Connected_Components/Input0"
    "Weakly_Connected_Components/Input1"
    "Weakly_Connected_Components/Label_Propagation_Nop_Invariant"
    "Weakly_Connected_Components/Label_Propagation_Op"
    "Weakly_Connected_Components/Label_Propagation_Op_Correctness"
    "Weakly_Connected_Components/Label_Propagation_Op_Correctness_Extras"
    "Weakly_Connected_Components/Label_Propagation_Op_Tests"
    "Weakly_Connected_Components/Labels"
    "Weakly_Connected_Components/Loop"
    "Weakly_Connected_Components/Wcc"
