(* Base image for the Dataplane session.

   This theory has no content of its own.  It exists so that everything the
   Dataplane session needs from outside its own directory is loaded into one
   heap image, namely this session's.

   Without it, `isabelle jedit -d . -R Dataplane` cannot simply reuse the
   parent heap: Dataplane imports AFP theories that are not part of
   Nondeterministic_Dataflow, so Isabelle synthesises a session
   "Dataplane_requirements(Nondeterministic_Dataflow)" and builds it before
   the editor appears (see Sessions.Background.load in
   src/Pure/Build/sessions.scala).  With Dataplane_Base as the parent, the
   ancestor already provides those theories, the synthetic session is empty,
   and the editor starts against the prebuilt heap.

   Keep the import list in sync with the external imports of dataplane/. *)

theory Dataplane_Base
  imports
    "Automatic_Refinement.Misc"
    "Coinductive.Coinductive_List"
    "Collections.HashCode"
    "Containers.Collection_Order"
    "DFS_Framework.Cyc_Check"
    "HOL-Eisbach.Eisbach"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Countable"
    "HOL-Library.Multiset"
    "HOL-Library.Numeral_Type"
    "HOL-Library.Product_Lexorder"
    "HOL-Library.While_Combinator"
    "Progress_Tracking.Antichain"
    "Progress_Tracking.Auxiliary"
    "Progress_Tracking.Graph"
    "Progress_Tracking.Propagate"
    "Refine_Monadic.Refine_Monadic"
begin

end
