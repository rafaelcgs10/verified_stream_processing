theory LList_Haskell_Setup

imports
  "Coinductive.Coinductive_List"
  Nondeterministic_Dataflow.CSet_LList_Impl
  "Timely_Infrastructure"
begin

(* code_printing code_module "Deter" \<rightharpoonup> (Haskell)
  \<open>
module Deter (cthe_elem, Cset (..) ) where

newtype Cset a = Cset_of_llist [a];

cthe_elem (Cset_of_llist xs) = Prelude.head xs;
\<close>
 *)



(*    | constant sum_list \<rightharpoonup>
    (Haskell) "sum"  *)
(*   | constant fold \<rightharpoonup>
    (Haskell) "(\\f xs x -> Prelude.foldl f x xs)"
 *)

end