theory Collatz

imports
  Dataplane.Timely_Stream
  Ooo_Input_op
  "../MyProduct_Instances"
  "../AntichainOrder"
   Dataplane.LList_Haskell_Setup
  Source_op
  Tmap_op
  Concat_op
begin

abbreviation "collatz_op os \<equiv> tmap_op os (\<lambda> (n, x). if even x then (n, x div 2) else (n, 3 * x + 1))"

abbreviation init_input_state where
"init_input_state inps \<equiv> \<lparr> 
   summar = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = Code.abort (STR ''Frontier of op1 not initialized'') (\<lambda> _ _. antichain_from_list []),
   ocaps = (\<lambda> _. [\<bottom>]),
   initia = True,
   nfron = False,
   en1 = id,
   de1 = id,
   es = inps
   \<rparr>"

abbreviation init_operator_state_ty2 where
"init_operator_state_ty2 \<equiv> \<lparr> 
   summar = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = Code.abort (STR ''Frontier of op2 not initialized'') (\<lambda> _ _. antichain_from_list []),
   ocaps = (\<lambda> _. []),
   initia = True,
   nfron = False,
   en1 = id,
   de1 = id,
   en2 = id,
   de2 = id
   \<rparr>"

abbreviation "nid0 \<equiv> 0 :: 2"
abbreviation "nid1 \<equiv> 1 :: 2"

abbreviation "inp_op nid inps \<equiv> map_op (case_option (Inl nid) (\<lambda> p. Inr (nid, p))) (case_option (Inl nid) (\<lambda> p. Inr (nid, p))) (ooo_input_op {|1|} (init_input_state inps))"

abbreviation "coll_op nid \<equiv> map_op (case_option (Inl nid) (\<lambda> p. Inr (nid, p))) (case_option (Inl nid) (\<lambda> p. Inr (nid, p))) (collatz_op init_operator_state_ty2)"

abbreviation "conc_op \<equiv> concat_op {|1, 2|} 1 init_operator_state_ty2"

abbreviation "graph_op inps \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (nid0, 0 :: 1) \<mapsto> Inr (nid1, 0)] (\<lambda> _. []) (inp_op nid0 inps) (coll_op nid1))"

abbreviation "inpp_op inps \<equiv>
   ((inp_op nid0 inps))"

abbreviation "op \<equiv> graph_op (\<lambda> (p :: 1). llist_of [Data (0 :: nat) (5 :: nat, 5 :: nat)])"

definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc 0 (Src 1) \<and> l2 = Loc 1 (Trg 0) 
   then antichain_from_list [0]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [0]
   else {}\<^sub>A)"


abbreviation \<open>sg \<equiv> init_subgraph my_summ (map (\<lambda> (nid, p). (Loc nid (Src p), bot, 1)) (List.product Enum.enum Enum.enum))\<close>

abbreviation "dt \<equiv> (dataflow_op sg op) :: (unit, 2 \<times> 1, (nat \<times> nat) \<times> nat) op"

term DEBUG

definition "r = trace_exec dt"

value [GHC] r

(* export_code r in Haskell module_name Test2
 *)
(* 
value [GHC] "check_prefix [VOut (1, 1) ((2, 2), 0)] dt"
 *)

end