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
  Branch_op
begin

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
   initia = False,
   nfron = False,
   en1 = id,
   de1 = id,
   es = inps
   \<rparr>"

abbreviation init_operator_state where
"init_operator_state \<equiv> \<lparr> 
   summar = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = Code.abort (STR ''Frontier of op2 not initialized'') (\<lambda> _ _. antichain_from_list []),
   ocaps = (\<lambda> _. []),
   initia = False,
   nfron = False
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
   initia = False,
   nfron = False,
   en1 = id,
   de1 = id,
   en2 = id,
   de2 = id
   \<rparr>"

abbreviation "nid0 \<equiv> (0 :: 4)"
abbreviation "nid1 \<equiv> (1 :: 4)"
abbreviation "nid2 \<equiv> (2 :: 4)"
abbreviation "nid3 \<equiv> (2 :: 4)"
abbreviation "p0 \<equiv> (0 :: 2)"
abbreviation "p1 \<equiv> (1 :: 2)"

abbreviation "logic_map nid op \<equiv> map_op (case_option (Inl nid) (\<lambda> p. Inr (nid, p))) (case_option (Inl nid) (\<lambda> p. Inr (nid, p))) op"

abbreviation "inp_op nid inps \<equiv> logic_map nid (ooo_input_op {|p0|} (init_input_state inps))"

abbreviation "collatz_op os \<equiv> tmap_op p0 p0 os (\<lambda> (n, x). if even x then (n, x div 2) else (n, 3 * x + 1))"
abbreviation "coll_op nid \<equiv> logic_map nid (collatz_op init_operator_state_ty2)"

abbreviation "conc_op nid \<equiv> logic_map nid (concat_op {|p0, p1|} p0 init_operator_state)"

abbreviation "bran_op nid \<equiv> logic_map nid (branch_op p0 p0 p1 (\<lambda> (x, t). t < 100) init_operator_state)"

abbreviation "comp_op_map \<equiv> map_op (case_sum id id) (case_sum id id)"

abbreviation "g0 \<equiv>
   comp_op_map (comp_op [Inr (nid3, p0) \<mapsto> Inr (nid1, p0)] (\<lambda> _. []) (conc_op nid3) (coll_op nid1))"

abbreviation "g1 inps \<equiv>
   comp_op_map (comp_op [Inr (nid0, p0) \<mapsto> Inr (nid1, p0)] (\<lambda> _. []) (inp_op nid0 inps) g0)"

abbreviation "g2 inps \<equiv>
   comp_op_map (comp_op [Inr (nid1, p0) \<mapsto> Inr (nid2, p0)] (\<lambda> _. []) (g1 inps) (bran_op nid2))"


abbreviation "inpp_op inps \<equiv>
   ((inp_op nid0 inps))"

abbreviation "op \<equiv> g2 (\<lambda> p. llist_of [Data (0 :: nat) (5 :: nat, 5 :: nat)])"

definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc 0 (Src 1) \<and> l2 = Loc 1 (Trg 0) 
   then antichain_from_list [0]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [0]
   else {}\<^sub>A)"


abbreviation \<open>sg \<equiv> init_subgraph my_summ (map (\<lambda> (nid, p). (Loc nid (Src p), bot, 1)) (List.product Enum.enum Enum.enum))\<close>
abbreviation "dt \<equiv> dataflow_op sg op"

definition "r = (trace_exec dt :: (unit, _ \<times> _, (nat \<times> nat) \<times> nat) VIO llist)"

term DEBUG

value [GHC] r

value [GHC] "p0"
value [GHC] "p1"

value [GHC] nid0
value [GHC] nid1
value [GHC] nid2

(* export_code r in Haskell module_name Test2
 *)
(* 
value [GHC] "check_prefix [VOut (1, 1) ((2, 2), 0)] dt"
 *)

end