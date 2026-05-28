theory Collatz

imports
  Dataplane.Timely_Stream
  Dataplane.Numeral_Conversion
  Ooo_Input_op
  "../MyProduct_Instances"
  "../AntichainOrder"
   Dataplane.LList_Haskell_Setup
  Source_op
  Tmap_op
  Concat_op
  Branch_op
  Increment_op
  Dataplane.Timely_Builder_Op
  Dataplane.Timely_Dataflow_Op
begin

abbreviation init_input_state where
"init_input_state inps \<equiv> \<lparr> 
   intsum = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = \<lambda> _. antichain_from_list bots,
   ocaps = \<lambda> _. bots,
   initia = True,
   en1 = id,
   de1 = id,
   is_en1 = \<top>,
   es = inps
   \<rparr>"

abbreviation init_operator_state where
"init_operator_state \<equiv> \<lparr> 
   intsum = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = \<lambda> _. antichain_from_list bots,
   ocaps = \<lambda> _. bots,
   initia = True
   \<rparr>"

abbreviation init_operator_state_ty2 where
"init_operator_state_ty2 \<equiv> \<lparr> 
   intsum = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = \<lambda> _. antichain_from_list bots,
   ocaps = \<lambda> _. bots,
   initia = True,
   en1 = id,
   de1 = id,
   is_en1 = \<top>,
   en2 = id,
   de2 = id,
   is_en2 = \<top>
   \<rparr>"


abbreviation "collatz_op os \<equiv> tmap_op 0 0 os (\<lambda> (n, x). if even x then (n, x div 2) else (n, 3 * x + 1))"
abbreviation "inps \<equiv> \<lambda> p. llist_of [Data (0 :: nat) (12 :: nat, 12 :: nat), Data 0 (2, 2)]"
abbreviation "n1 \<equiv> Logic (ooo_input_op {|0 :: 2|} (init_input_state inps)) default_internal_summary"
abbreviation "n2 \<equiv> Logic (concat_op {|0, 1|} 0 init_operator_state) default_internal_summary"
abbreviation "n3 \<equiv> Logic (collatz_op init_operator_state_ty2) default_internal_summary"
abbreviation "n4 \<equiv> Logic (branch_op 0 0 1 (\<lambda> (x, t). snd x \<le> 1 \<or> t > 100) init_operator_state) default_internal_summary"
abbreviation "n5 \<equiv> Logic (increment_op 1 1 1 init_operator_state) (\<lambda> p1 p2. if 1 = p2 then [1] else [])"

definition tscomp_op (infixl "\<sqdot>" 65) where
  "tscomp_op op1 op2 = Comp (\<lambda> (nid, p). if nid = 0 then Some (0, p) else None) op1 op2"

abbreviation G :: "(5, 2, (2, nat) shared_state + (2 \<Rightarrow> nat antichain), (nat \<times> nat) \<times> nat, nat) dataflow_tree" where
  "G \<equiv> Comp [(0, 0) \<mapsto> (0, 0)] n1 (Loop [(3, 1) \<mapsto> (0, 1)] ((Comp [(0, 0) \<mapsto> (0, 0)] n2 (Comp [(0, 0) \<mapsto> (0, 0)] n3 (Comp [(0, 1) \<mapsto> (0, 1)] n4 n5)))))"

value "list_connections (dataflow_tree_to_graph G)"

abbreviation "compiled \<equiv> opt_compile_dataflow (\<lambda> _. []) G"
value [GHC] "ltaken 2 (lmap show_Outs (trace_exec compiled))"


abbreviation G' :: "(5, 2, (2, nat) shared_state + (2 \<Rightarrow> nat antichain), (nat \<times> nat) \<times> nat, nat) dataflow_tree" where
  "G' \<equiv> Comp [(0, 0) \<mapsto> (0, 0)] n1 (Loop [(3, 1) \<mapsto> (0, 1)] (Comp [(2, 1) \<mapsto> (0, 1)] (Comp [(1, 0) \<mapsto> (0, 0)] (Comp [(0, 0) \<mapsto> (0, 0)] n2 n3) n4) n5))"

abbreviation "compiled' \<equiv> compile_dataflow (\<lambda> _. []) G"
value [GHC] "ltaken 2 (lmap show_Outs (trace_exec compiled'))"


(* value [GHC] "check_prefix 100000000 [((nid2, 0), ((4, 1), 1))] dt" *)


(* 
 export_code r2 in Haskell module_name Test10
 *)

term not_nop

end
