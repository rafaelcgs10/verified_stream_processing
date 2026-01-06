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
  Increment_op
begin

abbreviation init_input_state where
"init_input_state inps \<equiv> \<lparr> 
   summar = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = Code.abort (STR ''Frontier not initialized'') (\<lambda> _ _. antichain_from_list []),
   ocaps = (\<lambda> _. [\<bottom>]),
   initia = True,
   nfron = False,
   en1 = id,
   de1 = id,
   is_en1 = \<top>,
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
   front = Code.abort (STR ''Frontier not initialized'') (\<lambda> _ _. antichain_from_list []),
   ocaps = (\<lambda> _. []),
   initia = True,
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
   front = Code.abort (STR ''Frontier not initialized'') (\<lambda> _ _. antichain_from_list []),
   ocaps = (\<lambda> _. []),
   initia = True,
   nfron = False,
   en1 = id,
   de1 = id,
   is_en1 = \<top>,
   en2 = id,
   de2 = id,
   is_en2 = \<top>
   \<rparr>"

definition "nid0 = 0"
definition "nid1 = 1"
definition "nid2 = 2"
definition "nid3 = 3"
definition "nid4 = (4 :: 5)"
definition "p0 = (0 :: 2)"
definition "p1 = (1 :: 2)"

abbreviation "logic_map nid op \<equiv> map_op (case_option (Inl nid) (\<lambda> p. Inr (nid, p))) (case_option (Inl nid) (\<lambda> p. Inr (nid, p))) op"

abbreviation "inp_op nid inps \<equiv> logic_map nid (ooo_input_op {|p0|} (init_input_state inps))"

abbreviation "collatz_op os \<equiv> tmap_op p0 p0 os (\<lambda> (n, x). if even x then (n, x div 2) else (n, 3 * x + 1))"
abbreviation "coll_op nid \<equiv> logic_map nid (collatz_op init_operator_state_ty2)"

abbreviation "conc_op nid \<equiv> logic_map nid (concat_op {|p0, p1|} p0 init_operator_state)"

abbreviation "bran_op nid \<equiv> logic_map nid (branch_op p0 p0 p1 (\<lambda> (x, t). snd x \<le> 1 \<or> t > 100) init_operator_state)"

abbreviation "incr_op nid \<equiv> logic_map nid (increment_op p1 p1 1 init_operator_state)"

abbreviation "comp_op_map \<equiv> map_op (case_sum id id) (case_sum id id)"

abbreviation "g0 \<equiv>
   comp_op_map (comp_op [Inr (nid0, p0) \<mapsto> Inr (nid1, p0)] (\<lambda> _. []) (conc_op nid0) (coll_op nid1))"

abbreviation "g1 \<equiv>
   comp_op_map (comp_op [Inr (nid1, p0) \<mapsto> Inr (nid2, p0)] (\<lambda> _. []) g0 (bran_op nid2))"

abbreviation "g2 \<equiv>
   comp_op_map (comp_op [Inr (nid2, p1) \<mapsto> Inr (nid3, p1)] (\<lambda> _. []) g1 (incr_op nid3))"

abbreviation "g3 \<equiv>
   loop_op [Inr (nid3, p1) \<mapsto> Inr (nid0, p1)] (\<lambda> _. []) g2"

abbreviation "g4 inps \<equiv>
   comp_op_map (comp_op [Inr (nid4, p0) \<mapsto> Inr (nid0, p0)] (\<lambda> _. []) (inp_op nid4 inps) g3)"

abbreviation "inps0 \<equiv> (\<lambda> p. llist_of []) :: 'a \<Rightarrow> (nat, nat \<times> nat) event llist"
abbreviation "inps1 \<equiv> \<lambda> p. llist_of [Data (0 :: nat) (12 :: nat, 12 :: nat), Data 0 (2, 2)]"

abbreviation "op \<equiv> g4 inps1"

definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc nid4 (Src p0) \<and> l2 = Loc nid0 (Trg p0) 
   then antichain_from_list [0]
   else if l1 = Loc nid0 (Trg p0) \<and> l2 = Loc nid0 (Src p0)
   then antichain_from_list [0]
   else if l1 = Loc nid0 (Src p0) \<and> l2 = Loc nid1 (Trg p0)
   then antichain_from_list [0]
   else if l1 = Loc nid1 (Trg p0) \<and> l2 = Loc nid1 (Src p0)
   then antichain_from_list [0]
   else if l1 = Loc nid1 (Src p0) \<and> l2 = Loc nid2 (Trg p0)
   then antichain_from_list [0]
   else if l1 = Loc nid2 (Trg p0) \<and> l2 = Loc nid2 (Src p0)
   then antichain_from_list [0]
   else if l1 = Loc nid2 (Src p1) \<and> l2 = Loc nid3 (Trg p1)
   then antichain_from_list [0]
   else if l1 = Loc nid3 (Trg p1) \<and> l2 = Loc nid3 (Src p1)
   then antichain_from_list [1]
   else if l1 = Loc nid3 (Src p1) \<and> l2 = Loc nid0 (Trg p1)
   then antichain_from_list [0]
   else {}\<^sub>A)"


abbreviation \<open>sg \<equiv> init_subgraph my_summ (map (\<lambda> (nid, p). (Loc nid (Src p), bot, 1)) (List.product Enum.enum Enum.enum))\<close>
abbreviation "dt \<equiv> dataflow_op sg op"

definition "r = (trace_exec dt :: (_, _ \<times> _, (nat \<times> nat) \<times> nat) VIO llist)"

term DEBUG

value [GHC] r


value [GHC] "check_prefix 500 [((nid2, p0), ((2, 1), 0))] dt"
definition "r2 = check_prefix 250 [((nid2, p0), ((4, 1), 1))] dt"

value [GHC] r2

thm cUn_code

(* 
 export_code r2 in Haskell module_name Test10
 *)


end