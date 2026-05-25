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
  Dataplane.Timely_Builder_Op
  Dataplane.Timely_Dataflow_Op
begin

definition zero_to_nat where
  "zero_to_nat (n :: 0) = (0 :: nat)"
definition one_to_nat where
  "one_to_nat (n :: 1) = (0 :: nat)"
definition two_to_nat where
  "two_to_nat (n :: 2) = 
   (if n = 0 
   then (0 :: nat) 
   else 1)"
definition three_to_nat where
  "three_to_nat (n :: 3) = 
   (if n = 0 
   then (0 :: nat) 
   else (if n = 1 
   then 1
   else 2))"
definition four_to_nat where
  "four_to_nat (n :: 4) = 
   (if n = 0 
   then (0 :: nat) 
   else (if n = 1 
   then 1
   else (if n = 2
   then (2 :: nat) 
   else 3)))"
definition five_to_nat where
  "five_to_nat (n :: 5) = 
   (if n = 0 
   then (0 :: nat) 
   else (if n = 1 
   then 1
   else (if n = 2
   then (2 :: nat) 
   else (if n = 3
   then (3 :: nat) 
   else 4))))"

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

abbreviation "inps0 \<equiv> (\<lambda> p. llist_of []) :: 'a \<Rightarrow> (nat, nat \<times> nat) event llist"
abbreviation "inps1 \<equiv> \<lambda> p. llist_of [Data (0 :: nat) (12 :: nat, 12 :: nat), Data 0 (2, 2)]"


abbreviation "l1 \<equiv> Logic (ooo_input_op {|0 :: 2|} (init_input_state inps1)) default_internal_summary"
abbreviation "l2 \<equiv> Logic (concat_op {|p0, p1|} p0 init_operator_state) default_internal_summary"
abbreviation "l3 \<equiv> Logic (collatz_op init_operator_state_ty2) default_internal_summary"
abbreviation "l4 \<equiv> Logic (branch_op p0 p0 p1 (\<lambda> (x, t). snd x \<le> 1 \<or> t > 100) init_operator_state) default_internal_summary"
abbreviation "l5 \<equiv> Logic (increment_op p1 p1 1 init_operator_state) (\<lambda> p1 p2. if p1 = p2 then [1] else [])"


abbreviation G :: "(5, 2, (2, nat) shared_state + (2 \<Rightarrow> nat antichain), (nat \<times> nat) \<times> nat, nat) dataflow_tree" where
  "G \<equiv> Comp [(0, 0) \<mapsto> (0, 0)] l1 (Loop [(3, 1) \<mapsto> (0, 1)] (Comp [(2, 1) \<mapsto> (0, 1)] (Comp [(1, 0) \<mapsto> (0, 0)] (Comp [(0, 0) \<mapsto> (0, 0)] l2 l3) l4) l5))"

value "dataflow_tree_to_graph G (Loc 0 (Src 1)) (Loc 1 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 1 (Src 1)) (Loc 2 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 2 (Src 1)) (Loc 3 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 3 (Src 1)) (Loc 1 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 3 (Src 1)) (Loc 2 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 3 (Src 1)) (Loc 3 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 3 (Src 1)) (Loc 4 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 4 (Src 1)) (Loc 0 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 4 (Src 1)) (Loc 1 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 4 (Src 1)) (Loc 2 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 4 (Src 1)) (Loc 3 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 4 (Src 1)) (Loc 3 (Trg 1))"



value "dataflow_tree_to_graph G (Loc 0 (Src 0)) (Loc 1 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 1 (Src 0)) (Loc 2 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 2 (Src 0)) (Loc 3 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 3 (Src 0)) (Loc 4 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 4 (Src 0)) (Loc 1 (Trg 1))"
value "dataflow_tree_to_graph G (Loc 4 (Src 0)) (Loc 2 (Trg 1))"

abbreviation "compiled \<equiv> compile_dataflow (\<lambda> _. []) G"


definition "list_connections pnid pt su = 
 map (\<lambda> ((nid, p), (nid', p')). ((pnid nid, pt p),(pnid nid', pt p')))
 (filter (\<lambda> ((nid, p), (nid', p')). su (Loc nid (Src p)) (Loc nid' (Trg p')) \<noteq> []) (List.product(List.product Enum.enum Enum.enum) (List.product Enum.enum Enum.enum)))"

value "list_connections five_to_nat two_to_nat (dataflow_tree_to_graph G)"

value [GHC] "ltaken 2 (lmap (\<lambda> io. case io of VOut (nid, p) (x, t) \<Rightarrow> ((five_to_nat nid,  p), (x, t))) (trace_exec compiled))"

term DEBUG
find_consts "('a :: enum) \<Rightarrow> nat"

term to_nat

term "Abs_bit0 2"

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

abbreviation "my_op \<equiv> g4 inps1"

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


abbreviation \<open>my_sg \<equiv> init_subgraph my_summ\<close>
abbreviation "dt \<equiv> dataflow_op my_sg my_op"

definition "r = (trace_exec dt :: (_, _ \<times> _, (nat \<times> nat) \<times> nat) VIO llist)"
 
value [GHC] "ltaken 2 (lmap (\<lambda> io. case io of VOut (nid, p) (x, t) \<Rightarrow> ((five_to_nat nid, two_to_nat p), (x, t))) r)"


value [GHC] "check_prefix 100000000 [((nid2, p0), ((2, 1), 0))] dt"


(* value [GHC] "check_prefix 100000000 [((nid2, p0), ((4, 1), 1))] dt" *)

(* 
fun get_nid where
  "get_nid (Read (Inl nid) f) = Some nid"
| "get_nid (Read (Inr (nid, p)) f) = Some nid"
| "get_nid (Write op (Inr (nid, p)) (Inr x)) = Some nid"
| "get_nid (Write op (Inl nid) (Inl (Inl st))) = Some nid"
| "get_nid _ = None"

definition "is_busy sg op = (case get_nid op of None \<Rightarrow> True 
 | Some nid \<Rightarrow> 
    (\<forall> p. frontier (c_imp (pt_tr sg) (Loc nid (Trg p))) \<noteq> {}\<^sub>A \<or>
          frontier (c_imp (pt_tr sg) (Loc nid (Src p))) \<noteq> {}\<^sub>A))"

corec opt_dataflow_op where
  "opt_dataflow_op sg op = Choice (cimage (\<lambda> op. case op of
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (opt_dataflow_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None \<Rightarrow> \<oslash>)
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. opt_dataflow_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (opt_dataflow_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (opt_dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (opt_dataflow_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in opt_dataflow_op breaks contract'') (\<lambda> _. \<oslash>))
   (cfilter (\<lambda> op. not_nop sg op)
   (choices op))
   )"

abbreviation "opt_dt \<equiv> opt_dataflow_op my_sg my_op"
definition "opt_r = (trace_exec opt_dt :: (_, _ \<times> _, (nat \<times> nat) \<times> nat) VIO llist)"
value [GHC] "opt_r"



value [GHC] "check_prefix 100000000 [((nid2, p0), ((2, 1), 0))] opt_dt"
 *)
(* 
 export_code r2 in Haskell module_name Test10
 *)

term not_nop

end