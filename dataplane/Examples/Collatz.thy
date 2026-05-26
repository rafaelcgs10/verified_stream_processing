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
abbreviation "inps0 \<equiv> (\<lambda> p. llist_of []) :: 'a \<Rightarrow> (nat, nat \<times> nat) event llist"
abbreviation "inps1 \<equiv> \<lambda> p. llist_of [Data (0 :: nat) (12 :: nat, 12 :: nat), Data 0 (2, 2)]"
abbreviation "l1 \<equiv> Logic (ooo_input_op {|0 :: 2|} (init_input_state inps1)) default_internal_summary"
abbreviation "l2 \<equiv> Logic (concat_op {|0, 1|} 0 init_operator_state) default_internal_summary"
abbreviation "l3 \<equiv> Logic (collatz_op init_operator_state_ty2) default_internal_summary"
abbreviation "l4 \<equiv> Logic (branch_op 0 0 1 (\<lambda> (x, t). snd x \<le> 1 \<or> t > 100) init_operator_state) default_internal_summary"
abbreviation "l5 \<equiv> Logic (increment_op 1 1 1 init_operator_state) (\<lambda> p1 p2. if 1 = p2 then [1] else [])"

abbreviation G :: "(5, 2, (2, nat) shared_state + (2 \<Rightarrow> nat antichain), (nat \<times> nat) \<times> nat, nat) dataflow_tree" where
  "G \<equiv> Comp [(0, 0) \<mapsto> (0, 0)] l1 (Loop [(3, 1) \<mapsto> (0, 1)] (Comp [(2, 1) \<mapsto> (0, 1)] (Comp [(1, 0) \<mapsto> (0, 0)] (Comp [(0, 0) \<mapsto> (0, 0)] l2 l3) l4) l5))"

abbreviation "compiled \<equiv> compile_dataflow (\<lambda> _. []) G"

value [GHC] "ltaken 2 (lmap show_Outs (trace_exec compiled))"

(* value [GHC] "check_prefix 100000000 [((nid2, 0), ((4, 1), 1))] dt" *)

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



value [GHC] "check_prefix 100000000 [((nid2, 0), ((2, 1), 0))] opt_dt"
 *)
(* 
 export_code r2 in Haskell module_name Test10
 *)

term not_nop

end
