theory Batch_op

imports
  Ooo_Input_op
  "../Timely/Dataflow_Op"
  "../Lib/LList_Haskell_Setup"
begin

definition batch_op_logic where
  "batch_op_logic ips ops comb os logic = notifier_op ips ops os 
   (\<lambda> os compl_caps.
    let comb_caps = comb compl_caps in
    if (\<forall> p. comb_caps p = []) then trace (STR ''No capabilities'') {||} else
    let compl_batches = (\<lambda> p t. map (de1 os o fst) (filter (\<lambda> (d, t'). t' = t \<and> t \<in> set (comb_caps p)) (input os p))) in
    let ts = (\<lambda> p. remdups (map snd (filter (\<lambda> (d, t). t \<in> set (comb_caps p)) (input os p)))) in
    let os = os\<lparr> input := (\<lambda> p. filter (\<lambda> (d, t). t \<notin> set (comb_caps p)) (input os p)) \<rparr> in
    let outs_drops = logic compl_batches ts comb_caps in
    cimage (\<lambda> (outs, drops). 
    trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops))
    (drop_caps (produces os (map (\<lambda> (d, cap). (en2 os d, cap)) outs)) drops)) outs_drops)"


definition batch_op where
  "batch_op os f = batch_op_logic {|(1 :: 1)|} {|(1 :: 1)|} id os
   (\<lambda> compl_batches ts caps. {| (concat (map (\<lambda> t. map (\<lambda> x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda> t. Cap t 1) (caps 1)) |})"


(*
definition diff_op where
  "diff_op os = batch_op_logic {|(1 :: 2), 2|} {|1|} 
   (\<lambda> compl_caps p. if p = 1 then filter (\<lambda> t. t \<in> set (compl_caps 2)) (compl_caps 1) else filter (\<lambda> t. t \<in> set (compl_caps 1)) (compl_caps 2))
   (os\<lparr> de1 := projl, en2 := Inr \<rparr>)
   (\<lambda> compl_batches ts caps. 
   {| (map (\<lambda> t. (mset (compl_batches 1 t) - mset (compl_batches 2 t), Cap t 1)) (remdups (caps 1)),
       map (\<lambda> t. Cap t 1) (caps 1) @ map (\<lambda> t. Cap t 2) (caps 2)) |})"

definition batch_ty2_op where
  "batch_ty2_op ips ops comb os logic = notifier_op ips ops os 
   (\<lambda> os compl_caps.
    let comb_caps = comb compl_caps in
    let compl_batches = (\<lambda> p t. map (de1 os o fst) (filter (\<lambda> (d, t'). t' = t \<and> t \<in> set (comb_caps p)) (input os p))) in
    let os = os\<lparr> input := (\<lambda> p. filter (\<lambda> (d, t). t \<notin> set (comb_caps p)) (input os p)) \<rparr> in
    let outs_drops = logic compl_batches comb_caps in
    cimage (\<lambda> (outs, drops). drop_caps (produces os (map (\<lambda> (d, cap). (en2 os d, cap)) outs)) drops) outs_drops)"

 *)


section \<open>Example\<close>

abbreviation "t0 \<equiv> MyPair (0 :: nat) (0 :: nat)"
abbreviation "t_1_0 \<equiv> MyPair (Suc 0) (0 :: nat)"
abbreviation "t_0_1 \<equiv> MyPair (0 :: nat) (Suc 0)"
abbreviation "t_1_1 \<equiv> MyPair (Suc 0) (Suc 0)"

abbreviation "list_inps_test \<equiv> 
 [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"
abbreviation "inps_test \<equiv> llist_of list_inps_test"

abbreviation init_input_state where
  "init_input_state su inps \<equiv> \<lparr> 
   intsum = su,
   consu = [],
   inter = [],
   produ = [],
   input = \<lambda> _. [],
   outpu = \<lambda> _. [],
   front = \<lambda> _. antichain_from_list bots,
   ocaps = \<lambda> _. bots,
   initia = True,
   en1 = Inl,
   de1 = projl,
   is_en1 = isl,
   es = inps
   \<rparr>"

abbreviation init_operator_state_ty2 where
  "init_operator_state_ty2 su \<equiv> \<lparr> 
   intsum = su,
   consu = [],
   inter = [],
   produ = [],
   input = \<lambda> _. [],
   outpu = \<lambda> _. [],
   front = \<lambda> _. antichain_from_list bots,
   ocaps = \<lambda> _. bots,
   initia = False,
   en1 = Inl,
   de1 = projl,
   is_en1 = isl,
   en2 = Inr,
   de2 = projr,
   is_en2 = isr
   \<rparr>"

abbreviation "l1 ip_state \<equiv> ((Logic (ooo_input_op {|1 :: 1|} ip_state) default_internal_summary) :: ('a, _, (_, 't) shared_state + (1 \<Rightarrow> 't antichain), 'c \<times> 't, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) dataflow_tree)"
abbreviation "l2 os2 f \<equiv> Logic (batch_op os2 f) default_internal_summary"
abbreviation "G f ip_state os2 \<equiv> Comp [(0 :: 2, 1) \<mapsto> (0, 1)] (l1 (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state)) (l2 (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2) f)"

abbreviation "compiled_batch_op inps f \<equiv> compile_dataflow (\<lambda> _. []) (G f (init_input_state default_internal_summary inps) (init_operator_state_ty2 default_internal_summary) )"

value [GHC] "check_prefix 5500 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] (compiled_batch_op (\<lambda> _. inps_test) (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)]))"
  (* value [GHC] "check_prefix 5500 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] (compiled_batch_op (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)]))"
value [GHC] "check_prefix 5500 [((1, 1), (Inr 3, MyPair 1 0)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1))] (compiled_batch_op (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)]))"  *)

value [GHC] "ltaken 3 (lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec (compiled_batch_op (\<lambda> _. inps_test) (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)]))))"

end