theory Batch_op

imports
  "../Ooo_Input_op"
  "../../Timely/Dataflow_Op"
  "../../Timely/Dataflow_Opt_Op"
  "../../Lib/LList_Haskell_Setup"
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

lemma nop_leaf_batch_op:
  "nop_leaf None (batch_op os f)"
  unfolding batch_op_def batch_op_logic_def notifier_op_def
  by (rule nop_leaf_builder_op) simp
section \<open>The Batch Dataflow Program\<close>


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

abbreviation "input_dt ip_state \<equiv> ((Logic (ooo_input_op {|1 :: 1|} ip_state) default_internal_summary) :: ('a, _, (_, 't) shared_state + (1 \<Rightarrow> 't antichain), 'c \<times> 't, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) dataflow_tree)"
abbreviation "batch_dt os2 f \<equiv> Logic (batch_op os2 f) default_internal_summary"
abbreviation "G f ip_state os2 \<equiv>
  (input_dt (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state) :: (2, _, _, _, _) dataflow_tree)
    \<sqdot>\<^bsub>1\<^esub> batch_dt (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2) f"

abbreviation "compiled_batch_op inps f \<equiv> compile_dataflow (\<lambda> _. []) (G f (init_input_state default_internal_summary inps) (init_operator_state_ty2 default_internal_summary) )"

abbreviation "compiled_batch_op_opt inps f \<equiv>
  compile_dataflow_opt (\<lambda> _. [])
    (G f (init_input_state default_internal_summary inps)
         (init_operator_state_ty2 default_internal_summary))"

end