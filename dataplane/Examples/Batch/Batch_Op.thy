theory Batch_Op

imports
  "../../Common_Operators/Ooo_Input_Op"
  "../../Timely/Dataflow_Op"
  "../../Timely/Dataflow_Opt_Op"
  "../../Lib/LList_Haskell_Setup"
begin

definition batch_op_logic where
  \<open>batch_op_logic ps f g os caps =
  (let caps' = g caps in if \<exists>p. p \<in> set ps \<and> caps' p \<noteq> [] then
    let batches = (\<lambda>p t. map (de1 os \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (caps' p)) (input os p)));
        ts = (\<lambda>p. remdups (map snd (filter (\<lambda>(d, t). t \<in> set (caps' p)) (input os p))));
        os' = os\<lparr>input := (\<lambda>p. filter (\<lambda>(d, t). t \<notin> set (caps' p)) (input os p))\<rparr>;
        outs = concat (map (\<lambda>p. concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t p)) (f (batches p t))) (ts p))) ps);
        drops = concat (map (\<lambda>p. map (\<lambda>t. Cap t p) (caps' p)) ps)
    in {|trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops))
      (drop_caps (produces os' (map (\<lambda>(d, cap). (en2 os' d, cap)) outs)) drops)|}
  else trace (STR ''No capabilities'') {||})\<close>

definition batch_op where
  \<open>batch_op ps f g os = notifier_op (cset_from_list ps) (cset_from_list ps) os (batch_op_logic ps f g)\<close>

lemma nop_leaf_batch_op:
  "nop_leaf None (batch_op ps f g os)"
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

abbreviation "input_dt inp_os \<equiv> ((Logic (ooo_input_op {|1 :: 1|} inp_os) default_internal_summary) :: ('a, _, (_, 't) shared_state + (1 \<Rightarrow> 't antichain), 'c \<times> 't, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) dataflow_tree)"

abbreviation "batch_dt bat_os f \<equiv> Logic (batch_op [1 :: 1] f id bat_os) default_internal_summary"

abbreviation "G_dt f inp_os bat_os \<equiv>
  (input_dt (inp_os :: (1, 'd1 + 'd2, 'd1, _) input_state) :: (2, _, _, _, _) dataflow_tree)
    \<sqdot>\<^bsub>1\<^esub> batch_dt (bat_os :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2) f"

abbreviation "G_op f inp_os bat_os chns \<equiv> dataflow_tree_to_operator chns (G_dt f inp_os bat_os)"

abbreviation "batch_tree inps f \<equiv>
  G_dt f (init_input_state default_internal_summary inps) (init_operator_state_ty2 default_internal_summary)"

abbreviation "compiled_batch_op inps f \<equiv> compile_dataflow (\<lambda> _. []) (batch_tree inps f)"

section \<open>The Batch Program Example\<close>

text \<open>The input stream and program drawn in the thesis figure about the
  two possible output orders.\<close>

abbreviation "list_inps \<equiv>
  [Mint (MyPair (1 :: nat) (0 :: nat)), Mint (MyPair 0 1), Drop (MyPair 0 0),
   Data (MyPair 1 0) (10 :: nat), Data (MyPair 0 1) 7,
   Drop (MyPair 0 1), Drop (MyPair 1 0)]"

abbreviation "inps \<equiv> (\<lambda> p :: 1. llist_of list_inps)"

abbreviation "batch_max \<equiv> (\<lambda> b. if b = [] then [] else [Max (set b)])"

abbreviation "prog \<equiv> compile_dataflow_opt (\<lambda> p. [])
  ((input_dt (init_input_state default_internal_summary inps) :: (2, _, _, _, _) dataflow_tree)
     \<sqdot>\<^bsub>1\<^esub> batch_dt (init_operator_state_ty2 default_internal_summary) batch_max)"

end