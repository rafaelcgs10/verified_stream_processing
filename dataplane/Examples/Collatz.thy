theory Collatz

imports
  Ooo_Input_op
  "../Lib/LList_Haskell_Setup"
  Source_op
  Tmap_op
  Concat_op
  Branch_op
  Increment_op
  "../Timely/Dataflow_Op"
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


abbreviation "collatz_logic os \<equiv> tmap_op 0 0 os (\<lambda> (n, x). if even x then (n, x div 2) else (n, 3 * x + 1))"
definition "inps = (\<lambda> p. llist_of
  [Data (0 :: nat) (12 :: nat, 12 :: nat), Data 0 (2, 2), Data 0 (7, 7),
   Data 0 (15, 15), Data 0 (6, 6), Data 0 (9, 9), Data 0 (18, 18),
   Data 0 (11, 11), Drop 0])"
definition "input_dt = Logic (ooo_input_op {|0 :: 2|} (init_input_state inps)) default_internal_summary"
definition "concat_dt = Logic (concat_op {|0, 1|} 0 init_operator_state) default_internal_summary"
definition "collatz_dt = Logic (collatz_logic init_operator_state_ty2) default_internal_summary"
definition "branch_dt = Logic (branch_op 0 0 1 (\<lambda> (x, t). snd x \<le> 1 \<or> t > 100) init_operator_state) default_internal_summary"
definition "increment_dt = Logic (increment_op 1 1 1 init_operator_state) (\<lambda> p1 p2. if 1 = p2 then [1] else [])"

abbreviation dt :: "(5, 2, (2, nat) shared_state + (2 \<Rightarrow> nat antichain), (nat \<times> nat) \<times> nat, nat) dataflow_tree" where
  "dt \<equiv>
    input_dt \<sqdot>\<^bsub>0\<^esub>
      (concat_dt \<sqdot>\<^bsub>0\<^esub> collatz_dt \<sqdot>\<^bsub>0\<^esub> branch_dt \<sqdot>\<^bsub>1\<^esub> increment_dt) \<hookleftarrow>\<^bsub>1\<^esub>"

value "list_connections (dataflow_tree_to_graph dt)"

abbreviation "compiled \<equiv> compile_dataflow (\<lambda> _. []) dt"
value [GHC] "ltaken 8 (lmap show_Outs (trace_exec compiled))"

end
