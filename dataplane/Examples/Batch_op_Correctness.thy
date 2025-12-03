theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Ooo_Input_op
  Batch_op
  "../MyProduct_Instances"
  "../AntichainOrder"
   Dataplane.LList_Haskell_Setup
  Set_op
  Source_op
begin

abbreviation "t0 \<equiv> MyPair (0 :: nat) (0 :: nat)"
abbreviation "t_1_0 \<equiv> MyPair (Suc 0) (0 :: nat)"
abbreviation "t_0_1 \<equiv> MyPair (0 :: nat) (Suc 0)"
abbreviation "t_1_1 \<equiv> MyPair (Suc 0) (Suc 0)"

abbreviation "list_inps2 \<equiv> 
 [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"
abbreviation "inps2 \<equiv> llist_of list_inps2"

abbreviation init_input_state where
"init_input_state su inps \<equiv> \<lparr> 
   summar = su,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = undefined,
   ocaps = (\<lambda> _. [\<bottom>]),
   initia = False,
   nfron = False,
   en1 = Inl,
   de1 = projl,
   es = inps
   \<rparr>"
abbreviation "l1 inps \<equiv> Logic (ooo_input_op {|1|} (init_input_state default_internal_summary inps)) default_internal_summary"

abbreviation init_operator_state_ty2 where
"init_operator_state_ty2 su \<equiv> \<lparr> 
   summar = su,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = undefined,
   ocaps = (\<lambda> _. [\<bottom>]),
   initia = False,
   nfron = False,
   en1 = Inl,
   de1 = projl,
   en2 = Inr,
   de2 = projr
   \<rparr>"
abbreviation "l2 \<equiv> Logic (batch_fun_op (init_operator_state_ty2 default_internal_summary) (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)])) default_internal_summary"

abbreviation "test_dt2 \<equiv> Comp [(0, 1) \<mapsto> (0, 1)] (l1 (\<lambda> _. inps2)) l2"

abbreviation "test_op2 \<equiv> compile_dataflow test_dt2 :: (2 \<times> 1, 2 \<times> 1, _) op"

abbreviation "set_op_test \<equiv> set_op {||} {||} test_op2"


(* 
value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op1)"
 *)

find_theorems cUn name: code

value [GHC] "trace_exec set_op_test"

value "frontier {# t_1_1, t_0_1, t_1_0 #}\<^sub>z"

term DEBUG

find_theorems Max fold

abbreviation "timestamps inps \<equiv> cset_of_llist (lmap (\<lambda> ev. case ev of Data t d \<Rightarrow> t) (lfilter is_Data inps))"

abbreviation "Max_spec inps \<equiv> 
  cimage (\<lambda> t. (1 :: 1, Max (set (list_of (lmap (\<lambda> ev. case ev of Data _ d \<Rightarrow> d) (lfilter (\<lambda> ev. case ev of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps)))), t))
  (timestamps inps)"

value [GHC] "trace_exec (set_op (Max_spec inps2) {||} (\<oslash> :: (1, _, _) op))"

value [GHC] "check_prefix [VOut 1 (3, MyPair 1 0)] (set_op (Max_spec inps2) {||} (\<oslash> :: (1, _, _) op))"

value [GHC] "check_prefix [VOut (1, 1) (Inr 3, MyPair 1 0)] set_op_test"

value [GHC] "check_prefix [VOut (1, 1) (Inr 7, MyPair 0 1)] test_op2"

lemma
  "set_op {||} {||} test_op2 \<approx> set_op (cimage (\<lambda> (p, x, t). ((2, p), Inr x, t)) (Max_spec inps2)) {||} \<oslash>"
  oops


abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_fun_op os f)"

abbreviation "inp_tt_op os1 cbuf os2 f \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] cbuf (inp_op (os1\<lparr> en1 := Inl \<rparr>)) (tt_op (os2\<lparr> de1 := projl, en2 := Inr \<rparr>) f))"


definition \<open>subgraph_inv dtt cgs c = (let (su, _) = compile_dataflow_tree dtt in
 \<lparr> pt_tr = change_multiplicities su cgs c,
   edges = (\<lambda> l1. [l2 \<leftarrow> Enum.enum. \<not> is_empty_antichain (su l1 l2) \<and> is_Src (port l1) \<and> is_Trg (port l2) ]),
   summ = su,
   upfro = undefined \<rparr>)\<close>

lemma dataflow_op_inp_tt_op_wbisim_source_op_aux:
  fixes lxs :: \<open>('t :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
  and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
  and os1 :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
  and os2 :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
assumes
  buffers_inv: 
  \<open>es os1 1 = lxs\<close>
  \<open>outpu os1 1 = map (\<lambda> (d, t). (Inl d, t)) out_os1\<close>
  \<open>input os2 1 = map (\<lambda> (d, t). (Inl d, t)) inp_os2\<close>
  \<open>buf = out_os1 @ cbuf @ inp_os2\<close>
  and
  subgraph_inv:
  \<open>(a, st1) = obtain_progress os1\<close>   
  \<open>(b, st2) = obtain_progress os2\<close>
  \<open>cgs = extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2\<close>
  \<open>sg = subgraph_inv test_dt1 cgs c\<close>
  \<open>c' = pt_tr sg\<close>
  and
  c_pts_inv:
  \<open>c_pts c' (Loc 0 (Trg 1)) = {#}\<^sub>z\<close>
  \<open>c_pts c' (Loc 0 (Src 1)) = zmset_of (mset (ocaps os1 1))\<close>
  \<open>c_pts c' (Loc 1 (Trg 0)) = zmset_of (mset (map snd buf))\<close>
  \<open>c_pts c' (Loc 1 (Src 1)) = zmset_of (mset (ocaps os2 1))\<close>
  and
  c_imp_inv:
  \<open>front os2 1 \<le> frontier (c_imp c (Loc 1 (Trg 0)))\<close>

shows 
  \<open>dataflow_op sg (inp_tt_op os1 (\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (Inl d, t)) cbuf) os2 f) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. outpu os2 1 @@- lmap (\<lambda> (d, t). (Inr d, t)) (lconcat (batch_fun_spec f lxs buf caps))))\<close>

  term "ocaps os1 1"

end
