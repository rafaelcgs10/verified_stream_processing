theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Ooo_Input_op
  Batch_op
  "../MyProduct_Instances"
  "../AntichainOrder"
   Dataplane.LList_Haskell_Setup
  Source_op
  Set_op
begin

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
abbreviation init_operator_state_ty2 where
"init_operator_state_ty2 su \<equiv> \<lparr> 
   summar = su,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = undefined,
   ocaps = (\<lambda> _. []),
   initia = False,
   nfron = False,
   en1 = Inl,
   de1 = projl,
   en2 = Inr,
   de2 = projr
   \<rparr>"

abbreviation "l1 ip_state \<equiv> ((Logic (ooo_input_op {|1 :: 1|} ip_state) default_internal_summary) :: ('a, _, (_, 't) shared_state + (1 \<Rightarrow> 't antichain), 'c \<times> 't, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) dataflow_tree)"
abbreviation "l2 os2 f \<equiv> Logic (batch_op os2 f) default_internal_summary"
abbreviation "G f ip_state os2 cbuf \<equiv> Comp [(0 :: 2, 1) \<mapsto> (0, 1)] cbuf (l1 (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state)) (l2 (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2) f)"

abbreviation "test_op \<equiv> compile_dataflow (G (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)]) (init_input_state default_internal_summary (\<lambda> _. inps_test)) (init_operator_state_ty2 default_internal_summary) (\<lambda> _. []) ) :: (2 \<times> 1, 2 \<times> 1, _) op"

value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op)"
value [GHC] "check_prefix 100 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 100 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 100 [((1, 1), (Inr 3, MyPair 1 0)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1))] test_op"

section \<open>Generalized Correctness\<close>

abbreviation "coll inps t \<equiv> list_of (lmap (\<lambda> e. case e of Data t d \<Rightarrow> d) (lfilter (\<lambda> e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps))"

abbreviation "ts inps \<equiv> cimage (\<lambda> e. case e of Data t d \<Rightarrow> t) (cfilter is_Data (cset_of_llist inps))"

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_op os f)"

abbreviation "G_op f ip_state os2 cbuf \<equiv>
   dataflow_tree_to_operator (G f (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state) (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2) cbuf)"

(* abbreviation "G_op os1 cbuf os2 f \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] cbuf (inp_op (os1\<lparr> en1 := Inl \<rparr>)) (tt_op (os2\<lparr> de1 := projl, en2 := Inr \<rparr>) f))"
 *)
definition "c_pts_inv c caps = (\<forall> l. c_pts c l = caps l)"
definition "Src_caps_inv caps oss = (\<forall> nid p. caps (Loc nid (Src p)) = zmset_of (mset (ocaps (oss nid) p)))"
definition "Trg_caps_inv caps bufs = (\<forall> nid p. caps (Loc nid (Trg p)) = zmset_of (mset (map snd (bufs nid p))))"
definition "extract_prog eds oss = concat (map (\<lambda> nid. extract_progress nid eds (snd (obtain_progress (oss nid)))) Enum.enum)"
definition "front_inv oss c = (\<forall> nid p. front (oss nid) p \<le> frontier (c_imp c (Loc nid (Trg p))))"
definition "imp_front_inv su c = (\<forall> l. frontier (c_imp c l) \<le> dataflow_topology.implied_frontier_alt su (+) c l)"
definition "buf_imp_front_inv su c T nid p = (\<forall> t \<in> T. frontier_less_equal (dataflow_topology.implied_frontier_alt su (+) c (Loc nid (Trg p))) t)"
definition "changes_above_impl_inv su c cgs = (\<forall>(l, t, d)\<in>set cgs. frontier_less_equal (dataflow_topology.implied_frontier_alt su (+) c l) t)"
definition "changes_non_zero_inv cgs = (\<forall>d\<in>snd ` snd ` set cgs. d \<noteq> 0)"
definition "propagation_inv su c = 
  (dataflow_topology.inv_imps_work_sum su (-+-) c \<and>
   dataflow_topology.inv_implications_nonneg c \<and>
   dataflow_topology.inv_imp_plus_work_nonneg c)"

lemma correctness_gen:
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
    and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
    and oss :: \<open>2 \<Rightarrow> (1, 'd1 + 'd2, 't) operator_state\<close>
    and ip_state :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
    and bt_state :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
  assumes
    SUBGRAPH_INV:
    \<open>c = pt_tr sg\<close>
    \<open>summ sg = dataflow_tree_to_graph (G f ip_state bt_state gbuf)\<close>
    \<open>edges sg = (\<lambda> l. if l = Loc 0 (Src 1) then [Loc 1 (Trg 1)] else [])\<close>
    and
    OP_STATE_INV: 
    \<open>ip_state = operator_state.extend (oss 1) \<lparr>en1 = Inl, de1 = projl, es = inps\<rparr>\<close>
    \<open>bt_state = operator_state.extend (oss 2) \<lparr>en1 = Inl, de1 = projl, en2 = Inr, de2 = projr\<rparr>\<close>
    and
    BUFS_INV: 
    \<open>outpu (oss 1) 1 = map (\<lambda> (d, t). (Inl d, t)) out_os1\<close>
    \<open>input (oss 2) 1 = map (\<lambda> (d, t). (Inl d, t)) inp_os2\<close>
    \<open>buf = out_os1 @ cbuf @ inp_os2\<close>
    \<open>bufs = (\<lambda> nid p. if nid = 1 \<and> p = 0 then buf else [])\<close>
    \<open>gbuf = (\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (Inl d, t)) cbuf)\<close>
    and
    C_PTS_INV:
    \<open>Src_caps_inv caps oss\<close>
    \<open>Trg_caps_inv caps bufs\<close>
    \<open>cgs = extract_prog (edges sg) oss\<close>
    \<open>c' = change_multiplicities my_summ cgs c\<close>
    \<open>c_pts_inv c' caps\<close>
    \<open>buf_imp_front_inv my_summ c (snd ` set buf) 1 0\<close>
    and
    C_IMP_INV:
    \<open>front_inv oss c\<close>
    \<open>imp_front_inv my_summ c\<close>
    and
    CGS_INV:
    \<open>changes_above_impl_inv my_summ c cgs\<close>
    \<open>changes_non_zero_inv cgs\<close>
    and
    PROP_INV:
    \<open>propagation_inv my_summ c\<close>
  shows 
    \<open>set_op S D (dataflow_op sg (G_op f ip_state bt_state gbuf)) \<approx> set_spec_op (cUn S S') D\<close>
  oops




section \<open>Correctness\<close>

(* abbreviation "G inps f \<equiv> compile_dataflow (Comp [(0, 1) \<mapsto> (0, 1)] (l1 inps) (l2 f))"

lemma
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
   and f :: \<open>'d1 list \<Rightarrow> 'd2 list\<close>
   and S :: \<open>((2 \<times> 1) \<times> ('d1 + 'd2) \<times> 't) cset\<close>
 assumes \<open>S = cUnion (cimage (\<lambda> t. (cset_of_llist o llist_of) (map (\<lambda> x. ((2, 1), (Inr x, t))) (f (coll (inps 1) t)))) (ts (inps 1)))\<close>
  shows \<open>set_op {||} {||} (G inps f) \<approx> set_spec_op S {||}\<close>
  oops
 *)

end
