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
no_notation shiftr  (infixl \<open>>>\<close> 55)

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
abbreviation "G f ip_state os2 \<equiv> Comp [(0 :: 2, 1) \<mapsto> (0, 1)] (l1 (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state)) (l2 (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2) f)"

abbreviation "test_op \<equiv> compile_dataflow (\<lambda> _. []) (G (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)]) (init_input_state default_internal_summary (\<lambda> _. inps_test)) (init_operator_state_ty2 default_internal_summary) )"

value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op)"
value [GHC] "check_prefix 100 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 100 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 100 [((1, 1), (Inr 3, MyPair 1 0)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1))] test_op"

section \<open>Generalized Correctness\<close>

abbreviation "coll inps t \<equiv> list_of (lmap (\<lambda> e. case e of Data t d \<Rightarrow> d) (lfilter (\<lambda> e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps))"

abbreviation "ts inps \<equiv> cimage (\<lambda> e. case e of Data t d \<Rightarrow> t) (cfilter is_Data (cset_of_llist inps))"

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_op os f)"

abbreviation "G_op f ip_state os2 chns \<equiv>
   dataflow_tree_to_operator chns (G f (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state) (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2))"

definition "c_pts_inv c caps = (\<forall> l. c_pts c l = caps l)"
definition "Src_caps_inv caps oss = (\<forall> nid p. caps (Loc nid (Src p)) = zmset_of (mset (ocaps (oss nid) p)))"
definition "Trg_caps_inv caps bufs = (\<forall> nid p. caps (Loc nid (Trg p)) = zmset_of (mset (map snd (bufs nid p))))"
definition "extract_prog eds oss = concat (map (\<lambda> nid. extract_progress nid eds (snd (obtain_progress (oss nid)))) Enum.enum)"
definition "front_inv oss c = (\<forall> nid p. front (oss nid) p \<le> frontier (c_imp c (Loc nid (Trg p))))"
definition "imp_front_inv su c = (\<forall> l. frontier (c_imp c l) \<le> ifrontier su (+) c l)"
definition "chnls_imp_front_inv su c chns = (\<forall> nid p. \<forall> t \<in> snd ` set (chns (nid, p)). frontier_less_equal (ifrontier su (+) c (Loc nid (Trg p))) t)"

definition "propagation_inv su c = 
  (dataflow_topology.inv_imps_work_sum su (-+-) c \<and>
   dataflow_topology.inv_implications_nonneg c \<and>
   dataflow_topology.inv_imp_plus_work_nonneg c)"

definition "changes_non_zero_inv cgs = (\<forall>d\<in>snd ` snd ` set cgs. d \<noteq> 0)"
definition "changes_above_impl_inv su c cgs = 
  ((\<forall>(l, t, d)\<in>set cgs. frontier_less_equal (ifrontier su (+) c l) t) \<and>
   (\<forall> l' \<in> fst ` set cgs. let (cgs_l, cgs') = partition (\<lambda> (l, t, d). l' = l) cgs in
                         (\<forall> (l, t, d) \<in> set cgs'. frontier_less_equal (ifrontier su (+) (change_multiplicities su cgs_l c) l) t)))"

abbreviation "su_test a b \<equiv> dataflow_tree_to_graph (
    Comp [(0, 0) \<mapsto> (1, 1), (1, 0) \<mapsto> (0, 0)] 
    (Comp [(0, 0) \<mapsto> (0, 0)] (Logic (\<oslash> :: (_, _, unit + unit) op) (\<lambda> _ _. [0 :: nat])) (Logic \<oslash> (\<lambda> _ _. [0 :: nat])))
    (Comp [(0 :: 4, 0 :: 2) \<mapsto> (0, 0)] (Logic \<oslash> (\<lambda> _ _. [0 :: nat])) (Logic \<oslash> (\<lambda> _ _. [0 :: nat])))
    ) a b"


definition Src_from_Trg where
  "Src_from_Trg su nid p = Set.the_elem {(nid', p'). su (Loc nid' (Src p')) (Loc nid (Trg p)) \<noteq> {}\<^sub>A}"

lemma correctness_gen:
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
    and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
    and oss :: \<open>2 \<Rightarrow> (1, 'd1 + 'd2, 't) operator_state\<close>
    and ip_state :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
    and bt_state :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
    and chns :: \<open>2 \<times> 1 \<Rightarrow> (('d1 + 'd2) \<times> 't) list\<close>
    and sg :: \<open>(2, 1, 't) subgraph\<close>
  assumes
    SUBGRAPH_INV:
    \<open>c = pt_tr sg\<close>
    \<open>summ sg = dataflow_tree_to_graph (G f ip_state bt_state)\<close>
    \<open>edges sg = graph_to_edges (summ sg)\<close>
    and
    OP_STATE_INV: 
    \<open>ip_state = operator_state.extend (oss 0) \<lparr>en1 = Inl, de1 = projl, es = inps\<rparr>\<close>
    \<open>bt_state = operator_state.extend (oss 1) \<lparr>en1 = Inl, de1 = projl, en2 = Inr, de2 = projr\<rparr>\<close>
    and
    BUFS_INV: 
    \<open>outchns = (\<lambda> (nid, p). let (nid', p') = Src_from_Trg (summ sg) nid p in outpu (oss nid') p')\<close>
    \<open>inpchns = (\<lambda> (nid, p). outpu (oss nid) p)\<close>
    \<open>chns = outchns >> cbufs >> inpchns\<close>
    \<open>\<forall> x \<in> fst ` set (chns (0, 0)). isl x\<close>
    and
    C_PTS_INV:
    \<open>Src_caps_inv caps oss\<close>
    \<open>Trg_caps_inv caps bufs\<close>
    \<open>cgs = extract_prog (edges sg) oss\<close>
    \<open>c' = change_multiplicities (summ sg) cgs c\<close>
    \<open>c_pts_inv c' caps\<close>
    and
    C_IMP_INV:
    \<open>front_inv oss c\<close>
    \<open>imp_front_inv (summ sg) c\<close>
    \<open>chnls_imp_front_inv (summ sg) c chns\<close>
    and
    CGS_INV:
    \<open>changes_above_impl_inv (summ sg) c cgs\<close>
    \<open>changes_non_zero_inv cgs\<close>
    and
    PROP_INV:
    \<open>propagation_inv (summ sg) c\<close>
    and
    INP_STREAM_INV:
    \<open>timely_input_stream (inps 0) C\<close>
    \<open>zmset_of C = caps (Loc 0 (Src 0))\<close>
    and SPEC_INV:
    \<open>S = cUnion (cimage 
      (\<lambda> t. (cset_of_llist o llist_of) (map (\<lambda> x. ((2, 1), (Inr x, t))) (f (coll ((map (\<lambda> (x, t). Data t (projl x)) (chns (0, 0))) @@- (inps 1)) t))))
      (cUn (ts (inps 1)) (cset_of_llist (llist_of (map snd (chns (0, 0)))))))\<close>
  shows 
    \<open>set_op S D (dataflow_op sg (G_op f ip_state bt_state cbufs)) \<approx> set_spec_op (cUn S S') D\<close>


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
