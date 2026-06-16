theory Label_Propagation_op_Correctness

imports
  Label_Propagation_op
  Ooo_Input_op
  Increment_op
  Set_op
  "../Correctness/General"
  "../Correctness/Outputs"
  "../Correctness/Produces"
  "../Correctness/Mints"
  "../Correctness/OCapsReorder"
  "HOL-ex.Sketch_and_Explore"
  Dataplane.Timely_Dataflow_Op
  Dataplane.Bots
  "../Correctness/Timely_Collections"
begin



declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]
declare if_cong[cong]
declare list_emb_Nil2[simp del] BULK_BENQ_right_empty[simp del] BULK_BENQ_left_empty[simp del]
  filter_True[simp del] filter_False[simp del]
declare cin.rep_eq[simp del]
declare cin.rep_eq[symmetric, simp]

no_notation shiftr (infixl \<open>>>\<close> 55)
no_syntax (ASCII) "_thenM" :: \<open>['a, 'b] \<Rightarrow> 'c\<close>  (infixl \<open>>>\<close> 54)

abbreviation \<open>initial_state_input lxs \<equiv> \<lparr>
   intsum = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda>_. []),
   outpu = (\<lambda>_. []),
   front = \<lambda> _. antichain_from_list bots,
   ocaps = (\<lambda>_. bots),
   initia = True,
   en1 = Inl,
   de1 = projl,
   is_en1 = isl,
   es = (\<lambda>_. LNil)(0 := lxs)
   \<rparr> :: (_, _, _, _) input_state\<close>

abbreviation \<open>initial_state_label_prop \<equiv> \<lparr>
   intsum = (\<lambda>p1 p2. if p1 = 0 then [0] else if p2 = 1 then [0] else []),
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda>_. []),
   outpu = (\<lambda>_. []),
   front = \<lambda> _. antichain_from_list bots,
   ocaps = (\<lambda>_. bots),
   initia = False,
   en1 = Inl,
   de1 = projl,
   is_en1 = isl,
   en2 = Inr,
   de2 = projr,
   is_en2 = isr,
   timestamps = [],
   graph = (\<lambda>_ _. []),
   vertices = (\<lambda>_. []),
   label = (\<lambda>_. id)
   \<rparr> :: (_, nat, nat, nat) label_propagation_state\<close>

abbreviation \<open>increment_summary inc \<equiv> (\<lambda>p1 p2. if p1 = p2 then [inc] else [])\<close>

abbreviation \<open>initial_state_increment inc \<equiv> \<lparr>
   intsum = increment_summary inc,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda>_. []),
   outpu = (\<lambda>_. []),
   front = \<lambda> _. antichain_from_list bots,
   ocaps = (\<lambda>_. bots),
   initia = True
   \<rparr> :: (_, _, _) operator_state\<close>

abbreviation \<open>logic_map n \<equiv> map_op (case_option (Inl n) (\<lambda>p. Inr (n, p))) (case_option (Inl n) (\<lambda>p. Inr (n, p)))\<close>
abbreviation \<open>comp_map \<equiv> map_op (case_sum id id) (case_sum id id)\<close>

abbreviation \<open>op0 state \<equiv> Logic (ooo_input_op {|0 :: 2|} state) default_internal_summary\<close>
abbreviation \<open>op1 state \<equiv> Logic (label_propagation_op state) (\<lambda>p1 p2. if p1 = 0 then [0] else if p2 = 1 then [0] else [])\<close>
abbreviation \<open>op2 state \<equiv> Logic (increment_op (1 :: 2) 1 (MyPair 0 1) state) (increment_summary (MyPair 0 1))\<close>

abbreviation G :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (3, 2, (2, (nat, nat) myprod) shared_state + (2 \<Rightarrow> (nat, nat) myprod antichain), (nat \<times> nat + nat set set) \<times> (nat, nat) myprod, (nat, nat) myprod) dataflow_tree" where
  "G inp_state label_state incr_state \<equiv> (Comp [(0, 0) \<mapsto> (0, 0)] (op0 inp_state) (Loop [(1, 1) \<mapsto> (0, 1)] (Comp [(0, 1) \<mapsto> (0, 1)] (op1 label_state) (op2 incr_state))))"

abbreviation "compiled inp \<equiv> compile_dataflow (\<lambda> _. []) (G (initial_state_input inp) initial_state_label_prop (initial_state_increment (MyPair 0 1)))"

abbreviation "G_op inp_state label_state incr_state chns \<equiv>
   dataflow_tree_to_operator chns (G inp_state label_state incr_state)"

definition "unit_test v r = (if set v = set r then v else Code.abort (STR ''Failed unit test'') (\<lambda> _. v))"

(*
abbreviation \<open>test_input1 \<equiv> llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data \<bottom> (0, 1), Data (MyPair 1 0) (3, 4), Data \<bottom> (1, 2), Data (MyPair 2 0) (4, 5)]\<close>
value "list_connections (dataflow_tree_to_graph (G (initial_state_input test_input1) initial_state_label_prop (initial_state_increment (MyPair 0 1))))"

value [GHC] "unit_test (ltaken 3 (lmap show_Outs (trace_exec (compiled test_input1))))
 [(Loc 1 (Src 0), Inr {{1, 2, 0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr {{3, 4}, {1, 2, 0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0), Inr {{4, 5, 3, 4}, {1, 2, 0, 1}}, MyPair 2 0)]"

abbreviation \<open>test_input2 \<equiv> llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data \<bottom> (1, 2), Data \<bottom> (0, 1), Data (MyPair 1 0) (3, 4), Data (MyPair 2 0) (4, 5), Mint (MyPair 3 0), Data (MyPair 3 0) (2, 3)]\<close>
value [GHC] \<open>unit_test (ltaken 4 (lmap show_Outs (trace_exec (compiled test_input2))))
[(Loc 1 (Src 0), Inr {{1, 1, 0, 2}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr {{3, 4}, {1, 1, 0, 2}}, MyPair 1 0),
  (Loc 1 (Src 0), Inr {{4, 5, 3, 4}, {1, 1, 0, 2}}, MyPair 2 0),
  (Loc 1 (Src 0),
   Inr {{4, 5, 3, 4, 2, 1, 3, 1, 0, 2}},
   MyPair 3 0)]\<close>

abbreviation \<open>test_input3 \<equiv>
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data \<bottom> (0, 1), Data (MyPair 1 0) (2, 3),
  Mint (MyPair 3 0), Data (MyPair 3 0) (1, 2), Mint (MyPair 4 0), Data (MyPair 4 0) (4, 5), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5)]\<close>
value [GHC] \<open>unit_test (ltaken 5 (lmap show_Outs (trace_exec (compiled test_input3))))
[(Loc 1 (Src 0), Inr {{0, 1}, {0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr { {2, 1, 3, 1, 0, 2}}, MyPair 3 0),
  (Loc 1 (Src 0), Inr {{2, 1, 3, 1, 0, 2}, {4, 5}}, MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {2, 3}, {0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 1, 3, 4, 0}},
   MyPair 5 0)]\<close>

abbreviation \<open>test_input4 \<equiv>
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0),Mint (MyPair 3 0),Mint (MyPair 4 0), Mint (MyPair 5 0),
   Data (MyPair 5 0) (3, 5), Data (MyPair 4 0) (4, 5), Data (MyPair 3 0) (1, 2), Data (MyPair 1 0) (2, 3), Data \<bottom> (0, 1)]\<close>
value [GHC] \<open>unit_test (ltaken 5 (lmap show_Outs (trace_exec (compiled test_input4))))
[(Loc 1 (Src 0), Inr {{0, 1}, {0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr { {2, 1, 3, 1, 0, 2}}, MyPair 3 0),
  (Loc 1 (Src 0), Inr {{2, 1, 3, 1, 0, 2}, {4, 5}}, MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {2, 3}, {0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 1, 3, 4, 0}},
   MyPair 5 0)]\<close>

abbreviation \<open>test_input5 \<equiv>
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data \<bottom> (0, 1), Drop \<bottom>, Data (MyPair 1 0) (2, 3), Drop (MyPair 1 0),
  Mint (MyPair 3 0), Drop (MyPair 2 0), Data (MyPair 3 0) (1, 2), Mint (MyPair 4 0), Drop (MyPair 3 0), Data (MyPair 4 0) (4, 5), Mint (MyPair 5 0),  Drop (MyPair 4 0), Data (MyPair 5 0) (3, 5)]\<close>
value [GHC] \<open>unit_test (ltaken 5 (lmap show_Outs (trace_exec (compiled test_input5))))
[(Loc 1 (Src 0), Inr {{0, 1}, {0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr { {2, 1, 3, 1, 0, 2}}, MyPair 3 0),
  (Loc 1 (Src 0), Inr {{2, 1, 3, 1, 0, 2}, {4, 5}}, MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {2, 3}, {0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 1, 3, 4, 0}},
   MyPair 5 0)]\<close>

abbreviation \<open>test_input6 \<equiv>
  llist_of [Mint (MyPair 1 0), Mint (MyPair 4 0), Mint (MyPair 3 0),
   Data (MyPair 3 0) (1, 2), Data (MyPair 4 0) (4, 5), Mint (MyPair 2 0),
   Data \<bottom> (0, 1), Data (MyPair 1 0) (2, 3), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5)]\<close>
value [GHC] \<open>unit_test (ltaken 5 (lmap show_Outs (trace_exec (compiled test_input6))))
[(Loc 1 (Src 0), Inr {{0, 1}, {0, 1}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr { {2, 1, 3, 1, 0, 2}}, MyPair 3 0),
  (Loc 1 (Src 0), Inr {{2, 1, 3, 1, 0, 2}, {4, 5}}, MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {2, 3}, {0, 1}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 1, 3, 4, 0}},
   MyPair 5 0)]\<close>



abbreviation \<open>test_input7 \<equiv>
  llist_of [ Data \<bottom> (0, 6), Mint (MyPair 1 0), Mint (MyPair 4 0), Mint (MyPair 3 0),
   Data (MyPair 3 0) (1, 2), Data (MyPair 4 0) (4, 5), Mint (MyPair 2 0),
   Data \<bottom> (0, 1), Data (MyPair 1 0) (2, 3), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5), Data (MyPair 5 0) (6, 5)]\<close>
value [GHC] \<open>unit_test (ltaken 5 (lmap show_Outs (trace_exec (compiled test_input7))))
[(Loc 1 (Src 0), Inr {{0, 0, 1, 6}}, MyPair 0 0),
  (Loc 1 (Src 0),
   Inr {{2, 3, 1, 2, 0, 0, 1, 6}},
   MyPair 3 0),
  (Loc 1 (Src 0),
   Inr {{4, 5}, {2, 3, 1, 2, 0, 0, 1, 6}},
   MyPair 4 0),
  (Loc 1 (Src 0), Inr {{2, 3}, {0, 0, 1, 6}}, MyPair 1 0),
  (Loc 1 (Src 0),
   Inr {{5, 2, 3, 4, 6, 1, 0}},
   MyPair 5 0)]\<close>


abbreviation \<open>test_input8 \<equiv>
  llist_of [Data \<bottom> (0, 6), Mint (MyPair 3 0), Data (MyPair 3 0) (1, 2), Data \<bottom> (0, 1)]\<close>
value [GHC] \<open>unit_test (ltaken 2 (lmap show_Outs (trace_exec (compiled test_input8))))
      [(Loc 1 (Src 0), Inr {{0, 1, 6}}, MyPair 0 0),
  (Loc 1 (Src 0), Inr {{1, 2, 0, 6}}, MyPair 3 0)]\<close>

abbreviation \<open>test_input9 \<equiv>
  llist_of [ Data \<bottom> (0, 6), Data \<bottom> (0, 1), Data (MyPair 1 0) (2, 3)]\<close>
value [GHC] "unit_test (ltaken 2 (lmap show_Outs (trace_exec (compiled test_input9))))
      [(Loc 1 (Src 0), Inr {{0, 1, 6}}, MyPair 0 0), (Loc 1 (Src 0), Inr {{2, 3}, {0, 1, 6}}, MyPair 1 0)]"
*)

definition \<open>raw_summary = (\<lambda>l1 l2. case (find (\<lambda> (l1', s, l2'). l1' = l1 \<and> l2 = l2')
  [(Loc 0 (Trg 0), [MyPair 0 0], Loc 0 (Src 0)), (Loc 0 (Trg 1), [MyPair 0 0], Loc 0 (Src 1)), (Loc 0 (Src 0), [MyPair 0 0], Loc 1 (Trg 0)), (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0)),
  (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1)), (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)), (Loc 1 (Src 1), [MyPair 0 0], Loc 2 (Trg 1)), (Loc 2 (Trg 0), [MyPair 0 1], Loc 2 (Src 0)),
  (Loc 2 (Trg 1), [MyPair 0 1], Loc 2 (Src 1)), (Loc 2 (Src 1), [MyPair 0 0], Loc 1 (Trg 1))]) of
    Some (l1', s, l2') \<Rightarrow> s :: (nat, nat) myprod list | None \<Rightarrow> [])\<close>

lemma dataflow_tree_to_graph_raw_summary[simp]:
  "dataflow_tree_to_graph (G inp_state label_state incr_state) = raw_summary"
  unfolding dataflow_tree_to_graph_def Let_def default_internal_summary_def  comp_def                                               
  apply (simp only: split: if_splits prod.splits)
  apply (intro allI impI conjI)
  subgoal for nid su
    apply (rule ext)+
    apply simp
    apply (elim conjE)
    apply (drule sym[of _ su])
    apply hypsubst_thin
    subgoal premises prems for l1 l2
      unfolding raw_summary_def
      using loc_3_2_cases[of l1] loc_3_2_cases[of l2] apply -
      by (elim disjE; simp?; code_simp)
    done
  subgoal for nid su
    apply (rule ext)+
    subgoal for l1 l2
      apply (rule FalseE)
      apply safe
      subgoal
        apply simp
        apply (elim conjE)
        apply hypsubst_thin
        unfolding weights_to_graph_fun_def
        apply code_simp
        by eval
      subgoal
        apply simp
        apply (elim conjE)
        apply hypsubst_thin
        apply code_simp
        done
      subgoal
        apply simp
        apply (elim conjE)
        apply hypsubst_thin
        apply code_simp
        done
      subgoal
        by simp
      subgoal for l1 l2
        apply simp
        apply (elim conjE)
        apply hypsubst_thin
        using loc_3_2_cases[of l1] loc_3_2_cases[of l2] apply -
        by (elim disjE; hypsubst_thin?; eval?)
      subgoal for nid' p1 p2
        apply simp
        apply (elim conjE)
        apply hypsubst_thin
        using loc_3_2_cases[of l1] loc_3_2_cases[of l2] apply -
        by (elim disjE; (simp only: incomparable_def location.sel)?; simp?)
      subgoal
        apply simp
        apply (elim conjE)
        apply hypsubst_thin
        unfolding bi_unique_def
        apply safe
        subgoal
          by (clarsimp simp only: incomparable_def location.sel op_conn.simps port.simps split: option.split if_splits; (simp split: option.split if_splits)?)
        subgoal
          by (clarsimp simp only: incomparable_def location.sel op_conn.simps port.simps split: option.split if_splits; (simp split: option.split if_splits)?)
        subgoal
          by (clarsimp simp only: incomparable_def location.sel op_conn.simps port.simps split: option.split if_splits; (simp split: option.split if_splits)?)
        subgoal
          by (clarsimp simp only: incomparable_def location.sel op_conn.simps port.simps split: option.split if_splits; (simp split: option.split if_splits)?)
        done
      done
    done
  done

lemma outputs_at_target_raw_summary:
  \<open>outputs_at_target (antichain_from_list \<circ>\<circ> raw_summary) os = (\<lambda>l.
  if l = (1, 0) then outpu (os 0) 0
  else if l = (2 :: 3, 1 :: 2) then outpu (os 1) 1
  else if l = (1, 1) then outpu (os 2) 1
  else [])\<close>
  (is \<open>?f = ?g\<close>)
proof (rule ext)
  fix l :: \<open>3 \<times> 2\<close>
  consider \<open>l = (0, 0)\<close> | \<open>l = (0, 1)\<close> | \<open>l = (1, 0)\<close> | \<open>l = (1, 1)\<close> | \<open>l = (2, 0)\<close> | \<open>l = (2, 1)\<close>
    using num3_cases num2_cases prod.exhaust by (smt (verit, ccfv_SIG))
  thus \<open>?f l = ?g l\<close>
    by cases
      (simp_all add: outputs_at_target_def raw_summary_def antichain_from_list_singleton )
qed

lemma Inr_2_1_in_ran[simp]:
  "Inr (2 :: 3, 1 :: 2) \<in> ran (case_sum (\<lambda>_. None) (\<lambda>(nid, p). case if nid = 1 \<and> p = 1 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (Inr (1 + 1 + offset, q))))"
  unfolding ran_def
  by (auto split: sum.splits if_splits)

find_consts "_ list \<Rightarrow> _ cset"

(* FIXME: move me to operator states *)
lemma produ_release_caps[simp]:
  "produ (release_caps os p) = produ os"
  unfolding release_caps_def
  by auto


(* FIXME: move me? *)
definition "label_prob_ty2_check os bufs \<equiv>
   (\<forall> p. (\<forall> x \<in> fst ` set (input os p) \<union> fst ` set (bufs p). is_en1 os x)) \<and>
   (\<forall> x \<in> fst ` set (outpu os 0). is_en2 os x) \<and> (\<forall> x \<in> fst ` set (outpu os 1). is_en1 os x)"

(* FIXME: move me to cset things *)
lemma cfilter_False:
  "\<forall> x. x |\<in>| A \<longrightarrow> \<not> P x \<Longrightarrow>
   cfilter P A = {||}"
  by auto
lemma cfilter_True:
  "\<forall> x. x |\<in>| A \<longrightarrow> P x \<Longrightarrow>
   cfilter P A = A"
  by auto

(* FIXME: move me *)
lemma MyPair_zero_zero_sum[simp]:
  "MyPair (0 :: nat) (0 :: nat) + a = a"
  by (simp add: zero_myprod_def)

lemma all_edges_add_caps[simp]:
  "all_edges (add_caps os caps) = all_edges os"
  unfolding add_caps_def all_edges_def all_vertices_def neighbors_def
  by auto

lemma ccs_insert_swap:
  "ccs (insert (v1, v2) X) = ccs (insert (v2, v1) X)"
proof -
  have rel_eq:
    "(insert (v1, v2) X \<union> (insert (v1, v2) X)\<inverse>)\<^sup>* =
     (insert (v2, v1) X \<union> (insert (v2, v1) X)\<inverse>)\<^sup>*"
    by (rule arg_cong[where f=rtrancl]) auto
  have field_eq:
    "Field (insert (v1, v2) X) = Field (insert (v2, v1) X)"
    by auto
  show ?thesis
    unfolding Wcc.is_cc_def Wcc.is_subcc_def Wcc.reachable_def Wcc.edge_vertices_def
    by (simp only: rel_eq field_eq)
qed

lemma label_propagation_correctness:
  fixes lxs :: \<open>((nat, nat) myprod, nat \<times> nat) event llist\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_input :: \<open>(2, nat \<times> nat + nat set set, nat \<times> nat, (nat, nat) myprod) input_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs chns :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
    and S SO SP D :: \<open>((3 \<times> 2) \<times> (nat \<times> nat + nat set set) \<times> (nat, nat) myprod) cset\<close>
  assumes
    subgraph_inv:
    \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close> \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and
    os_inv:
    \<open>os_input = operator_state.extend (os 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
      es = (\<lambda>_. LNil)(0 := lxs)\<rparr>\<close> \<open>input (os 0) = (\<lambda>_. [])\<close> \<open>initia (os 0)\<close>
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    \<open>ty1_check os_input (curry cbufs 0)\<close> \<open>label_prob_ty2_check os_label_prop (curry cbufs 1)\<close>
    \<open>\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and buffers_inv:
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    and dataplane_inv:
    \<open>dataplane_tracker_inv os cbufs sg\<close> (*\<open>cbufs (0, 0) = []\<close>*)
    and csets_inv:
    \<open>SP = cimage
      (\<lambda>t. ((1, 0), (Inr (ccs
        (set (icoll (map (\<lambda>(x, t'). Data t' (projl x)) (chns (1, 0)) @@- lxs) t)
        \<union> all_edges os_label_prop (myfst t))), t)))
      (cUn (cUn (ts lxs) (cset_from_list (map snd (chns (1, 0))))) ((\<lambda> t. MyPair t 0) |`| (cset_from_list (timestamps os_label_prop))))\<close>
    \<open>SO = cset_from_list (map (\<lambda>x. ((1, 0), x)) (outpu (os 1) 0))\<close>
    and input_stream_inv:
    \<open>timely_input_stream lxs (mset (ocaps (os 0) 0))\<close>
    and label_prop_inv:
    \<open>(\<forall> t. labels_cc_inv os_label_prop t)\<close>
    \<open>(\<forall> t \<in> set (timestamps os_label_prop). \<not> frontier_less_equal (exit_scope myfst (front (os 1) 0 + front (os 1) 1)) t \<longrightarrow> labels_stable (all_edges os_label_prop t) (min_label os_label_prop t))\<close>
    \<open>\<forall> t \<in> myfst ` snd ` set (input (os 1) 0). frontier_less_equal (exit_scope myfst (front (os 1) 1)) t\<close>
    \<open>\<forall> t. t \<in> set (ocaps (os 1) 0) \<longrightarrow> myfst t |\<in>| cset_from_list T\<close>
    \<open>\<forall> t \<in> set (ocaps (os 1) 0) \<union> snd ` set (input (os 1) 0) \<union> snd ` set (outpu (os 0) 0) \<union> time ` lset lxs. mysnd t = 0\<close>
    \<open>label_prop_upd_inv os_label_prop\<close>
    \<open>input_ocaps_inv (os 1)\<close>
  shows \<open>set_op S D (dataflow_op sg (G_op os_input os_label_prop (os 2) cbufs))
         \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms
proof (coinduction arbitrary: S SO SP D lxs os os_input os_label_prop cbufs chns sg T G V L
    rule: weakBisimWeakUptoBisimCong)
  case SIM1
  thm SIM1(3,4,5,6,7,8,9)
  note subgraph_inv = SIM1(1,2)
    and os_inv = SIM1(3,4,5,6,7,8,9)
    and buffers_inv = SIM1(10)
    and dataplane_inv = SIM1(11)
    and csets_inv = SIM1(12,13)
    and input_stream_inv = SIM1(14)
    and label_prop_inv = SIM1(15,16,17,18,19,20,21)
  have D: \<open>dataflow_topology (summ sg) (-+-)\<close> 
    unfolding subgraph_inv comp_def
    apply (subst dataflow_tree_to_graph_raw_summary[symmetric])
    using dataflow_topology_from_tree.dataflow_topology_axioms[unfolded comp_def]
    apply auto
    done
  also have G: "graph_summar_nt (summ sg) (subgraph.nxt sg) os"
    apply -
    apply (rule graph_summar_nt[simplified, OF _ subgraph_inv(1)])
      apply (rule sym)
      apply (rule dataflow_tree_to_graph_raw_summary)
    using os_inv(7) apply assumption
    using subgraph_inv(2) apply assumption
    done
  show ?case (is \<open>wsim ((~) OO \<U> ?R OO (\<approx>)) _ _\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    show ?thesis
      using [[goals_limit=16]]
      unfolding R_def[symmetric]
      unfolding wsim_def dataflow_tree_to_operator_def  ooo_input_op_def label_propagation_op_def increment_op_def
      apply simp
      apply (intro allI impI)
      apply (repeat_new \<open>erule conjE step_dataflow_op_elim step_set_op_elim step_map_op_elim
  step_comp_op_elim step_loop_op_elim step_builder_op_elim; simp?; hypsubst_thin?\<close>;
          auto 0 0 split: if_splits option.splits dest!: num2_neq simp flip: ooo_input_op_def label_propagation_op_def increment_op_def; hypsubst_thin?)
      subgoal
        apply (intro exI conjI relcomppI)
           apply (rule step_set_spec_op_intro_Out)
              apply (rule refl)
             apply simp
            apply assumption
           apply (rule refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def)
        apply (intro exI conjI)
        using SIM1 by (simp_all add: dataflow_tree_to_operator_def)
      subgoal sorry
      subgoal sorry
      subgoal sorry
      subgoal sorry
      subgoal sorry
      subgoal for os'
        unfolding label_propagation_op_logic_def trace_simp
        apply clarsimp
        apply (elim disjE)
          prefer 3
        subgoal
          apply (simp split: if_splits prod.splits)
          apply hypsubst_thin
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ S])
          apply (rule exI[of _ "Pair (1, 0) |`|
             cset_from_list
              (outpu
                ((os(1 := drop_caps
                           (produces (os 1)
                             (label_prop_output_batch os_label_prop
                               (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t))
                                 (ocaps os_label_prop 0))))
                           (map (\<lambda>t. Cap t 0)
                             (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)) (ocaps os_label_prop 0)))))
                  1)
                0)"])
          apply (rule exI[of _ SP])
          apply (rule exI[of _ D])
          apply (rule exI[of _ lxs])
          apply (rule exI[of _ "os(1 := drop_caps
                       (produces (os 1)
                         (label_prop_output_batch os_label_prop
                           (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)) (ocaps os_label_prop 0))))
                       (map (\<lambda>t. Cap t 0) (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)) (ocaps os_label_prop 0))))"])
          apply (rule exI[of _ "drop_caps
                       (produces os_label_prop
                         (label_prop_output_batch os_label_prop
                           (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)) (ocaps os_label_prop 0))))
                       (map (\<lambda>t. Cap t 0) (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)) (ocaps os_label_prop 0)))"])
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ chns])
          apply (rule exI[of _ sg])
          apply (intro conjI)
          subgoal
            by (simp add: dataflow_tree_to_operator_def os_inv(1))
          subgoal premises aux
            apply (rule arg_cong2[where f=set_spec_op])
             apply (simp_all add: subgraph_inv(1) buffers_inv csets_inv(1,2) outputs_at_target_raw_summary BULK_BENQ_def flip: list_diff_append map_append filter_append)
            apply (simp only: cUn_assoc)
            apply (rule arg_cong2[where f=cUn])
             apply simp
            apply (subst cset_eq_iff)
            apply (intro allI iffI)
            subgoal for x
              apply (cases x)
              subgoal for p d t
                apply hypsubst_thin
                apply (subst (asm) icoll_lshift)
                subgoal
                  using input_stream_inv timely_input_stream_expires_le 
                  by auto
                subgoal
                  apply (subst icoll_lshift)
                  subgoal
                    using input_stream_inv timely_input_stream_expires_le 
                    by auto
                  subgoal
                    subgoal
                      apply (clarsimp del: disjCI simp add: inputs_at_target_def cUn_assoc cimage_cUn)
                      apply (elim disjE; simp?)
                      done
                    done
                  done
                done
              done
            subgoal for x
              apply (cases x)
              subgoal for p d t
                apply hypsubst_thin
                apply (subst (asm) icoll_lshift)
                subgoal
                  using input_stream_inv timely_input_stream_expires_le 
                  by auto
                subgoal
                  apply (subst icoll_lshift)
                  subgoal
                    using input_stream_inv timely_input_stream_expires_le 
                    by auto
                  subgoal
                    apply (clarsimp del: disjCI simp add: label_prop_output_batch_def cimage_iff os_inv(4) operator_state.defs inputs_at_target_def cUn_assoc cimage_cUn)
                    apply (elim disjE; (clarsimp del: disjCI simp add: cimage_iff)?; hypsubst_thin?)
                    subgoal for t'
                      apply (rule disjI2)
                      apply (rule disjI2)
                      apply (rule disjI2)
                      apply (rule disjI2)
                      apply (rule disjI2)
                      unfolding release_caps_def drop_caps_def
                      apply (subgoal_tac "myfst t' |\<in>| cset_from_list T ")
                      subgoal
                        apply (rule cBexI[rotated])
                         apply assumption
                        apply simp
                        apply (subgoal_tac "filter (\<lambda>y. y \<le> myfst t') T \<noteq> []")
                        subgoal
                          apply (subgoal_tac "icoll (llist_of (map (\<lambda>(x, t'). Data t' (projl x)) (input (os 1) 0) @ map (\<lambda>(x, t'). Data t' (projl x)) (cbufs (1, 0)) @ map (\<lambda>(x, t'). Data t' (projl x)) (outpu (os 0) 0))) (MyPair (myfst t') 0) = []")
                          subgoal
                            apply (subgoal_tac "icoll lxs (MyPair (myfst t') 0) = []")
                            subgoal
                              apply simp
                              apply (rule components_from_labels_correct)
                              subgoal
                                using label_prop_inv(1)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of "myfst t'"] 
                                  labels_cc_inv_imp_labels_inv
                                by auto
                              subgoal
                                using label_prop_inv(2)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of "myfst t'"] 
                                by auto
                              done
                            subgoal
                              apply (subgoal_tac "\<forall>x. x \<in> lset lxs \<longrightarrow> is_Data x \<longrightarrow> frontier_less_equal (front (os 1) 0) (event.time x)")
                              subgoal
                                apply (drule frontier_less_equal_exit_scope)
                                apply (drule not_frontier_less_equal_sum)
                                apply clarsimp
                                unfolding icoll_def
                                apply simp
                                apply (subst lfilter_False)
                                 apply simp_all
                                apply (clarsimp split: event.splits)
                                apply (metis (no_types, opaque_lifting) MyPair_mono dataflow_topology_from_tree.zero_le dual_order.eq_iff event.discI(1) event.sel(1) frontier_less_equal_trans myprod.exhaust myprod.sel(1))
                                done
                              subgoal
                                apply safe
                                subgoal for x
                                  apply (drule timely_input_stream_frontier_less_equal[OF input_stream_inv, rule_format, of x])
                                   apply assumption
                                  using dataplane_inv[unfolded dataplane_tracker_inv_def, simplified, rule_format] apply -
                                  apply clarsimp
                                  unfolding front_inv_def imp_front_inv_def
                                  apply (drule spec[of _ 1])
                                  apply (drule spec[of _ 0])
                                  apply (drule spec[of _ "Loc 1 (Trg 0)"])
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule order.trans)
                                    apply assumption
                                   apply assumption
                                  subgoal for caps
                                    unfolding Src_caps_inv_def
                                    apply (drule spec[of _ 0])
                                    apply (drule spec[of _ 0])
                                    unfolding c_pts_inv_def
                                    apply (drule spec[of _ "Loc 0 (Src 0)"])
                                    apply simp
                                    apply (rule frontier_less_equal_ifrontier_from_Src[where p=0 and s=0 and nid=0 and os=os and nt="subgraph.nxt sg", simplified, OF D])
                                    subgoal
                                      apply (drule sym[of _ "to_zmset (ocaps (os 0) 0)"])
                                      unfolding extract_prog_def
                                      apply simp
                                      apply (simp add:  c_pts_change_multiplicities SIM1(1,2) comp_def  zmset_filter_extract_progress_Src_consumes_diff)
                                      done
                                    subgoal premises aux
                                      apply (simp add: subgraph_inv)
                                      apply (rule path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF]])
                                      using D[unfolded subgraph_inv] apply assumption
                                      apply (subst raw_summary_def)
                                      apply simp
                                      apply code_simp
                                      done
                                    apply assumption
                                    done
                                  done
                                done
                              done
                            done
                          subgoal
                            apply (subgoal_tac "\<forall> t \<in> snd ` set ((outputs_at_target (summ sg) os >> cbufs) (1, 0)). frontier_less_equal (front (os 1) 0) t")
                             defer
                            subgoal
                              apply safe
                              subgoal for _ a t
                                apply simp
                                using dataplane_inv[unfolded dataplane_tracker_inv_def, simplified] apply -
                                apply safe
                                unfolding front_inv_def imp_front_inv_def
                                apply (drule spec[of _ 1])
                                apply (drule spec[of _ 0])
                                apply (drule spec[of _ "Loc 1 (Trg 0)"])
                                unfolding chnls_imp_front_inv_def
                                apply (drule spec[of _ 1])
                                apply (drule spec[of _ 0])
                                apply (drule bspec[of _ _ t])
                                subgoal 
                                  by blast
                                apply (drule frontier_less_equal_le_trans)
                                 apply (rule order.trans[rotated])
                                  apply assumption+
                                done
                              done
                            subgoal
                              apply (simp add: icoll_append)
                              apply (intro conjI)
                              subgoal
                                (* issue: things can still be in the input buffer, but not yet processed, so the frontier advances without processing the new edge?
                                   maybe not because the loop capabilities are still on hold *)
                                using label_prop_inv(3) apply -
                                subgoal
                                  unfolding icoll_def
                                  apply (subst lfilter_False)
                                  subgoal
                                    apply clarsimp
                                    apply (drule bspec, assumption)
                                    apply simp
                                    subgoal for a b
                                      apply (cases b; cases t'; simp; hypsubst_thin?)
                                      subgoal for t1 t2 t3
                                        apply (subgoal_tac "\<not> frontier_less_equal (exit_scope myfst (front (os 1) 1)) t2")
                                        subgoal
                                          using frontier_less_equal_trans by blast
                                        subgoal
                                          using exit_scope_plus_distrib
                                          by (metis not_frontier_less_equal_sum)
                                        done
                                      done
                                    done
                                  subgoal
                                    by simp
                                  done
                                done
                              subgoal
                                apply (drule frontier_less_equal_exit_scope)
                                apply (drule not_frontier_less_equal_sum)
                                apply clarsimp
                                unfolding icoll_def
                                apply (subst lfilter_False)
                                subgoal
                                  apply clarsimp
                                  unfolding BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary
                                  apply simp
                                  apply (metis (no_types, opaque_lifting) MyPair_le Un_iff bot_nat_0.extremum frontier_less_equal_trans myprod.exhaust myprod.sel(1) snd_eqD trivial_dataflow_topology_interpretation.sum_le_zeroD)
                                  done
                                subgoal
                                  by simp
                                done
                              subgoal
                                apply (drule frontier_less_equal_exit_scope)
                                apply (drule not_frontier_less_equal_sum)
                                apply clarsimp
                                unfolding icoll_def
                                apply (subst lfilter_False)
                                subgoal
                                  apply clarsimp
                                  unfolding BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary
                                  apply simp
                                  apply (metis (no_types, opaque_lifting) MyPair_le Un_iff bot_nat_0.extremum frontier_less_equal_trans myprod.exhaust myprod.sel(1) snd_eqD trivial_dataflow_topology_interpretation.sum_le_zeroD)
                                  done
                                subgoal
                                  by simp
                                done
                              done
                            done
                          done
                        subgoal
                          by (metis List.empty_filter_conv order_class.order_eq_iff)
                        done
                      subgoal
                        using label_prop_inv(4) by fast
                      done
                    done
                  done
                done
              done
            done
          subgoal
            using subgraph_inv by auto
          subgoal
            using subgraph_inv by auto
          subgoal
            using os_inv(2) by force
          subgoal
            using os_inv(3) by force
          subgoal
            apply (rule exI[of _ T])
            apply (simp add: operator_state.defs)
            apply safe
            subgoal
              apply (rule exI[of _ G])
              apply (rule exI[of _ V])
              apply (rule exI[of _ L])
              unfolding drop_caps_def produces_def release_caps_def
              apply (simp add: os_inv(4) operator_state.defs)
              done
            subgoal
              using os_inv(5) apply -
              unfolding ty1_check_def os_inv(1)
              apply (auto simp add: operator_state.defs)
              done
            subgoal
              using os_inv(6) 
              unfolding label_prob_ty2_check_def os_inv(4)  
                drop_caps_def produces_def release_caps_def label_prop_output_batch_def
              by (auto simp add: operator_state.defs)
            subgoal
              using os_inv(7) 
              unfolding input_ocaps_inv_def  os_inv(4)  
                drop_caps_def produces_def release_caps_def
              by (auto simp add: os_inv(7)[rule_format, of 1] raw_summary_def operator_state.defs dest!: in_set_list_diffD del: in_set_list_diffI intro!: in_set_list_diffI)
            subgoal
              using os_inv(7) 
              unfolding input_ocaps_inv_def  os_inv(4)  
                drop_caps_def produces_def release_caps_def
              by (auto simp add: os_inv(7)[rule_format, of 1] raw_summary_def operator_state.defs dest!: in_set_list_diffD del: in_set_list_diffI intro!: in_set_list_diffI)
            subgoal
              by (auto simp add: label_prop_output_batch_def if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
            subgoal premises aux
              apply (rule iffD1[OF dataplane_tracker_inv_clean, rotated 2, of _ _ sg "upfro sg"])
                apply (rule dataplane_tracker_inv_produces_drops[OF D, where nid=1 and os=os 
                    and drops = "\<lambda> p. if p = 1
                         then []
                         else filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)) (ocaps os_label_prop 0)"
                    and produs="map (\<lambda> t . (0, MyPair t 0, 1)) (rmdups {} (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)) (ocaps os_label_prop 0))))"
                    and oputs="(\<lambda> p. if p = 1 then [] else map (\<lambda>t. (en2 os_label_prop (components_from_labels (all_edges os_label_prop t) (min_label os_label_prop t)), (MyPair t 0)))
                          (rmdups {} (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)) (ocaps os_label_prop 0)))))"])
                           apply (rule refl)+
                      prefer 9
              subgoal
                apply (intro allI impI conjI)
                       apply simp
                subgoal
                  apply (rule ext)+
                  unfolding produces_def drop_caps_def
                  apply auto
                  subgoal
                    apply (subst filter_False)
                     apply auto
                    done
                  subgoal for p
                    apply (subst (2) filter_True)
                     apply clarsimp
                     apply (metis num2_neq(2))
                    apply (simp add: comp_def)
                    done
                  done
                subgoal
                  by auto
                subgoal
                  unfolding produces_def drop_caps_def
                  by auto
                subgoal
                  unfolding produces_def drop_caps_def label_prop_output_batch_def
                  by auto
                subgoal
                  apply (rule ext)+
                  unfolding produces_def drop_caps_def
                  apply (auto simp add: filter_True)
                  apply (subst filter_True)
                   apply auto
                  subgoal for p a t
                    apply (subgoal_tac "p = 0")
                    subgoal
                      using label_prop_inv(3)[rule_format, of "myfst t"] apply -
                      apply (drule meta_mp)
                      subgoal
                        by auto
                      subgoal
                        by (simp add: os_inv(4) operator_state.defs exit_scope_plus_distrib frontier_less_equal_antichain_plusI2)
                      done
                    subgoal
                      by (metis num2_neq(2))
                    done
                  done
                subgoal
                  apply (rule ext)+
                  unfolding produces_def drop_caps_def label_prop_output_batch_def
                  apply (clarsimp simp add: operator_state.defs os_inv(4) filter_empty_conv)
                  subgoal for p
                    apply (subgoal_tac "p = 0")
                    subgoal
                      apply (subst (2) filter_True)
                      subgoal
                        by auto
                      subgoal
                        by simp
                      done
                    subgoal
                      by (metis num2_neq(2))
                    done
                  done
                subgoal for nid
                  unfolding produces_def drop_caps_def
                  by auto
                done
              subgoal
                using num2_neq(2) by (force simp add: operator_state.defs os_inv(4))
              subgoal
                apply (clarsimp simp add: operator_state.defs os_inv(4))
                subgoal for x
                  using label_prop_inv(5)[unfolded buffers_inv, simplified]
                  by (metis UnI1 myprod.collapse)               
                done
              subgoal 
                apply (clarsimp simp add: operator_state.defs os_inv(4))
                subgoal for p x
                  using label_prop_inv(5)[unfolded buffers_inv, simplified]
                  by (metis (full_types) UnCI myprod.exhaust_sel num2_neq(2))
                done
              subgoal 
                apply (auto simp add: filter_False comp_def operator_state.defs os_inv(4))
                subgoal for p
                  apply (subgoal_tac "p = 0")
                  subgoal
                    by (auto simp add: filter_True comp_def operator_state.defs os_inv(4))
                  subgoal
                    by (metis num2_neq(2))
                  done
                done
              subgoal
                using G by assumption
              subgoal
                using subgraph_inv(2) by assumption
              subgoal
                using dataplane_inv by assumption
              subgoal
                by auto
              done
            subgoal
              unfolding label_prop_output_batch_def
              by (auto simp add: csets_inv(1) if_distrib[of input] label_prop_output_batch_def filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
            subgoal
              unfolding label_prop_output_batch_def
              by (auto simp add: csets_inv(1) if_distrib[of input] label_prop_output_batch_def filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
            subgoal premises aux for a b aa _ _ ab tt
              using aux(3,2)[unfolded label_prop_output_batch_def] apply -
              apply (clarsimp simp add: csets_inv(1) operator_state.defs os_inv if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
              apply (subst (1) icoll_lshift)
              subgoal
                using input_stream_inv timely_input_stream_expires_le 
                by auto
              subgoal
                apply (clarsimp simp add: icoll_append operator_state.defs os_inv if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
                apply (rule cimage_eqI[rotated, of tt])
                 apply force
                apply (clarsimp simp add: icoll_append operator_state.defs os_inv if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
                apply (subst (1) icoll_lshift)
                subgoal
                  using input_stream_inv timely_input_stream_expires_le 
                  by auto
                apply (clarsimp simp add: icoll_append operator_state.defs os_inv if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
                done
              done
            subgoal premises aux
              using aux(3,2)[unfolded label_prop_output_batch_def] apply -
              apply (clarsimp simp add: csets_inv(1) operator_state.defs os_inv if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
              apply (subst (1) icoll_lshift)
              subgoal
                using input_stream_inv timely_input_stream_expires_le 
                by auto
              subgoal
                apply (clarsimp simp add: icoll_append operator_state.defs os_inv if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
                apply (rule cimage_eqI[rotated])
                 apply force
                apply (clarsimp simp add: icoll_append operator_state.defs os_inv if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
                apply (subst (1) icoll_lshift)
                subgoal
                  using input_stream_inv timely_input_stream_expires_le 
                  by auto
                apply (clarsimp simp add: icoll_append operator_state.defs os_inv if_distrib[of input] filter_empty_conv inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary buffers_inv BULK_BENQ_def split: if_splits)
                done
              done
            subgoal
              using input_stream_inv by auto
            subgoal
              using label_prop_inv(1)
              unfolding labels_cc_inv_def
              by auto
            subgoal
              using label_prop_inv(2) by auto
            subgoal
              using label_prop_inv(3) by auto
            subgoal
              using label_prop_inv(4)
              unfolding drop_caps_def release_caps_def
              by (auto dest!: in_set_list_diffD)
            subgoal
              using label_prop_inv(5)
              unfolding drop_caps_def release_caps_def
              by (auto dest!: in_set_list_diffD)
            subgoal
              using label_prop_inv(5)
              unfolding drop_caps_def release_caps_def
              by (auto dest!: in_set_list_diffD)
            subgoal
              using label_prop_inv(5)
              unfolding drop_caps_def release_caps_def
              by (auto dest!: in_set_list_diffD)
            subgoal
              using label_prop_inv(5)
              unfolding drop_caps_def release_caps_def
              by (auto dest!: in_set_list_diffD)
            subgoal
              using label_prop_inv(6) by assumption
            subgoal premises aux
              using label_prop_inv(7) apply -
              unfolding input_ocaps_inv_def drop_caps_def
              apply (auto simp add: filter_False os_inv(7)[rule_format, unfolded raw_summary_def, simplified])
              subgoal for a b
                apply (drule spec2[of _  0])
                apply simp
                apply (drule bspec[of _ ])
                 apply assumption
                apply (simp add: filter_True comp_def )
                apply (rule in_set_list_diffI)
                 apply fastforce
                apply simp
                using label_prop_inv(3)[rule_format, of "myfst b"] apply -
                apply (drule meta_mp)
                subgoal
                  by force
                subgoal
                  apply (simp add: operator_state.defs os_inv(4) exit_scope_plus_distrib)
                  apply (rule frontier_less_equal_antichain_plusI2)
                  apply auto
                  done
                done
              done
            done
          done
        subgoal
          apply (simp  del: filter.simps split: list.splits)
          subgoal for x xs
            apply (cases x; simp del: filter.simps)
            apply hypsubst_thin
            subgoal for d t
              apply (simp del: filter.simps split: prod.splits)
              subgoal for v1 v2 l1 l2
                apply hypsubst_thin
                apply (intro exI conjI relcomppI)
                   apply (rule rtranclp.intros(1))
                  apply (rule bisim_refl)
                 defer
                 apply (rule wbisim_refl)
                apply (rule wb_upto_b_base)
                unfolding R_def[simplified]
                apply (rule exI[of _ S])
                apply (rule exI[of _ SO])
                apply (rule exI[of _ "((\<lambda>ta. ((1, 0), Inr (ccs (set (icoll (map (\<lambda>(x, t'). Data t' (projl x)) (chns (1, 0)) @@- lxs) ta) \<union>
                  all_edges (release_caps
                       (produces
                         (drop_caps
                           (add_caps (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (map snd (label_prop_edge_batch os_label_prop
                               (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                               (myfst t) l1 l2 t)))
                           (map snd (label_prop_edge_batch os_label_prop
                             (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                         (label_prop_edge_batch os_label_prop
                           (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                           (myfst t) l1 l2 t))
                       1) (myfst ta))), ta)) |`|
                  cUn (cUn (ts lxs) (snd |`| cset_from_list (chns (1, 0))))
                    ((\<lambda>t0. MyPair t0 0) |`| cset_from_list (timestamps os_label_prop)))"])

                apply (rule exI[of _ D])
                apply (rule exI[of _ lxs])
                apply (rule exI[of _ "os(1 := release_caps
                       (produces
                         (drop_caps
                           (add_caps ((os 1)\<lparr>input := (input os_label_prop)(0 := xs)\<rparr>)
                             (map snd (label_prop_edge_batch os_label_prop
                               (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                               (myfst t) l1 l2 t)))
                           (map snd (label_prop_edge_batch os_label_prop
                             (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                         (label_prop_edge_batch os_label_prop
                           (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                           (myfst t) l1 l2 t))
                       1)"])
                apply (rule exI[of _ "release_caps
                       (produces
                         (drop_caps
                           (add_caps (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (map snd (label_prop_edge_batch os_label_prop
                               (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                               (myfst t) l1 l2 t)))
                           (map snd (label_prop_edge_batch os_label_prop
                             (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                         (label_prop_edge_batch os_label_prop
                           (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                           (myfst t) l1 l2 t))
                       1"])

                apply (rule exI[of _ cbufs])
                apply (rule exI[of _ "(outputs_at_target (summ sg) (os(1 := release_caps
                       (produces
                         (drop_caps
                           (add_caps ((os 1)\<lparr>input := (input os_label_prop)(0 := xs)\<rparr>)
                             (map snd (label_prop_edge_batch os_label_prop
                               (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                               (myfst t) l1 l2 t)))
                           (map snd (label_prop_edge_batch os_label_prop
                             (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                         (label_prop_edge_batch os_label_prop
                           (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                           (myfst t) l1 l2 t))
                       1)) >> cbufs) >> inputs_at_target (os(1 := release_caps
                       (produces
                         (drop_caps
                           (add_caps (os 1\<lparr>input := (input (os 1))(0 := xs)\<rparr>)
                             (map snd (label_prop_edge_batch os_label_prop
                               (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                               (myfst t) l1 l2 t)))
                           (map snd (label_prop_edge_batch os_label_prop
                             (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                         (label_prop_edge_batch os_label_prop
                           (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                           (myfst t) l1 l2 t))
                       1))"])
                apply (rule exI[of _ sg])
                apply (intro conjI)
                subgoal
                  by (simp add: operator_state.defs dataflow_tree_to_operator_def os_inv(1))
                subgoal premises aux
                  using aux(1,2,3) apply -
                  apply (simp  del: filter.simps add: label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
                  apply (rule arg_cong2[where f=set_spec_op])
                   apply (simp_all del: filter.simps)
                  apply (clarsimp simp del: filter.simps del: disjCI simp add: inputs_at_target_def BULK_BENQ_def operator_state.defs outputs_at_target_raw_summary subgraph_inv buffers_inv csets_inv(1) os_inv(4))
                  subgoal
                    apply (subst (1) icoll_LCons_Data)
                    subgoal
                      using input_stream_inv timely_input_stream_expires_le 
                      by auto
                    subgoal
                      apply (simp add: input_tl_def)
                      apply (subgoal_tac "t = MyPair (myfst t) 0")
                      subgoal
                        apply (subst (1) all_edges_eq[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                        subgoal 
                          using label_prop_inv(6)[unfolded os_inv(4) operator_state.defs] by simp
                        subgoal by simp
                        subgoal
                          apply simp
                          apply (rule arg_cong2[where f=cinsert])
                          subgoal
                            apply (subst (1) icoll_LCons_Data)
                            subgoal
                              using input_stream_inv timely_input_stream_expires_le
                              by auto
                            apply (simp add: insert_commute ccs_insert_symmetric)
                            apply (subst ccs_insert_swap)
                            apply (rule refl)
                            done
                          subgoal
                            apply (rule arg_cong2[where f=cUn])
                            subgoal
                              by simp
                            subgoal
                              apply (subst (1) icoll_LCons_Data)
                              subgoal
                                using input_stream_inv timely_input_stream_expires_le 
                                by auto
                              subgoal 
                                apply (rule cimage_cong)
                                subgoal
                                  by simp
                                subgoal for t''
                                  apply (cases "t \<le> t''")
                                  subgoal
                                    apply (subst all_edges_eq_le[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                                    subgoal using label_prop_inv(6)[unfolded os_inv(4) operator_state.defs] by simp
                                    subgoal 
                                      using myfst_mono by blast
                                    subgoal by simp
                                    subgoal
                                      apply (subst insert_commute)
                                      apply (simp add: ccs_insert_symmetric)
                                      apply (subst (1) icoll_LCons_Data)
                                      subgoal
                                        using input_stream_inv timely_input_stream_expires_le 
                                        by auto
                                      subgoal
                                        apply simp
                                        done
                                      done
                                    done
                                  subgoal
                                    apply (subst all_edges_eq_not_le[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                                    subgoal
                                      by (metis MyPair_mono bot_nat_0.extremum myprod.exhaust_sel)
                                    subgoal
                                      by simp
                                    subgoal
                                      apply (subst (1) icoll_LCons_Data)
                                      subgoal
                                        using input_stream_inv timely_input_stream_expires_le
                                        by auto
                                      apply simp
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      subgoal
                        using label_prop_inv(5)[rule_format, of t] apply -
                        apply (drule meta_mp)
                        subgoal
                          by auto
                        subgoal
                          apply (cases t)
                          apply auto
                          done
                        done
                      done
                    done
                  done
                subgoal
                  using subgraph_inv(1) by assumption
                subgoal
                  using subgraph_inv(2) by assumption
                subgoal
                  using os_inv(2)
                  by auto
                subgoal
                  using os_inv(3)
                  by auto
                subgoal 
                  apply (simp del: filter.simps add:  operator_state.defs os_inv(4) )
                  apply (rule exI[of _ "Cons (myfst t) T"])
                  apply (simp del: filter.simps)
                  apply (intro conjI)
                  subgoal 
                    apply (rule exI[of _ "G(myfst t := (map_entry v1 (Cons v2) (G (myfst t)))(v2 := Cons v1 (G (myfst t) v2)))"])
                    apply (rule exI[of _ "map_entry (myfst t) (append [v1, v2]) V"])
                    apply (rule exI[of _ "L(myfst t := (L (myfst t))(l1 := l2))"])
                    apply (auto simp add: label_prop_neighbor_batch_def add_caps_def comp_def operator_state.defs  produces_def release_caps_def drop_caps_def label_prop_edge_batch_def label_prop_edge_record_update_def input_tl_def)
                    done
                  subgoal 
                    using os_inv(1,5)
                    unfolding ty1_check_def
                    by (auto simp add: operator_state.defs produces_def release_caps_def drop_caps_def)
                  subgoal premises aux
                    using os_inv(4,6) aux(1,2,3) apply -
                    unfolding label_prob_ty2_check_def add_caps_def input_tl_def label_prop_edge_batch_def label_prop_edge_record_update_def label_prop_neighbor_batch_def
                    apply (auto 0 0 simp add: os_inv(1,4) image_iff operator_state.defs produces_def release_caps_def drop_caps_def)
                    subgoal
                      by (metis UnI1 img_fst list.set_intros(2))
                    subgoal
                      by auto
                    subgoal
                      by force
                    subgoal
                      by force
                    done
                  subgoal premises aux
                    unfolding add_caps_def
                    using os_inv(7) by auto
                  subgoal premises aux

                    unfolding release_caps_def
                    apply (simp del: filter.simps)
                    apply (rule iffD1[OF dataplane_tracker_inv_clean_reorder_ocaps, rotated 2, of _ _ sg "upfro sg"])
                      apply (rule dataplane_tracker_inv_produces_drops_alt
                        [OF D, where nid=1 and p=0 and n=1 and os=os and
                          produs="map (\<lambda> (_, cap :: (2, (nat, nat) myprod) capability). (1, capability.time cap, 1)) (label_prop_edge_batch
                         \<lparr>intsum = intsum (os 1), consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1),
                            front = front (os 1), ocaps = ocaps (os 1), initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G,
                            vertices = V, label = L\<rparr>
                         (label_prop_edge_record_update
                           (input_tl
                             \<lparr>intsum = intsum (os 1), consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1),
                                front = front (os 1), ocaps = ocaps (os 1), initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G,
                                vertices = V, label = L\<rparr>
                             0)
                           (myfst t) v1 v2 l1 l2)
                         (myfst t) l1 l2 t)" and
                          oputs="(\<lambda> p. if p = 0 then [] else (map (\<lambda> (d, cap :: (2, (nat, nat) myprod) capability). (d, capability.time cap)) (label_prop_edge_batch
                         \<lparr>intsum = intsum (os 1), consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1),
                            front = front (os 1), ocaps = ocaps (os 1), initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G,
                            vertices = V, label = L\<rparr>
                         (label_prop_edge_record_update
                           (input_tl
                             \<lparr>intsum = intsum (os 1), consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1),
                                front = front (os 1), ocaps = ocaps (os 1), initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G,
                                vertices = V, label = L\<rparr>
                             0)
                           (myfst t) v1 v2 l1 l2)
                         (myfst t) l1 l2 t)))" and
                          drops="(\<lambda> p. if p = 0 then [] else list_diff (ocaps (os 1) 1) (map snd (xs @ input (os 1) 1)))"
                          and ninter="operator_state.inter (os 1) @
                         map (\<lambda>x. (out (snd x), capability.time (snd x), 1))
                         (label_prop_edge_batch
                           \<lparr>intsum =
                              \<lambda>p1 p2.
                                 case if p1 = 0 \<and> p2 = 0 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0))
                                      else if p1 = 0 \<and> p2 = 1 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1)) else if p1 = 1 \<and> p2 = 1 then Some (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)) else None of
                                 None \<Rightarrow> [] | Some (l1' :: (3, 2) location, s, l2' :: (3, 2) location) \<Rightarrow> s,
                              consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1), ocaps = ocaps (os 1), initia = True,
                              en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>
                           (label_prop_edge_record_update
                             (input_tl
                               \<lparr>intsum =
                                  \<lambda>p1 p2.
                                     case if p1 = 0 \<and> p2 = 0 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0))
                                          else if p1 = 0 \<and> p2 = 1 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1)) else if p1 = 1 \<and> p2 = 1 then Some (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)) else None of
                                     None \<Rightarrow> [] | Some (l1' :: (3, 2) location, s, l2' :: (3, 2) location) \<Rightarrow> s,
                                  consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1), ocaps = ocaps (os 1),
                                  initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>
                               0)
                             (myfst t) v1 v2 l1 l2)
                           (myfst t) l1 l2 t) @
                         map (\<lambda>x. (out (snd x), capability.time (snd x), - 1))
                         (label_prop_edge_batch
                           \<lparr>intsum =
                              \<lambda>p1 p2.
                                 case if p1 = 0 \<and> p2 = 0 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0))
                                      else if p1 = 0 \<and> p2 = 1 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1)) else if p1 = 1 \<and> p2 = 1 then Some (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)) else None of
                                 None \<Rightarrow> [] | Some (l1' :: (3, 2) location, s, l2' :: (3, 2) location) \<Rightarrow> s,
                              consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1), ocaps = ocaps (os 1), initia = True,
                              en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>
                           (label_prop_edge_record_update
                             (input_tl
                               \<lparr>intsum =
                                  \<lambda>p1 p2.
                                     case if p1 = 0 \<and> p2 = 0 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0))
                                          else if p1 = 0 \<and> p2 = 1 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1)) else if p1 = 1 \<and> p2 = 1 then Some (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)) else None of
                                     None \<Rightarrow> [] | Some (l1' :: (3, 2) location, s, l2' :: (3, 2) location) \<Rightarrow> s,
                                  consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1), ocaps = ocaps (os 1),
                                  initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>
                               0)
                             (myfst t) v1 v2 l1 l2)
                           (myfst t) l1 l2 t) @
                                             map (\<lambda> c. (1, c, -1)) (list_diff
     (list_diff
       (list_diff
         (ocaps (os 1) 1 @
          map capability.time
           (filter (\<lambda>cap::(2, (nat, nat) myprod) capability. out cap = 1)
             (map snd
               (label_prop_edge_batch
                 \<lparr>intsum =
                    \<lambda>p1 p2.
                       case if p1 = 0 \<and> p2 = 0 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0))
                            else if p1 = 0 \<and> p2 = 1 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1))
                                 else if p1 = 1 \<and> p2 = 1 then Some (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)) else None of
                       None \<Rightarrow> [] | Some (l1' :: (3, 2) location, s, l2' :: (3, 2) location) \<Rightarrow> s,
                    consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1), ocaps = ocaps (os 1),
                    initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>
                 (label_prop_edge_record_update
                   (input_tl
                     \<lparr>intsum =
                        \<lambda>p1 p2.
                           case if p1 = 0 \<and> p2 = 0 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0))
                                else if p1 = 0 \<and> p2 = 1 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1))
                                     else if p1 = 1 \<and> p2 = 1 then Some (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)) else None of
                           None \<Rightarrow> [] | Some (l1' :: (3, 2) location, s, l2' :: (3, 2) location) \<Rightarrow> s,
                        consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1), ocaps = ocaps (os 1),
                        initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>
                     0)
                   (myfst t) v1 v2 l1 l2)
                 (myfst t) l1 l2 t))))
         (map capability.time
           (filter (\<lambda>cap::(2, (nat, nat) myprod) capability. out cap = 1)
             (map snd
               (label_prop_edge_batch
                 \<lparr>intsum =
                    \<lambda>p1 p2.
                       case if p1 = 0 \<and> p2 = 0 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0))
                            else if p1 = 0 \<and> p2 = 1 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1))
                                 else if p1 = 1 \<and> p2 = 1 then Some (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)) else None of
                       None \<Rightarrow> [] | Some (l1' :: (3, 2) location, s, l2' :: (3, 2) location) \<Rightarrow> s,
                    consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1), ocaps = ocaps (os 1),
                    initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>
                 (label_prop_edge_record_update
                   (input_tl
                     \<lparr>intsum =
                        \<lambda>p1 p2.
                           case if p1 = 0 \<and> p2 = 0 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 0))
                                else if p1 = 0 \<and> p2 = 1 then Some (Loc 1 (Trg 0), [MyPair 0 0], Loc 1 (Src 1))
                                     else if p1 = 1 \<and> p2 = 1 then Some (Loc 1 (Trg 1), [MyPair 0 0], Loc 1 (Src 1)) else None of
                           None \<Rightarrow> [] | Some (l1' :: (3, 2) location, s, l2' :: (3, 2) location) \<Rightarrow> s,
                        consu = consu (os 1), inter = operator_state.inter (os 1), produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1), ocaps = ocaps (os 1),
                        initia = True, en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>
                     0)
                   (myfst t) v1 v2 l1 l2)
                 (myfst t) l1 l2 t)))))
       (map snd xs))
     (map snd (input (os 1) 1)))"])
                                 apply (rule refl)+
                             prefer 10
                             apply (intro allI impI conjI)
                                    prefer 4
                    subgoal
                      by (clarsimp simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                    subgoal
                      by (clarsimp simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                    subgoal for ni p
                      apply (clarsimp simp add: filter_mset_image_mset os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                      subgoal
                        apply (subgoal_tac " p = 1")
                        subgoal
                          by simp
                        subgoal
                          using num2_neq(2) by blast
                        done
                      done
                    subgoal
                      by (clarsimp simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                    subgoal
                      unfolding produces_def label_prop_edge_batch_def label_prop_neighbor_batch_def 
                        (* show but finishes *)
                      by (clarsimp simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                    subgoal
                      using aux(2)
                      by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                    subgoal for nid
                      apply (rule ext)+
                      apply (auto 0 0 simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                      subgoal
                        unfolding produces_def label_prop_edge_batch_def label_prop_neighbor_batch_def 
                        by (clarsimp simp add: filter_mset_image_mset os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                      subgoal for p
                        apply (subgoal_tac " p = 1")
                        subgoal
                          unfolding produces_def label_prop_edge_batch_def label_prop_neighbor_batch_def 
                          by (clarsimp simp add: filter_mset_image_mset os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                        subgoal
                          using num2_neq(2) by blast
                        done
                      done
                    subgoal
                      by (clarsimp simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                    subgoal
                      apply (clarsimp simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                      apply (rule arg_cong2[where f="(+)"])
                      subgoal
                        unfolding label_prop_edge_batch_def label_prop_neighbor_batch_def
                        by (auto intro!: multiset.map_cong0)
                      subgoal
                        unfolding label_prop_edge_batch_def label_prop_neighbor_batch_def
                        by (auto intro!: multiset.map_cong0)
                      done
                    subgoal
                      using num2_cases by force
                    subgoal
                      apply (subgoal_tac "t \<in> set (ocaps (os 1) 1)")
                      subgoal
                        unfolding label_prop_edge_batch_def label_prop_neighbor_batch_def label_prop_edge_record_update_def
                        apply (auto del: disjCI simp add: image_iff split_beta)
                        apply (rule bexI[rotated])
                         apply assumption
                        apply (simp add: less_eq_myprod_def)
                        done
                      subgoal
                        apply (rule  label_prop_inv(7)[unfolded input_ocaps_inv_def, rule_format, of _ 0 0, simplified])
                        subgoal
                          using aux(2,3) by simp
                        subgoal
                          by (simp add: zero_myprod_def os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                        done
                      done
                    subgoal
                      apply (subgoal_tac "t \<in> set (ocaps (os 1) 1)")
                      subgoal
                        apply (intro conjI allI)
                        subgoal for p
                          apply (cases "p = 1")
                          subgoal
                            unfolding label_prop_edge_batch_def label_prop_neighbor_batch_def label_prop_edge_record_update_def
                            apply (auto del: disjCI simp add: image_iff split_beta)
                            apply (metis MyPair_mono myprod.exhaust_sel verit_comp_simplify1(2))
                            done
                          subgoal
                            unfolding label_prop_edge_batch_def label_prop_neighbor_batch_def label_prop_edge_record_update_def
                            using num2_neq(2) by (auto del: disjCI simp add: image_iff split_beta)
                          done
                        done
                      subgoal
                        apply (rule  label_prop_inv(7)[unfolded input_ocaps_inv_def, rule_format, of _ 0 0, simplified])
                        subgoal
                          using aux(2,3) by simp
                        subgoal
                          by (simp add: zero_myprod_def os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                        done
                      done
                    subgoal
                      apply (clarsimp simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                      subgoal for p
                        apply (subgoal_tac "p = 1")
                        subgoal
                          by (clarsimp simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] comp_def split_beta filter_False filter_True drop_caps_def add_caps_def)
                        subgoal
                          using num2_cases by force
                        done
                      done
                    subgoal
                      using G by assumption
                    subgoal
                      using subgraph_inv(2) by assumption
                    subgoal
                      using dataplane_inv by assumption
                    subgoal
                      by simp
                    done
                  subgoal premises aux
                    using aux(1,2,3) apply -
                    apply (simp add: buffers_inv image_iff)
                    unfolding BULK_BENQ_def inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary label_prop_edge_record_update_def input_tl_def
                    apply (clarsimp del: disjCI)
                    apply (subst (1) icoll_LCons_Data)
                    subgoal
                      using input_stream_inv timely_input_stream_expires_le
                      by auto
                    subgoal
                      apply (subgoal_tac "t = MyPair (myfst t) 0")
                      apply (clarsimp simp add: icoll_append)
                      apply (rule arg_cong2[where f=cinsert])
                      subgoal
                        apply (subst (1 2) all_edges_eq[rotated, where V=V and label_sync=" L"])
                        prefer 4
                        apply (simp add: insert_commute ccs_insert_symmetric)
                        prefer 2
                        apply simp
                        using label_prop_inv(6)[unfolded os_inv(4) operator_state.defs, simplified] apply simp_all
                        done
                      subgoal
                        apply (rule cimage_cong)
                        apply simp
                        subgoal for t'
                          apply (subst (1) icoll_LCons_Data)
                          subgoal
                            using input_stream_inv timely_input_stream_expires_le
                            by auto
                          apply (cases "t \<le> t'")
                          subgoal
                            apply simp
                            apply (subst (1 2) all_edges_eq_le[rotated, where V=V and label_sync=" L"])
                            using label_prop_inv(6)[unfolded os_inv(4) operator_state.defs, simplified] apply simp_all
                            using myfst_mono apply blast
                            done
                          subgoal
                            by simp
                          done
                        done
                      subgoal
                        using label_prop_inv(5)[rule_format, of t] apply -
                        apply (drule meta_mp)
                        subgoal
                          by auto
                        subgoal
                          apply (cases t)
                          apply auto
                          done
                        done
                      done
                    done
                  subgoal premises aux
                    by (auto simp add: label_prop_edge_batch_def label_prop_neighbor_batch_def image_iff csets_inv(2))
                  subgoal
                    using input_stream_inv by assumption
                  subgoal
                    apply safe
                    subgoal for t''
                      apply (rule labels_cc_inv_input0_preserved[where xs=xs])
                      using label_prop_inv(1) apply blast
                      subgoal
                        using label_prop_inv(6) by assumption
                      subgoal
                        by (clarsimp simp add: input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                      apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                      apply simp
                      apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                      apply simp
                      apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                      apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                      apply simp
                      apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                      done
                    done
                  subgoal premises aux
                    apply safe
                    subgoal for t'
                      unfolding label_prop_edge_record_update_def
                      apply simp      
                      apply (elim disjE)
                      subgoal
                      apply (subgoal_tac "frontier_less_equal (exit_scope myfst (front (os 1) 1)) t'")
                        subgoal
                          by (simp add: exit_scope_plus_distrib frontier_less_equal_antichain_plusI2)
                      subgoal
                        using aux(2) label_prop_inv(3)[rule_format] by auto
                      done
                    subgoal
                      apply (rule labels_stable_input0_preserved[of _ "myfst t"])
                      using label_prop_inv(2)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of t']


                    using label_prop_inv

end



                      find_theorems t

          

                      find_theorems labels_stable name: preser


                      find_theorems os_label_prop

end
                    sorry
                  subgoal premises aux
                    using aux(2) label_prop_inv(3)
                    by auto
                  subgoal
                    using label_prop_inv(4) 
                    unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                    by (auto dest!: in_set_list_diffD  simp add:  comp_def release_caps_def drop_caps_def)
                  subgoal
                    using label_prop_inv(5) 
                    unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                    by (auto dest!: in_set_list_diffD  simp add: release_caps_def drop_caps_def)
                  subgoal
                    apply (rule label_prop_upd_inv_input0_preserved)
                    apply (rule label_prop_inv(6))
                    unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                    apply (auto simp add: operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                    done
                  done
                done
              done
            done
          done
        subgoal
          sorry
        done
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal for d t xs (* Laouen *)
        (* old proof, might be salvaged --
        apply (intro exI conjI)
         apply (rule rtranclp.rtrancl_refl)
        apply (intro relcomppI)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def)
        apply (rule exI[of _ \<open>cinsert ((1, 0), d, t) S\<close>])
        apply (rule exI[of _ \<open>cset_from_list (map (\<lambda>x. ((1, 0), x)) xs)\<close>])
        apply (rule exI[of _ SP])
        apply (rule exI)
        apply (rule exI)
        apply (rule exI[of _ \<open>os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(0 := xs)\<rparr>)\<close>])
        apply (rule exI)
        apply (rule exI[of _ \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(0 := xs)\<rparr>\<close>])
        apply (intro exI conjI)
                            apply (simp add: dataflow_tree_to_operator_def)
                           apply (rule arg_cong[where f=\<open>\<lambda>X. set_spec_op (cUn X SP) D\<close>])
        using SIM1(6,14) apply (simp add: operator_state.defs(3))
                            apply (simp_all add: SIM1 operator_state.defs(3))
        using SIM1(3,7) unfolding ty1_check_def apply (simp add: operator_state.defs(3), blast)
        subgoal
          using SIM1(6,8) that unfolding label_prob_ty2_check_def apply -
          by (simp add: operator_state.defs(3), drule spec[of _ 0], simp)
        using SIM1(9) unfolding input_ocaps_inv_def apply simp
                  defer
                  apply (subgoal_tac \<open>outputs_at_target (antichain_from_list \<circ>\<circ> raw_summary) (os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(0 := xs)\<rparr>)) (1, 0)
  = outputs_at_target (antichain_from_list \<circ>\<circ> raw_summary) os (1, 0)\<close>)
        subgoal
          apply (simp add: BULK_BENQ_def)
          apply (rule arg_cong[where f=\<open>\<lambda>x. cimage x _\<close>])
          apply (simp add: fun_eq_iff)
          apply (rule allI)
          apply (rule arg_cong[where f=ccs])
          apply (rule arg_cong[where f=\<open>\<lambda>x. _ \<union> x\<close>])
          by (simp add: all_edges_def neighbors_def)
                  apply (simp add: outputs_at_target_raw_summary)
                  apply (rule input_stream_inv)
                  apply (rule dataplane_tracker_inv_update_outputs_outside)
                  apply (rule SIM1(12))
        unfolding fun_upd_def apply simp
        using subgraph_inv apply (simp add: raw_summary_def)
        sorry
*)
        sorry
      done
  qed
next
  case SIM2
  then show ?case sorry
  oops
end
