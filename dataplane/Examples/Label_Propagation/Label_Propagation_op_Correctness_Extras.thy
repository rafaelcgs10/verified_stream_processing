theory Label_Propagation_op_Correctness_Extras

imports
  Label_Propagation_op
  "../Ooo_Input_op"
  "../Increment_op"
  "../Set_op"
  "../../Timely/Dataflow_Op"
  "../../Correctness/General"
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

section \<open>Dataflow wiring and generic preservation facts\<close>

subsection \<open>Concrete wiring\<close>


abbreviation "(loop_wire :: 3 + 3 \<times> 2 \<Rightarrow> (3 + 3 \<times> 2) option) \<equiv> (case_sum (\<lambda>_. None) (\<lambda>(nid, p). case if nid = 2 \<and> p = 1 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (Inr (1 + offset, q))))"
abbreviation "(comp_wire :: 3 + 3 \<times> 2 \<Rightarrow> (3 + 3 \<times> 2) option) \<equiv> (case_sum (\<lambda>_. None) (\<lambda>(nid, p). case if nid = 1 \<and> p = 1 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (Inr (1 + 1 + offset, q))))"

lemma ran_loop_wire:
  \<open>ran loop_wire = {Inr (1, 1)}\<close>
proof -
  have \<open>loop_wire (Inr (2, 1)) = Some (Inr (1, 1))\<close> by simp
  moreover have \<open>loop_wire x = None\<close> if \<open>x \<noteq> Inr (2, 1)\<close> for x by (cases x; clarsimp simp add: that)
  ultimately show ?thesis unfolding ran_def
    using Collect_cong Set.empty_def insert_Collect option.simps(1,2) by (smt (verit, del_insts))
qed

lemma ran_comp_wire:
  \<open>ran comp_wire = {Inr (2, 1)}\<close>
proof -
  have \<open>comp_wire (Inr (1, 1)) = Some (Inr (2, 1))\<close> by simp
  moreover have \<open>comp_wire x = None\<close> if \<open>x \<noteq> Inr (1, 1)\<close> for x by (cases x; clarsimp simp add: that)
  ultimately show ?thesis unfolding ran_def
    using Collect_cong Set.empty_def insert_Collect option.simps(1,2) by (smt (verit, del_insts))
qed



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

section \<open>Concrete graph summary\<close>

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

lemma path_weight_loop_increment:
  \<open>MyPair 0 1 \<in>\<^sub>A graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
  (Loc (1 :: 3) (Trg (0 :: 2))) (Loc 1 (Trg 1))\<close> (is \<open>?s \<in>\<^sub>A graph.path_weight ?su ?l1 ?l2\<close>)
proof -
  have G: \<open>Graph.graph ?su\<close>
    using dataflow_topology.axioms(1)[OF dataflow_topology_from_tree.dataflow_topology_axioms]
      dataflow_tree_to_graph_raw_summary by metis
  let ?xs = \<open>[(?l1, 0, Loc 1 (Src 1)), (Loc 1 (Src 1), 0, Loc 2 (Trg 1)),
  (Loc 2 (Trg 1), ?s, Loc 2 (Src 1)), (Loc 2 (Src 1), 0, ?l2)]\<close>
  have s: \<open>graph.sum_path_weights ?xs = ?s\<close> by simp
  have \<open>graph.path ?su ?l1 (Loc 1 (Src 1)) [(?l1, 0, Loc 1 (Src 1))]\<close>
    using graph.path_singleton[OF G]
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  moreover have \<open>graph.path ?su (Loc 1 (Src 1)) (Loc 2 (Trg 1)) [(Loc 1 (Src 1), 0, Loc 2 (Trg 1))]\<close>
    using graph.path_singleton[OF G]
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  moreover have \<open>graph.path ?su (Loc 2 (Trg 1)) (Loc 2 (Src 1)) [(Loc 2 (Trg 1), ?s, Loc 2 (Src 1))]\<close>
    using graph.path_singleton[OF G]
    by (simp add: raw_summary_def antichain_from_list_singleton)
  moreover have \<open>graph.path ?su (Loc 2 (Src 1)) ?l2 [(Loc 2 (Src 1), 0, ?l2)]\<close>
    using graph.path_singleton[OF G]
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  ultimately have path_xs: \<open>graph.path ?su ?l1 ?l2 ?xs\<close> using G path_ConsE path_ConsI by metis
  moreover have \<open>\<not> graph.sum_path_weights ys < ?s\<close> if path_ys: \<open>graph.path ?su ?l1 ?l2 ys\<close> for ys
  proof
    assume path_weights_ys: \<open>graph.sum_path_weights ys < ?s\<close>
    obtain ys' where ys': \<open>ys = ys' @ [(Loc 2 (Trg 1), ?s, Loc 2 (Src 1)), (Loc 2 (Src 1), 0, ?l2)]\<close>
    proof -
      have \<open>ys \<noteq> []\<close> using empty_path_inversion[OF _ G] path_ys by fastforce
      then obtain ys' l1 s l2 where l1_s_l2: \<open>ys = ys' @ [(l1, s, l2)]\<close>
        using rev_cases surj_pair by metis
      hence l1_s_l2_alt: \<open>l2 = ?l2 \<and> graph.path ?su ?l1 l1 ys' \<and> s \<in>\<^sub>A ?su l1 l2\<close>
        using path_ys graph.path_AppendE[OF G] by blast
      hence l1_s: \<open>l1 = Loc 2 (Src 1) \<and> s = 0\<close>
        by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
          (insert set_antichain2 set_antichain_antichain_singleton, blast)
      have \<open>ys' \<noteq> []\<close> using empty_path_inversion[OF _ G] l1_s_l2_alt l1_s by fastforce
      then obtain ys'' l1' s' l2' where l1'_s'_l2': \<open>ys' = ys'' @ [(l1', s', l2')]\<close>
        using rev_cases surj_pair by metis
      hence l1'_s'_l2'_alt: \<open>l2' = l1 \<and> graph.path ?su ?l1 l1' ys'' \<and> s' \<in>\<^sub>A ?su l1' l2'\<close>
        using l1_s_l2_alt graph.path_AppendE[OF G] by blast
      hence l1'_s': \<open>l1' = Loc 2 (Trg 1) \<and> s' = MyPair 0 1\<close> using l1_s
        by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
          (insert set_antichain2 set_antichain_antichain_singleton, blast)
      show ?thesis using that l1_s_l2 l1'_s'_l2' l1_s l1'_s' l1_s_l2_alt l1'_s'_l2'_alt by simp
    qed
    hence \<open>[(Loc 2 (Trg 1), MyPair 0 1, Loc 2 (Src 1)), (Loc 2 (Src 1), 0, Loc 1 (Trg 1))] \<preceq> ys\<close>
      by blast
    hence \<open>?s \<le> graph.sum_path_weights ys\<close>
      using graph.subseq_sum_path_weights_le[OF G] subseq_map by fastforce
    thus False using path_weights_ys by order
  qed
  hence \<open>?s \<in> minimal_antichain {x. graph.path_weightp ?su ?l1 ?l2 x}\<close>
    using path_xs graph.in_path_weight[OF G]
    unfolding minimal_antichain_def graph.path_weightp_def[OF G] by auto
  thus ?thesis using s graph.in_path_weight[OF G] by fastforce
qed

lemma path_weight_singleton_if_lower_bound:
  assumes G: \<open>Graph.graph su\<close>
    and s_in: \<open>s \<in>\<^sub>A graph.path_weight su l1 l2\<close>
    and lower: \<open>\<And>xs. graph.path su l1 l2 xs \<Longrightarrow> s \<le> graph.sum_path_weights xs\<close>
  shows \<open>graph.path_weight su l1 l2 = antichain {s}\<close>
proof (subst ac_eq_iff, safe)
  fix x
  assume x_in: \<open>x \<in>\<^sub>A graph.path_weight su l1 l2\<close>
  then obtain xs where xs: \<open>graph.path su l1 l2 xs\<close> \<open>graph.sum_path_weights xs = x\<close>
    using graph.path_weight_conv_path[OF G] by blast
  have s_le_x: \<open>s \<le> x\<close>
    using lower[OF xs(1)] xs(2) by simp
  have s_pw: \<open>graph.path_weightp su l1 l2 s\<close>
    using s_in graph.in_path_weight[OF G]
    unfolding minimal_antichain_def by auto
  have x_min: \<open>x \<in> minimal_antichain {x. graph.path_weightp su l1 l2 x}\<close>
    using x_in graph.in_path_weight[OF G] by simp
  have \<open>\<not> s < x\<close>
    using x_min s_pw unfolding minimal_antichain_def by auto
  then show \<open>x \<in>\<^sub>A antichain {s}\<close>
    using s_le_x by (simp add: order.order_iff_strict)
next
  fix x
  assume \<open>x \<in>\<^sub>A antichain {s}\<close>
  show \<open>x \<in>\<^sub>A graph.path_weight su l1 l2\<close>
    using \<open>x \<in>\<^sub>A antichain {s}\<close> s_in
    by (metis finite.emptyI finite_insert in_antichain_minimal_antichain minimal_antichain_singleton singleton_iff)

qed

lemma path_weight_singleton_from_path_lower_bound:
  assumes G: \<open>Graph.graph su\<close>
    and path_s: \<open>graph.path su l1 l2 xs\<close>
    and sum_s: \<open>graph.sum_path_weights xs = s\<close>
    and lower: \<open>\<And>ys. graph.path su l1 l2 ys \<Longrightarrow> s \<le> graph.sum_path_weights ys\<close>
  shows \<open>graph.path_weight su l1 l2 = antichain {s}\<close>
proof -
  have s_pw: \<open>graph.path_weightp su l1 l2 s\<close>
    using path_s sum_s unfolding graph.path_weightp_def[OF G] by blast
  have s_min: \<open>s \<in> minimal_antichain {x. graph.path_weightp su l1 l2 x}\<close>
  proof (clarsimp simp add: minimal_antichain_def s_pw)
    fix y
    assume y_pw: \<open>graph.path_weightp su l1 l2 y\<close> and y_less: \<open>y < s\<close>
    obtain ys where ys: \<open>graph.path su l1 l2 ys\<close> \<open>graph.sum_path_weights ys = y\<close>
      using y_pw unfolding graph.path_weightp_def[OF G] by blast
    have \<open>s \<le> y\<close>
      using lower[OF ys(1)] ys(2) by simp

    then show False
      using y_less by order
  qed
  have s_in: \<open>s \<in>\<^sub>A graph.path_weight su l1 l2\<close>
    using s_min graph.in_path_weight[OF G] by simp
  show ?thesis
    by (rule path_weight_singleton_if_lower_bound[OF G s_in lower])
qed

lemma path_weight_singleton_trans_zero_left:
  fixes su :: \<open>'l::finite \<Rightarrow> 'l \<Rightarrow> 't::{canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} antichain\<close>
    and s :: \<open>'t\<close>
  assumes G: \<open>Graph.graph su\<close>
    and edge0: \<open>0 \<in>\<^sub>A su l0 l1\<close>
    and s_in1: \<open>s \<in>\<^sub>A graph.path_weight su l1 l2\<close>
    and lower: \<open>\<And>ys. graph.path su l0 l2 ys \<Longrightarrow> s \<le> graph.sum_path_weights ys\<close>
  shows \<open>graph.path_weight su l0 l2 = antichain {s}\<close>
proof -
  have zero_in: \<open>0 \<in>\<^sub>A graph.path_weight su l0 l1\<close>
    using edge0 by (rule path_weight_direct_0path[OF G])
  obtain u where u: \<open>u \<in>\<^sub>A graph.path_weight su l0 l2\<close> \<open>u \<le> 0 + s\<close>
    using graph.path_weight_elem_trans[OF G zero_in s_in1] by blast
  obtain ys where ys: \<open>graph.path su l0 l2 ys\<close> \<open>graph.sum_path_weights ys = u\<close>
    using u(1) graph.path_weight_conv_path[OF G] by blast
  have \<open>s \<le> u\<close>
    using lower[OF ys(1)] ys(2) by simp
  moreover have \<open>u \<le> s\<close>
    using u(2) by simp
  ultimately have \<open>u = s\<close>
    by order
  then have s_in: \<open>s \<in>\<^sub>A graph.path_weight su l0 l2\<close>
    using u(1) by simp
  show ?thesis
    by (rule path_weight_singleton_if_lower_bound[OF G s_in lower])
qed

lemma path_weight_self_antichain0:
  fixes su :: \<open>'l::finite \<Rightarrow> 'l \<Rightarrow> 't::{canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} antichain\<close>
  assumes G: \<open>Graph.graph su\<close>
  shows \<open>graph.path_weight su l l = antichain {0}\<close>
proof -
  have empty: \<open>graph.path su l l []\<close>
    by (rule graph.path.intros(1)[OF G], simp)
  show ?thesis
    apply (rule path_weight_singleton_from_path_lower_bound[OF G empty])
     apply simp
    by simp
qed





subsection \<open>Concrete path-weight table for raw_summary\<close>

text \<open>These non-reflexive cases use the minimal accumulated path weight in raw_summary.\<close>

lemma raw_summary_path_to_L1T0_source_cases[simp]:
  assumes p: \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l
    (Loc (1 :: 3) (Trg (0 :: 2))) xs\<close>
  shows \<open>l = Loc (0 :: 3) (Trg (0 :: 2)) \<or>
    l = Loc (0 :: 3) (Src (0 :: 2)) \<or>
    l = Loc (1 :: 3) (Trg (0 :: 2))\<close>
proof -
  have G: \<open>Graph.graph (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)



  show ?thesis using p
  proof (induct xs arbitrary: l rule: rev_induct)
    case Nil
    then show ?case
      using empty_path_inversion[OF _ G] unfolding comp_def by auto
  next
    case (snoc x xs)
    obtain l1 s l2 where x: \<open>x = (l1, s, l2)\<close>
      by (cases x)
    have step: \<open>l2 = Loc (1 :: 3) (Trg (0 :: 2))\<close>
      using snoc.prems x graph.path_AppendE[OF G] by blast
    have edge: \<open>s \<in>\<^sub>A (antichain_from_list \<circ>\<circ> raw_summary) l1 l2\<close>
      using snoc.prems x graph.path_AppendE[OF G] by blast
    have l1: \<open>l1 = Loc (0 :: 3) (Src (0 :: 2))\<close>
      using edge step
      by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
    have path_prefix: \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l l1 xs\<close>
      using snoc.prems x graph.path_AppendE[OF G] by blast
    show ?case
    proof (cases xs rule: rev_cases)
      case Nil
      then show ?thesis
        using path_prefix l1 empty_path_inversion[OF _ G] by auto
    next
      case (snoc ys y)
      obtain l1' s' l2' where y: \<open>y = (l1', s', l2')\<close>
        by (cases y)
      have step': \<open>l2' = Loc (0 :: 3) (Src (0 :: 2))\<close>
        using path_prefix l1 snoc y graph.path_AppendE[OF G] by blast
      have edge': \<open>s' \<in>\<^sub>A (antichain_from_list \<circ>\<circ> raw_summary) l1' l2'\<close>
        using path_prefix snoc y graph.path_AppendE[OF G] by blast
      have l1': \<open>l1' = Loc (0 :: 3) (Trg (0 :: 2))\<close>
        using edge' step'
        by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)

      have path_prefix': \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l l1' ys\<close>
        using path_prefix snoc y graph.path_AppendE[OF G] by blast
      show ?thesis
      proof (cases ys rule: rev_cases)
        case Nil
        then show ?thesis
          using path_prefix' l1' empty_path_inversion[OF _ G] by auto
      next
        case (snoc zs' z1)
        obtain l1'' s'' l2'' where z1: \<open>z1 = (l1'', s'', l2'')\<close>
          by (cases z1)
        have step'': \<open>l2'' = Loc (0 :: 3) (Trg (0 :: 2))\<close>
          using path_prefix' l1' snoc z1 graph.path_AppendE[OF G] by blast
        have edge'': \<open>s'' \<in>\<^sub>A (antichain_from_list \<circ>\<circ> raw_summary) l1'' l2''\<close>
          using path_prefix' snoc z1 graph.path_AppendE[OF G] by blast
        show ?thesis
          using edge'' step''
          by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
      qed

    qed
  qed
qed

lemma raw_summary_path_weight_to_L1T0_empty[simp]:
  assumes \<open>l \<noteq> Loc (0 :: 3) (Trg (0 :: 2))\<close>
    \<open>l \<noteq> Loc (0 :: 3) (Src (0 :: 2))\<close>
    \<open>l \<noteq> Loc (1 :: 3) (Trg (0 :: 2))\<close>
  shows \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary) l
    (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
proof -
  have G: \<open>Graph.graph (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  show ?thesis
    apply (subst ac_eq_iff)
    apply safe
    subgoal for x
      apply (drule graph.path_weight_conv_path[OF G])
      apply clarsimp
      using assms raw_summary_path_to_L1T0_source_cases by blast
    subgoal by simp
    done

qed

lemma raw_summary_path_to_L1T1_source_cases[simp]:
  assumes p: \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l
    (Loc (1 :: 3) (Trg (1 :: 2))) xs\<close>
  shows \<open>l = Loc (0 :: 3) (Trg (0 :: 2)) \<or>
    l = Loc (0 :: 3) (Src (0 :: 2)) \<or>
    l = Loc (1 :: 3) (Trg (0 :: 2)) \<or>
    l = Loc (1 :: 3) (Src (1 :: 2)) \<or>
    l = Loc (2 :: 3) (Trg (1 :: 2)) \<or>
    l = Loc (2 :: 3) (Src (1 :: 2)) \<or>
    l = Loc (1 :: 3) (Trg (1 :: 2))\<close>
proof -
  have G: \<open>Graph.graph (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  show ?thesis using p
  proof (induct xs arbitrary: l rule: length_induct)
    case (1 xs)
    show ?case
    proof (cases xs rule: rev_cases)
      case Nil
      have \<open>l = Loc (1 :: 3) (Trg (1 :: 2))\<close>
        using 1(2) Nil empty_path_inversion[OF _ G] by blast
      then show ?thesis by simp
    next
      case (snoc ys y)
      obtain l1 s l2 where y: \<open>y = (l1, s, l2)\<close>
        by (cases y)
      have step: \<open>l2 = Loc (1 :: 3) (Trg (1 :: 2))\<close>
        using 1(2) snoc y graph.path_AppendE[OF G] by blast
      have edge: \<open>s \<in>\<^sub>A (antichain_from_list \<circ>\<circ> raw_summary) l1 l2\<close>
        using 1(2) snoc y graph.path_AppendE[OF G] by blast
      have l1: \<open>l1 = Loc (2 :: 3) (Src (1 :: 2))\<close>
        using edge step
        by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
      have path_prefix: \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l l1 ys\<close>
        using 1(2) snoc y graph.path_AppendE[OF G] by blast
      show ?thesis
      proof (cases ys rule: rev_cases)
        case Nil
        then have \<open>l = Loc (2 :: 3) (Src (1 :: 2))\<close>
          using path_prefix l1 empty_path_inversion[OF _ G] by blast
        then show ?thesis by simp
      next
        case (snoc zs z)
        obtain l1' s' l2' where z: \<open>z = (l1', s', l2')\<close>
          by (cases z)
        have step': \<open>l2' = Loc (2 :: 3) (Src (1 :: 2))\<close>
          using path_prefix l1 snoc z graph.path_AppendE[OF G] by blast
        have edge': \<open>s' \<in>\<^sub>A (antichain_from_list \<circ>\<circ> raw_summary) l1' l2'\<close>
          using path_prefix snoc z graph.path_AppendE[OF G] by blast
        have l1': \<open>l1' = Loc (2 :: 3) (Trg (1 :: 2))\<close>
          using edge' step'
          by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
        have path_prefix': \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l l1' zs\<close>
          using path_prefix snoc z graph.path_AppendE[OF G] by blast
        show ?thesis
        proof (cases zs rule: rev_cases)
          case Nil
          then have \<open>l = Loc (2 :: 3) (Trg (1 :: 2))\<close>
            using path_prefix' l1' empty_path_inversion[OF _ G] by blast
          then show ?thesis by simp
        next
          case (snoc ws w)
          obtain l1'' s'' l2'' where w: \<open>w = (l1'', s'', l2'')\<close>
            by (cases w)
          have step'': \<open>l2'' = Loc (2 :: 3) (Trg (1 :: 2))\<close>
            using path_prefix' l1' snoc w graph.path_AppendE[OF G] by blast
          have edge'': \<open>s'' \<in>\<^sub>A (antichain_from_list \<circ>\<circ> raw_summary) l1'' l2''\<close>
            using path_prefix' snoc w graph.path_AppendE[OF G] by blast
          have l1'': \<open>l1'' = Loc (1 :: 3) (Src (1 :: 2))\<close>
            using edge'' step''
            by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
          have path_prefix'': \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l l1'' ws\<close>
            using path_prefix' snoc w graph.path_AppendE[OF G] by blast
          show ?thesis
          proof (cases ws rule: rev_cases)
            case Nil
            then have \<open>l = Loc (1 :: 3) (Src (1 :: 2))\<close>
              using path_prefix'' l1'' empty_path_inversion[OF _ G] by blast
            then show ?thesis by simp
          next
            case (snoc vs v)
            obtain l1''' s''' l2''' where v: \<open>v = (l1''', s''', l2''')\<close>
              by (cases v)
            have step''': \<open>l2''' = Loc (1 :: 3) (Src (1 :: 2))\<close>
              using path_prefix'' l1'' snoc v graph.path_AppendE[OF G] by blast
            have edge''': \<open>s''' \<in>\<^sub>A (antichain_from_list \<circ>\<circ> raw_summary) l1''' l2'''\<close>
              using path_prefix'' snoc v graph.path_AppendE[OF G] by blast
            have l1'''_cases:
              \<open>l1''' = Loc (1 :: 3) (Trg (0 :: 2)) \<or>
               l1''' = Loc (1 :: 3) (Trg (1 :: 2))\<close>
              using edge''' step'''
              by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
            have path_prefix''': \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l l1''' vs\<close>
              using path_prefix'' snoc v graph.path_AppendE[OF G] by blast


            have vs_short: \<open>length vs < length xs\<close>
              using snoc \<open>xs = ys @ [y]\<close> \<open>ys = zs @ [z]\<close> \<open>zs = ws @ [w]\<close> \<open>ws = vs @ [v]\<close> by simp
            consider (l1t0) \<open>l1''' = Loc (1 :: 3) (Trg (0 :: 2))\<close> |
              (l1t1) \<open>l1''' = Loc (1 :: 3) (Trg (1 :: 2))\<close>
              using l1'''_cases by blast
            then show ?thesis
            proof cases
              case l1t0
              then show ?thesis
                using path_prefix''' raw_summary_path_to_L1T0_source_cases by blast
            next
              case l1t1
              then have path_to_L1T1: \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l
                (Loc (1 :: 3) (Trg (1 :: 2))) vs\<close>
                using path_prefix''' by simp
              then show ?thesis
                using 1(1) vs_short by blast


            qed
          qed
        qed
      qed
    qed
  qed
qed



lemma raw_summary_path_weight_to_L1T1_empty[simp]:
  assumes \<open>l \<noteq> Loc (0 :: 3) (Trg (0 :: 2))\<close>
    \<open>l \<noteq> Loc (0 :: 3) (Src (0 :: 2))\<close>
    \<open>l \<noteq> Loc (1 :: 3) (Trg (0 :: 2))\<close>
    \<open>l \<noteq> Loc (1 :: 3) (Src (1 :: 2))\<close>
    \<open>l \<noteq> Loc (2 :: 3) (Trg (1 :: 2))\<close>
    \<open>l \<noteq> Loc (2 :: 3) (Src (1 :: 2))\<close>
    \<open>l \<noteq> Loc (1 :: 3) (Trg (1 :: 2))\<close>
  shows \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary) l
    (Loc (1 :: 3) (Trg (1 :: 2))) = {}\<^sub>A\<close>
proof -
  have G: \<open>Graph.graph (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  show ?thesis
    apply (subst ac_eq_iff)
    apply safe
    subgoal for x
      apply (drule graph.path_weight_conv_path[OF G])
      apply clarsimp
      using assms raw_summary_path_to_L1T1_source_cases by blast
    subgoal by simp
    done
qed

lemma raw_summary_path_to_L1T1_increment_suffix:
  assumes path_ys: \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l
    (Loc (1 :: 3) (Trg (1 :: 2))) ys\<close>
    and not_dest: \<open>l \<noteq> Loc (1 :: 3) (Trg (1 :: 2))\<close>
    and not_final_source: \<open>l \<noteq> Loc (2 :: 3) (Src (1 :: 2))\<close>
  obtains ys' where \<open>ys = ys' @
    [(Loc (2 :: 3) (Trg (1 :: 2)), MyPair 0 1, Loc (2 :: 3) (Src (1 :: 2))),
     (Loc (2 :: 3) (Src (1 :: 2)), 0, Loc (1 :: 3) (Trg (1 :: 2)))]\<close>
proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> raw_summary\<close>
  let ?l2 = \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>
  have G: \<open>Graph.graph ?su\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  have \<open>ys \<noteq> []\<close>
    using empty_path_inversion[OF _ G] path_ys not_dest by fastforce
  then obtain ys1 l1 s l2 where last: \<open>ys = ys1 @ [(l1, s, l2)]\<close>
    using rev_cases surj_pair by metis
  have last_props: \<open>l2 = ?l2 \<and> graph.path ?su l l1 ys1 \<and> s \<in>\<^sub>A ?su l1 l2\<close>
    using path_ys last graph.path_AppendE[OF G] by blast
  then have final_edge: \<open>l1 = Loc (2 :: 3) (Src (1 :: 2)) \<and> s = 0\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
      (insert set_antichain2 set_antichain_antichain_singleton, blast)
  have \<open>ys1 \<noteq> []\<close>
    using empty_path_inversion[OF _ G] last_props final_edge not_final_source by fastforce
  then obtain ys' l1' s' l2' where prev: \<open>ys1 = ys' @ [(l1', s', l2')]\<close>
    using rev_cases surj_pair by metis
  have prev_props: \<open>l2' = l1 \<and> graph.path ?su l l1' ys' \<and> s' \<in>\<^sub>A ?su l1' l2'\<close>
    using last_props prev graph.path_AppendE[OF G] by blast
  then have prev_edge: \<open>l1' = Loc (2 :: 3) (Trg (1 :: 2)) \<and> s' = MyPair 0 1\<close>
    using final_edge
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def split: if_splits)
      (insert set_antichain2 set_antichain_antichain_singleton, blast)
  show ?thesis
    using that last prev final_edge prev_edge prev_props last_props by simp
qed

lemma raw_summary_path_to_L1T1_increment_lower_bound:
  assumes path_ys: \<open>graph.path (antichain_from_list \<circ>\<circ> raw_summary) l
    (Loc (1 :: 3) (Trg (1 :: 2))) ys\<close>
    and not_dest: \<open>l \<noteq> Loc (1 :: 3) (Trg (1 :: 2))\<close>
    and not_final_source: \<open>l \<noteq> Loc (2 :: 3) (Src (1 :: 2))\<close>
  shows \<open>MyPair 0 1 \<le> graph.sum_path_weights ys\<close>
proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> raw_summary\<close>
  have G: \<open>Graph.graph ?su\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  obtain ys' where suffix: \<open>ys = ys' @
    [(Loc (2 :: 3) (Trg (1 :: 2)), MyPair 0 1, Loc (2 :: 3) (Src (1 :: 2))),
     (Loc (2 :: 3) (Src (1 :: 2)), 0, Loc (1 :: 3) (Trg (1 :: 2)))]\<close>
    using raw_summary_path_to_L1T1_increment_suffix[OF path_ys not_dest not_final_source] by blast
  hence \<open>[(Loc (2 :: 3) (Trg (1 :: 2)), MyPair 0 1, Loc (2 :: 3) (Src (1 :: 2))),
     (Loc (2 :: 3) (Src (1 :: 2)), 0, Loc (1 :: 3) (Trg (1 :: 2)))] \<preceq> ys\<close>
    by blast
  thus ?thesis
    using graph.subseq_sum_path_weights_le[OF G] subseq_map by fastforce
qed

lemma path_weight_raw_summary_L0T0_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = antichain {0}\<close>
proof -
  have G: \<open>Graph.graph (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  have first: \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Trg (0 :: 2))) (Loc (0 :: 3) (Src (0 :: 2))) = antichain {0}\<close>
    apply (rule path_weight_antichain0[OF G])
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  have zero_in: \<open>0 \<in>\<^sub>A graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2)))\<close>
  proof -
    have \<open>0 \<in>\<^sub>A graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
        (Loc (0 :: 3) (Trg (0 :: 2))) (Loc (0 :: 3) (Src (0 :: 2)))\<close>
      using first by simp
    moreover have \<open>0 \<in>\<^sub>A graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
        (Loc (0 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2)))\<close>
      apply (rule path_weight_direct_0path[OF G])
      by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
    ultimately obtain u where u: \<open>u \<in>\<^sub>A graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
        (Loc (0 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2)))\<close> \<open>u \<le> 0 + 0\<close>
      using graph.path_weight_elem_trans[OF G] by blast
    then show ?thesis by auto
  qed
  show ?thesis
    apply (subst ac_eq_iff)
    apply safe
    subgoal for x
      using G zero_in
      by (metis finite.emptyI finite_insert graph.path_weight_conv_path in_antichain_minimal_antichain minimal_antichain_singleton not_gr_zero singletonI)
    subgoal for x
      using zero_in
      by (metis finite.emptyI finite_insert in_antichain_minimal_antichain minimal_antichain_singleton singleton_iff)
    done
qed

lemma path_weight_raw_summary_L0T1_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Trg (1 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L0S0_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = antichain {0}\<close>
proof -
  have G: \<open>Graph.graph (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)

  show ?thesis
    apply (rule path_weight_antichain0[OF G])
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
qed

lemma path_weight_raw_summary_L1T0_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (1 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = antichain {0}\<close>
proof -
  have G: \<open>Graph.graph (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  show ?thesis
    by (rule path_weight_self_antichain0[OF G])
qed


lemma path_weight_raw_summary_L0S1_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L1T1_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (1 :: 3) (Trg (1 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L1S0_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (1 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L1S1_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (1 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L2T0_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (2 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L2T1_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (2 :: 3) (Trg (1 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L2S0_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (2 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L2S1_L1T0[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (2 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) = {}\<^sub>A\<close>
  by simp



lemma path_weight_raw_summary_L0T1_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Trg (1 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = {}\<^sub>A\<close>
  by simp
lemma path_weight_raw_summary_L0S0_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = antichain {MyPair 0 1}\<close>
proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> raw_summary\<close>
  let ?l1 = \<open>Loc (0 :: 3) (Src (0 :: 2))\<close>
  let ?mid = \<open>Loc (1 :: 3) (Trg (0 :: 2))\<close>
  let ?l2 = \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>
  have G: \<open>Graph.graph ?su\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  have edge0: \<open>0 \<in>\<^sub>A ?su ?l1 ?mid\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  show ?thesis
    apply (rule path_weight_singleton_trans_zero_left[OF G edge0 path_weight_loop_increment])
    subgoal for ys
      using raw_summary_path_to_L1T1_increment_lower_bound[of ?l1 ys]
      by (simp add: location.inject port.distinct)
    done
qed

lemma path_weight_raw_summary_L0T0_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = antichain {MyPair 0 1}\<close>
proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> raw_summary\<close>
  let ?l1 = \<open>Loc (0 :: 3) (Trg (0 :: 2))\<close>
  let ?mid = \<open>Loc (0 :: 3) (Src (0 :: 2))\<close>
  let ?l2 = \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>
  have G: \<open>Graph.graph ?su\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  have edge0: \<open>0 \<in>\<^sub>A ?su ?l1 ?mid\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  have s_in: \<open>MyPair 0 1 \<in>\<^sub>A graph.path_weight ?su ?mid ?l2\<close>
    using path_weight_raw_summary_L0S0_L1T1
    by (metis finite.emptyI finite_insert in_antichain_minimal_antichain minimal_antichain_singleton singleton_iff)
  show ?thesis
    apply (rule path_weight_singleton_trans_zero_left[OF G edge0 s_in])
    subgoal for ys
      using raw_summary_path_to_L1T1_increment_lower_bound[of ?l1 ys]
      by (simp add: location.inject port.distinct)
    done
qed


lemma path_weight_raw_summary_L0S1_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (0 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L1T0_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (1 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = antichain {MyPair 0 1}\<close>
proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> raw_summary\<close>
  let ?l1 = \<open>Loc (1 :: 3) (Trg (0 :: 2))\<close>
  let ?l2 = \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>
  have G: \<open>Graph.graph ?su\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  show ?thesis
    apply (rule path_weight_singleton_if_lower_bound[OF G path_weight_loop_increment])
    subgoal for ys
      using raw_summary_path_to_L1T1_increment_lower_bound[of ?l1 ys]
      by (simp add: location.inject port.distinct)
    done
qed


lemma path_weight_raw_summary_L1S0_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (1 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L1S1_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (1 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = antichain {MyPair 0 1}\<close>
proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> raw_summary\<close>
  let ?l1 = \<open>Loc (1 :: 3) (Src (1 :: 2))\<close>
  let ?mid1 = \<open>Loc (2 :: 3) (Trg (1 :: 2))\<close>
  let ?mid2 = \<open>Loc (2 :: 3) (Src (1 :: 2))\<close>
  let ?l2 = \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>
  let ?xs = \<open>[(?l1, 0, ?mid1), (?mid1, MyPair 0 1, ?mid2), (?mid2, 0, ?l2)]\<close>
  have G: \<open>Graph.graph ?su\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  have edge1: \<open>0 \<in>\<^sub>A ?su ?l1 ?mid1\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  have edge2: \<open>MyPair 0 1 \<in>\<^sub>A ?su ?mid1 ?mid2\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton)
  have edge3: \<open>0 \<in>\<^sub>A ?su ?mid2 ?l2\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  have path_xs: \<open>graph.path ?su ?l1 ?l2 ?xs\<close>
    by (intro path_ConsI[OF G] graph.path.intros(1)[OF G] edge1 edge2 edge3; simp)
  have sum_xs: \<open>graph.sum_path_weights ?xs = MyPair 0 1\<close>
    by simp
  show ?thesis
    apply (rule path_weight_singleton_from_path_lower_bound[OF G path_xs sum_xs])
    subgoal for ys
      using raw_summary_path_to_L1T1_increment_lower_bound[of ?l1 ys]
      by (simp add: location.inject port.distinct)
    done
qed


lemma path_weight_raw_summary_L2T0_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (2 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L2T1_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (2 :: 3) (Trg (1 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = antichain {MyPair 0 1}\<close>
proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> raw_summary\<close>
  let ?l1 = \<open>Loc (2 :: 3) (Trg (1 :: 2))\<close>
  let ?mid = \<open>Loc (2 :: 3) (Src (1 :: 2))\<close>
  let ?l2 = \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>
  let ?xs = \<open>[(?l1, MyPair 0 1, ?mid), (?mid, 0, ?l2)]\<close>
  have G: \<open>Graph.graph ?su\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  have edge1: \<open>MyPair 0 1 \<in>\<^sub>A ?su ?l1 ?mid\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton)
  have edge2: \<open>0 \<in>\<^sub>A ?su ?mid ?l2\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
  have path_xs: \<open>graph.path ?su ?l1 ?l2 ?xs\<close>
    by (intro path_ConsI[OF G] graph.path.intros(1)[OF G] edge1 edge2; simp)
  have sum_xs: \<open>graph.sum_path_weights ?xs = MyPair 0 1\<close>
    by simp
  show ?thesis
    apply (rule path_weight_singleton_from_path_lower_bound[OF G path_xs sum_xs])
    subgoal for ys
      using raw_summary_path_to_L1T1_increment_lower_bound[of ?l1 ys]
      by (simp add: location.inject port.distinct)
    done
qed



lemma path_weight_raw_summary_L2S0_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (2 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = {}\<^sub>A\<close>
  by simp

lemma path_weight_raw_summary_L2S1_L1T1[simp]:
  \<open>graph.path_weight (antichain_from_list \<circ>\<circ> raw_summary)
      (Loc (2 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) = antichain {0}\<close>
proof -
  have G: \<open>Graph.graph (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    by standard (auto simp add: raw_summary_def antichain_from_list_singleton intro: add_mono)
  show ?thesis
    apply (rule path_weight_antichain0[OF G])
    by (simp add: raw_summary_def antichain_from_list_singleton zero_myprod_def)
qed


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


lemma reachable_locations_raw_summary[simp]:
  "reachable_locations (antichain_from_list \<circ>\<circ> raw_summary) = (UNIV :: (3, 2) location set)"
  unfolding reachable_locations_def UNIV_3_2
  apply (clarsimp del: disjCI simp add: UNIV_3_2 split: prod.splits)
  apply (intro subsetI equalityI)  
  subgoal for l
    using loc_3_2_cases[of l]
    by simp
  subgoal for l
    using loc_3_2_cases[of l] apply -
    apply (simp add: raw_summary_def)
    apply fastforce
    done
  done

lemma raw_summary_no_self_loop[simp]:
  "\<forall>loc. (antichain_from_list \<circ>\<circ> raw_summary) (loc :: (3, 2) location) loc = {}\<^sub>A"
  apply (intro allI)
  subgoal for l
    using loc_3_2_cases[of l] apply -
    unfolding raw_summary_def
    apply simp
    apply blast
    done
  done


lemma Inr_2_1_in_ran[simp]:
  "Inr (2 :: 3, 1 :: 2) \<in> ran (case_sum (\<lambda>_. None) (\<lambda>(nid, p). case if nid = 1 \<and> p = 1 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (Inr (1 + 1 + offset, q))))"
  unfolding ran_def
  by (auto split: sum.splits if_splits)

find_consts "_ list \<Rightarrow> _ cset"

(* FIXME: move me to operator states *)
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

lemma MyPair_zero_zero_sum2[simp]:
  "a -+- MyPair 0 0 = a"
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




lemma exit_scope_ifrontier_L1T0_le_L1T1_empty_loop:
  fixes c :: \<open>((3, 2) location, (nat, nat) myprod) configuration\<close>
  assumes D: \<open>dataflow_topology
    (antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list))
    (((-+-) :: (nat, nat) myprod \<Rightarrow> (nat, nat) myprod \<Rightarrow> (nat, nat) myprod))\<close>

and empty_L1S1:
\<open>c_pts c (Loc (1 :: 3) (Src (1 :: 2))) = {#}\<^sub>z\<close>
and empty_L2T1:
\<open>c_pts c (Loc (2 :: 3) (Trg (1 :: 2))) = {#}\<^sub>z\<close>
and empty_L2S1:
\<open>c_pts c (Loc (2 :: 3) (Src (1 :: 2))) = {#}\<^sub>z\<close>
and empty_L1T1:
\<open>c_pts c (Loc (1 :: 3) (Trg (1 :: 2))) = {#}\<^sub>z\<close>
shows \<open>exit_scope myfst (ifrontier
      (antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list))
      (-+-) c (Loc 1 (Trg 0)))
    \<le> exit_scope myfst (ifrontier
      (antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list))
      (-+-) c (Loc 1 (Trg 1)))\<close>

proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list)\<close>

  let ?L0T0 = \<open>Loc (0 :: 3) (Trg (0 :: 2))\<close>
  let ?L0S0 = \<open>Loc (0 :: 3) (Src (0 :: 2))\<close>
  let ?L1T0 = \<open>Loc (1 :: 3) (Trg (0 :: 2))\<close>
  let ?L1S1 = \<open>Loc (1 :: 3) (Src (1 :: 2))\<close>
  let ?L2T1 = \<open>Loc (2 :: 3) (Trg (1 :: 2))\<close>
  let ?L2S1 = \<open>Loc (2 :: 3) (Src (1 :: 2))\<close>
  let ?L1T1 = \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>

  have rhs_member_to_lhs_fle:
    \<open>frontier_less_equal (exit_scope myfst (ifrontier ?su (-+-) c ?L1T0)) y\<close>
    if y_in: \<open>y \<in>\<^sub>A exit_scope myfst (ifrontier ?su (-+-) c ?L1T1)\<close> for y :: nat
  proof -
    obtain a :: \<open>(nat, nat) myprod\<close> where
      a_in: \<open>a \<in>\<^sub>A ifrontier ?su (-+-) c ?L1T1\<close> and y_eq: \<open>myfst a = y\<close>
      using y_in by (rule exit_scope_memberE)
    have rhs_fle: \<open>frontier_less_equal (ifrontier ?su (-+-) c ?L1T1) a\<close>
      using a_in unfolding frontier_less_equal_iff2 by blast
    have decomp:
      \<open>\<exists>l s t. s \<in>\<^sub>A graph.path_weight ?su l ?L1T1 \<and>
        frontier_less_equal (frontier (c_pts c l)) t \<and> a = t -+- s\<close>
      apply (rule frontier_less_equal_ifrontierE[where su = ?su and c = c and l' = ?L1T1 and t = a])
      apply (rule rhs_fle)
      apply (rule D)
      done
    obtain l :: \<open>(3, 2) location\<close> and s :: \<open>(nat, nat) myprod\<close> and t :: \<open>(nat, nat) myprod\<close> where
      s_in: \<open>s \<in>\<^sub>A graph.path_weight ?su l ?L1T1\<close>
      and source_fle: \<open>frontier_less_equal (frontier (c_pts c l)) t\<close>
      and a_eq: \<open>a = t -+- s\<close>
      using decomp by blast

    have loc_cases:
      \<open>l = ?L0T0 \<or> l = ?L0S0 \<or> l = ?L1T0 \<or>
       l = ?L1S1 \<or> l = ?L2T1 \<or> l = ?L2S1 \<or> l = ?L1T1\<close>
      using loc_3_2_cases[of l] s_in by auto
    consider (base) \<open>l = ?L0T0 \<or> l = ?L0S0 \<or> l = ?L1T0\<close> |
      (empty) \<open>l = ?L1S1 \<or> l = ?L2T1 \<or> l = ?L2S1 \<or> l = ?L1T1\<close>
      using loc_cases by blast
    then show ?thesis
    proof cases
      case base
      have zero_in: \<open>(0 :: (nat, nat) myprod) \<in>\<^sub>A graph.path_weight ?su l ?L1T0\<close>
        using base by auto
      have lhs_fle0: \<open>frontier_less_equal (ifrontier ?su (-+-) c ?L1T0) (t -+- 0)\<close>
        using frontier_less_equal_ifrontierI[where su = ?su and c = c and l = l
            and l' = ?L1T0 and t = t and t' = \<open>0 :: (nat, nat) myprod\<close>]
          D zero_in source_fle
        by blast
      have lhs_fle: \<open>frontier_less_equal (ifrontier ?su (-+-) c ?L1T0) t\<close>
        using lhs_fle0 by simp
      obtain b :: \<open>(nat, nat) myprod\<close> where
        b_in: \<open>b \<in>\<^sub>A ifrontier ?su (-+-) c ?L1T0\<close> and b_le: \<open>b \<le> t\<close>
        using lhs_fle unfolding frontier_less_equal_iff2 by blast
      have s_eq: \<open>s = MyPair 0 1\<close>
        using base s_in by (auto simp add: member_antichain.rep_eq)
      have myfst_b_le_y: \<open>myfst b \<le> y\<close>
        using myfst_mono[OF b_le] a_eq y_eq s_eq by simp
      have \<open>frontier_less_equal (exit_scope myfst (ifrontier ?su (-+-) c ?L1T0)) (myfst b)\<close>
        using b_in by (rule frontier_less_equal_exit_scopeI)
      then show ?thesis
        using myfst_b_le_y by (rule frontier_less_equal_trans)
    next
      case empty
      then have False
        using source_fle empty_L1S1 empty_L2T1 empty_L2S1 empty_L1T1 by auto
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    unfolding less_eq_antichain_def
  proof safe
    fix y :: nat
    assume y_in: \<open>y \<in>\<^sub>A exit_scope myfst (ifrontier ?su (-+-) c ?L1T1)\<close>
    obtain x :: nat where x_in: \<open>x \<in>\<^sub>A exit_scope myfst (ifrontier ?su (-+-) c ?L1T0)\<close>
      and x_le: \<open>x \<le> y\<close>
      using rhs_member_to_lhs_fle[OF y_in] unfolding frontier_less_equal_iff2 by blast
    show \<open>\<exists>x. x \<in>\<^sub>A exit_scope myfst (ifrontier ?su (-+-) c ?L1T0) \<and> x \<le> y\<close>
      using x_in x_le by blast
  qed
qed

end
