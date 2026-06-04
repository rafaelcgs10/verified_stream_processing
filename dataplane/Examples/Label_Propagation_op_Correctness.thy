theory Label_Propagation_op_Correctness

imports
  Label_Propagation_op
  Ooo_Input_op
  Increment_op
  Set_op
  "../Correctness/General"
  "../Correctness/Outputs"
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

(*

abbreviation \<open>test_input1 \<equiv> llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data \<bottom> (0, 1), Data (MyPair 1 0) (3, 4), Data \<bottom> (1, 2), Data (MyPair 2 0) (4, 5)]\<close>
value "list_connections (dataflow_tree_to_graph (G (initial_state_input test_input1) initial_state_label_prop (initial_state_increment (MyPair 0 1))))"
value [GHC] \<open>ltaken 3 (lmap show_Outs (trace_exec (compiled test_input1)))\<close>

abbreviation \<open>test_input2 \<equiv> llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data \<bottom> (1, 2), Data \<bottom> (0, 1), Data (MyPair 1 0) (3, 4), Data (MyPair 2 0) (4, 5), Mint (MyPair 3 0), Data (MyPair 3 0) (2, 3)]\<close>
value [GHC] \<open>ltaken 4 (lmap show_Outs (trace_exec (compiled test_input2)))\<close>

abbreviation \<open>test_input3 \<equiv>
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data \<bottom> (0, 1), Data (MyPair 1 0) (2, 3),
  Mint (MyPair 3 0), Data (MyPair 3 0) (1, 2), Mint (MyPair 4 0), Data (MyPair 4 0) (4, 5), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5)]\<close>
value [GHC] \<open>ltaken 5 (lmap show_Outs (trace_exec (compiled test_input3)))\<close>

abbreviation \<open>test_input4 \<equiv>
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0),Mint (MyPair 3 0),Mint (MyPair 4 0), Mint (MyPair 5 0),
   Data (MyPair 5 0) (3, 5), Data (MyPair 4 0) (4, 5), Data (MyPair 3 0) (1, 2), Data (MyPair 1 0) (2, 3), Data \<bottom> (0, 1)]\<close>
value [GHC] \<open>ltaken 5 (lmap show_Outs (trace_exec (compiled test_input4)))\<close>

abbreviation \<open>test_input5 \<equiv>
  llist_of [Mint (MyPair 1 0), Mint (MyPair 2 0), Data \<bottom> (0, 1), Drop \<bottom>, Data (MyPair 1 0) (2, 3), Drop (MyPair 1 0),
  Mint (MyPair 3 0), Drop (MyPair 2 0), Data (MyPair 3 0) (1, 2), Mint (MyPair 4 0), Drop (MyPair 3 0), Data (MyPair 4 0) (4, 5), Mint (MyPair 5 0),  Drop (MyPair 4 0), Data (MyPair 5 0) (3, 5)]\<close>
value [GHC] \<open>ltaken 5 (lmap show_Outs (trace_exec (compiled test_input5)))\<close>

abbreviation \<open>test_input6 \<equiv>
  llist_of [Mint (MyPair 1 0), Mint (MyPair 4 0), Mint (MyPair 3 0),
   Data (MyPair 3 0) (1, 2), Data (MyPair 4 0) (4, 5), Mint (MyPair 2 0),
   Data \<bottom> (0, 1), Data (MyPair 1 0) (2, 3), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5)]\<close>
value [GHC] \<open>ltaken 5 (lmap show_Outs (trace_exec (compiled test_input6)))\<close>

abbreviation \<open>test_input7 \<equiv>
  llist_of [ Data \<bottom> (0, 6), Mint (MyPair 1 0), Mint (MyPair 4 0), Mint (MyPair 3 0),
   Data (MyPair 3 0) (1, 2), Data (MyPair 4 0) (4, 5), Mint (MyPair 2 0),
   Data \<bottom> (0, 1), Data (MyPair 1 0) (2, 3), Mint (MyPair 5 0), Data (MyPair 5 0) (3, 5), Data (MyPair 5 0) (6, 5)]\<close>
value [GHC] \<open>ltaken 5 (lmap show_Outs (trace_exec (compiled test_input7)))\<close>


abbreviation \<open>test_input8 \<equiv>
  llist_of [Data \<bottom> (0, 6), Mint (MyPair 3 0), Data (MyPair 3 0) (1, 2), Data \<bottom> (0, 1)]\<close>

value [GHC] \<open>ltaken 2 (lmap show_Outs (trace_exec (compiled test_input8)))\<close>

abbreviation \<open>test_input9 \<equiv>
  llist_of [ Data \<bottom> (0, 6), Data \<bottom> (0, 1), Data (MyPair 1 0) (2, 3)]\<close>
value [GHC] \<open>ltaken 2 (lmap show_Outs (trace_exec (compiled test_input9)))\<close>

 *)

context
  fixes edges :: \<open>('a \<times> 'a) set\<close> (\<open>E\<close>)
begin

(* Undirected reachability and connected components *)

definition reachable where
  \<open>reachable x y \<equiv> (x, y) \<in> (E \<union> E\<inverse>)\<^sup>*\<close>

definition is_subcc :: \<open>'a set \<Rightarrow> bool\<close>  where
  \<open>is_subcc S \<equiv> \<forall>x \<in> S. \<forall>y \<in> S. reachable x y\<close>

definition is_cc :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>is_cc S \<equiv> S \<noteq> {} \<and> is_subcc S \<and> (\<forall>S'. S \<subseteq> S' \<and> is_subcc S' \<longrightarrow> S' = S)\<close>

abbreviation ccs :: \<open>'a set set\<close> where
  \<open>ccs \<equiv> {S. is_cc S}\<close>

definition is_ccs :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>is_ccs \<equiv> (=) ccs\<close>

lemma Ex1_is_ccs:
  \<open>Ex1 is_ccs\<close>
  unfolding is_ccs_def by blast

end

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
    subgraph_inv: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close> \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and
    os_inv:
    \<open>os_input = operator_state.extend (os 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
      es = (\<lambda>_. LNil)(0 := lxs)\<rparr>\<close> \<open>input (os 0) = (\<lambda>_. [])\<close> \<open>initia (os 0)\<close>
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    \<open>ty1_check os_input (curry cbufs 0)\<close> \<open>ty2_check os_label_prop (curry cbufs 1)\<close>
    \<open>input_ocaps_inv (os 1)\<close>
    \<open>\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and buffers_inv: \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    and dataplane_inv: \<open>dataplane_tracker_inv os cbufs sg\<close> (*\<open>cbufs (0, 0) = []\<close>*)
    and csets_inv:
    \<open>SP = cimage
      (\<lambda>t. ((1, 0), (Inr (ccs
        (set (icoll (map (\<lambda>(x, t'). Data t' (projl x)) (chns (1, 0)) @@- lxs) t)
        \<union> all_edges os_label_prop (myfst t))), t)))
      (cUn (ts lxs) (cset_from_list (map snd (chns (1, 0)))))\<close>
    \<open>SO = cset_from_list (map (\<lambda>x. ((1, 0), x)) (outpu (os 1) 0))\<close>
    and input_stream_inv: \<open>timely_input_stream lxs (mset (ocaps (os 0) 0))\<close>
  shows \<open>set_op S D (dataflow_op sg (G_op os_input os_label_prop (os 2) chns))
         \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms
proof (coinduction arbitrary: S SO SP D lxs os os_input os_label_prop cbufs chns sg T G V L
    rule: weakBisimWeakUptoBisimCong)
  case SIM1
  note subgraph_inv = SIM1(1,2)
  show ?case (is \<open>wsim ((~) OO \<U> ?R OO (\<approx>)) _ _\<close>)
  proof -
    thm SIM1
    define R where \<open>R = ?R\<close>

    show ?thesis
      using [[goals_limit=16]]
      unfolding R_def[symmetric]
      unfolding wsim_def dataflow_tree_to_operator_def  ooo_input_op_def label_propagation_op_def increment_op_def
      apply simp
      apply (intro allI impI)
      apply ((elim step_dataflow_op_elim step_set_op_elim step_map_op_elim step_comp_op_elim
            step_builder_op_elim conjE; simp only: IO.simps; hypsubst_thin?; (elim step_map_op_elim
              step_comp_op_elim step_loop_op_elim step_builder_op_elim conjE)?), simp_all only: IO.simps;
          clarsimp split: if_splits option.splits dest!: num2_neq simp flip:  ooo_input_op_def label_propagation_op_def increment_op_def; hypsubst_thin?)
                     prefer 7
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
          apply (rule exI[of _ D])
          apply (rule exI[of _ lxs])
          apply (rule exI[of _ "os(1 := drop_caps
                       (produces (release_caps (os 1) 1)
                         (map (\<lambda>t. (en2 os_label_prop
                                      (all_vertices (release_caps os_label_prop 1) t //
                                       {(v1, v2).
                                        v1 \<in> all_vertices (release_caps os_label_prop 1) t \<and>
                                        v2 \<in> all_vertices (release_caps os_label_prop 1) t \<and> min_label (release_caps os_label_prop 1) t v1 = min_label (release_caps os_label_prop 1) t v2}),
                                     Cap (MyPair t 0) 0))
                           (mergesort_remdups
                             (map myfst
                               (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front (release_caps (os 1) 1) 0 + front (release_caps (os 1) 1) 1)) (myfst t))
                                 (ocaps (release_caps (os 1) 1) 0))))))
                       (map (\<lambda>t. Cap t 0)
                         (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front (release_caps (os 1) 1) 0 + front (release_caps (os 1) 1) 1)) (myfst t))
                           (ocaps (release_caps os_label_prop 1) 0)) @
                        map (\<lambda>t. Cap t 1)
                         (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front (release_caps (os 1) 1) 0 + front (release_caps (os 1) 1) 1)) (myfst t))
                           (ocaps (release_caps (os 1) 1) 1))))"])
          apply (rule exI[of _ "drop_caps
                       (produces (release_caps os_label_prop 1)
                         (map (\<lambda>t. (en2 (release_caps os_label_prop 1)
                                      (all_vertices (release_caps os_label_prop 1) t //
                                       {(v1, v2).
                                        v1 \<in> all_vertices (release_caps os_label_prop 1) t \<and>
                                        v2 \<in> all_vertices (release_caps os_label_prop 1) t \<and> min_label (release_caps os_label_prop 1) t v1 = min_label (release_caps os_label_prop 1) t v2}),
                                     Cap (MyPair t 0) 0))
                           (mergesort_remdups
                             (map myfst
                               (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front (release_caps os_label_prop 1) 0 + front (release_caps os_label_prop 1) 1)) (myfst t))
                                 (ocaps (release_caps os_label_prop 1) 0))))))
                       (map (\<lambda>t. Cap t 0)
                         (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front (release_caps os_label_prop 1) 0 + front (release_caps os_label_prop 1) 1)) (myfst t))
                           (ocaps (release_caps os_label_prop 1) 0)) @
                        map (\<lambda>t. Cap t 1)
                         (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front (release_caps os_label_prop 1) 0 + front (release_caps os_label_prop 1) 1)) (myfst t))
                           (ocaps (release_caps os_label_prop 1) 1)))"])
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ sg])
          apply (intro conjI)
          subgoal
            apply simp
            apply (simp add: dataflow_tree_to_operator_def SIM1(3))
            apply (rule arg_cong3[where f=set_op])
              apply simp
             apply simp
            apply (rule arg_cong2[where f=dataflow_op])
             apply simp
            apply (rule arg_cong[where f=comp_map])
            apply (rule arg_cong4[where f=comp_op])
               apply simp
              apply (simp add: SIM1(11))
            subgoal premises aux
              apply (rule ext)+
              unfolding BULK_BENQ_def
              apply (simp add: operator_state.defs)
              apply (rule arg_cong2[where f=append])
              subgoal
                apply (rule map_cong)
                 apply simp_all
                unfolding drop_caps_def produces_def release_caps_def inputs_at_target_def
                apply (simp split: prod.splits)
                done
              subgoal
                apply (rule arg_cong2[where f=append])
                subgoal
                  by simp
                subgoal
                  apply (rule map_cong)
                   apply (simp_all add: SIM1(1) outputs_at_target_raw_summary release_caps_def filter_empty_conv)
                  done
                done
              done
            subgoal by simp
            subgoal
              apply (rule arg_cong3[where f=loop_op])
                apply simp
              subgoal premises aux
                by (auto cong: map_cong simp add: BULK_BENQ_def SIM1(11) drop_caps_def produces_def inputs_at_target_def operator_state.defs SIM1(1) outputs_at_target_raw_summary release_caps_def filter_empty_conv split: sum.splits)
              apply (rule arg_cong[where f=comp_map])
              apply (rule arg_cong4[where f=comp_op])
                 apply simp
              subgoal premises aux
                by (auto cong: map_cong simp add: BULK_BENQ_def SIM1(11) drop_caps_def produces_def inputs_at_target_def operator_state.defs SIM1(1) outputs_at_target_raw_summary release_caps_def filter_empty_conv split: sum.splits)
               apply simp
              apply simp
              done
            done
          subgoal premises aux
            apply (rule arg_cong2[where f=set_spec_op])
            apply (simp_all add: SIM1(13,14))

          find_theorems SP

end
  have "\<exists>op2'. step (Out (n, p) (d, t)) (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S (cinsert ((n, p), d, t) D) (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os_label_prop) (my_increment_op (os 2))))))))) op2'"
    (is \<open>\<exists>_. step _ ?op2 _ \<and> ((~) OO \<U> R OO (\<approx>)) ?op1' _\<close>)
    if "((n, p), d, t) |\<in>| S"
      and "\<not> ((n, p), d, t) |\<in>| D"
    for n :: "3"
      and p :: "2"
      and d :: "nat \<times> nat + nat set set"
      and t :: "(nat, nat) myprod"
  proof -
    have \<open>R ?op1' (set_spec_op (cUn (cUn S SO) SP) (cinsert ((n, p), d, t) D))\<close> unfolding R_def
      by (intro exI conjI) (use SIM1 in \<open>simp_all add: comp_def\<close>)
    thus ?thesis using bisim_refl wbisim_refl wb_upto_b_base step_set_spec_op_intro_Out that by blast
  qed
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (BENQ (1, 0) (Inr (d, t)) (\<lambda>l. map Inr (cbufs l)))) (my_ooo_input_op (os_input\<lparr>outpu := (outpu os_input)(0 := xs)\<rparr>)) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os_label_prop) (my_increment_op (os 2))))))))) op2'"
    if "outpu os_input 0 = (d, t) # xs"
    for d :: "nat \<times> nat + nat set set"
      and t :: "(nat, nat) myprod"
      and xs :: "((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (BTL (1, 0) (\<lambda>l. map Inr (cbufs l)))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op (consumes os_label_prop 0 t d)) (my_increment_op (os 2))))))))) op2'"
    if "cbufs (1, 0) \<noteq> []"
      and "(d, t) = BHD (1, 0) cbufs"
    for d :: "nat \<times> nat + nat set set"
      and t :: "(nat, nat) myprod"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os') (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os_label_prop) (my_increment_op (os 2))))))))) op2'"
    if "initia os_input"
      and "os' |\<in>| ooo_input_op_logic {|0|} os_input"
    for os' :: "(2, nat \<times> nat + nat set set, nat \<times> nat, (nat, nat) myprod) input_state"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (BENQ (2, 0) (Inr (d, t)) (\<lambda>l. map Inr (cbufs l)))) (my_label_propagation_op (os_label_prop \<lparr>outpu := (outpu os_label_prop)(1 := xs)\<rparr>)) (my_increment_op (os 2))))))))) op2'"
    if "outpu os_label_prop 1 = (d, t) # xs"
    for d :: "nat \<times> nat + nat set set"
      and t :: "(nat, nat) myprod"
      and xs :: "((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (BTL (2, 0) (\<lambda>l. map Inr (cbufs l)))) (my_label_propagation_op os_label_prop) (my_increment_op (consumes (os 2) 0 t d))))))))) op2'"
    if "cbufs (2, 0) \<noteq> []"
      and "(d, t) = BHD (2, 0) cbufs"
    for d :: "nat \<times> nat + nat set set"
      and t :: "(nat, nat) myprod"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os') (my_increment_op (os 2))))))))) op2'"
    if "initia os_label_prop"
      and "os' |\<in>| label_propagation_op_logic os_label_prop"
    for os' :: "(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os_label_prop) (my_increment_op os')))))))) op2'"
    if "initia (os 2)"
      and "os' |\<in>| increment_op_logic 0 0 (MyPair 0 1) (os 2)"
    for os' :: "(2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (BTL (1, 1) (\<lambda>l. map Inr (cbufs l)))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op (consumes os_label_prop 1 t d)) (my_increment_op (os 2))))))))) op2'"
    if "cbufs (1, 1) \<noteq> []"
      and "(d, t) = BHD (1, 1) cbufs"
    for d :: "nat \<times> nat + nat set set"
      and t :: "(nat, nat) myprod"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (BENQ (1, 1) (Inr (d, t)) (\<lambda>l. map Inr (cbufs l)))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os_label_prop) (my_increment_op (os 2\<lparr>outpu := (outpu (os 2))(0 := xs)\<rparr>))))))))) op2'"
    if "outpu (os 2) 0 = (d, t) # xs"
    for d :: "nat \<times> nat + nat set set"
      and t :: "(nat, nat) myprod"
      and xs :: "((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 2 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>) (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os_label_prop) (my_increment_op os')))))))) op2'"
    if "(os', st) = obtain_progress (os 2)"
    for st :: "(2, (nat, nat) myprod) shared_state"
      and os' :: "(2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 1 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>) (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os') (my_increment_op (os 2))))))))) op2'"
    if "(os', st) = obtain_progress os_label_prop"
    for st :: "(2, (nat, nat) myprod) shared_state"
      and os' :: "(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 0 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>) (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os') (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op os_label_prop) (my_increment_op (os 2))))))))) op2'"
    if "(os', st) = obtain_progress os_input"
    for st :: "(2, (nat, nat) myprod) shared_state"
      and os' :: "(2, nat \<times> nat + nat set set, nat \<times> nat, (nat, nat) myprod) input_state"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op undefined (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op (os_label_prop \<lparr>front := frontier \<circ> (\<lambda>p. c_imp (pt_tr undefined) (Loc 1 (Trg p))), initia := True\<rparr>)) (my_increment_op (os 2))))))))) op2'"
    if "propagate_all (summ sg) (pt_tr sg) = None"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>pt_tr := c, upfro := (upfro sg)(1 := False)\<rparr>) (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op (os_label_prop \<lparr>front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg p))), initia := True\<rparr>)) (my_increment_op (os 2))))))))) op2'"
    if "propagate_all (summ sg) (pt_tr sg) = Some c"
    for c :: "((3, 2) location, (nat, nat) myprod) configuration"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op (cinsert ((1, 0), d, t) S) D (dataflow_op sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_ooo_input_op os_input) (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (case_sum (\<lambda>x. []) (\<lambda>l. map Inr (cbufs l))) (my_label_propagation_op (os_label_prop \<lparr>outpu := (outpu os_label_prop)(0 := xs)\<rparr>)) (my_increment_op (os 2))))))))) op2'"
    if "outpu os_label_prop 0 = (d, t) # xs"
    for d :: "nat \<times> nat + nat set set"
      and t :: "(nat, nat) myprod"
      and xs :: "((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf"
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
    apply simp
    apply (rule arg_cong[where f=\<open>\<lambda>X. set_spec_op (cUn X SP) D\<close>])
    using SIM1(6,14) that apply (simp add: operator_state.defs(3))
    apply (simp_all add: SIM1 operator_state.defs(3))
    using SIM1(3,7) unfolding ty1_check_def apply (simp add: operator_state.defs(3), blast)
    subgoal
      using SIM1(6,8) that unfolding ty2_check_def apply -
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
    apply (rule SIM1(15))
    apply (rule dataplane_tracker_inv_update_outputs_outside)
    apply (rule SIM1(12))
    unfolding fun_upd_def apply simp
    using SIM1(1) apply (simp add: raw_summary_def)
    sorry
end
  ultimately show ?thesis
    (* takes around 70s *)
    by (use nothing in \<open>((unfold R_def[symmetric], unfold wsim_def my_ooo_input_op_def ooo_input_op_def
          my_label_propagation_op_def label_propagation_op_def my_increment_op_def increment_op_def,
          intro allI impI, elim step_dataflow_op_elim step_set_op_elim step_map_op_elim step_comp_op_elim
          step_builder_op_elim conjE; simp only: IO.simps; hypsubst_thin?; (elim step_map_op_elim
            step_comp_op_elim step_loop_op_elim step_builder_op_elim conjE)?), simp_all only: IO.simps;
        clarsimp split: if_splits option.splits dest!: num2_neq simp flip: my_ooo_input_op_def ooo_input_op_def
          my_label_propagation_op_def label_propagation_op_def my_increment_op_def increment_op_def; hypsubst_thin?),
        use method_facts in simp_all\<close>)
qed
next
  case SIM2
  then show ?case sorry
  oops

end