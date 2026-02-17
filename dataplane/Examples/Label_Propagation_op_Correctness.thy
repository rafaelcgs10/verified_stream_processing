theory Label_Propagation_op_Correctness

imports
  Label_Propagation_op
  Ooo_Input_op
  Increment_op
  Dataplane.LList_Haskell_Setup
begin

(* TODO move *)
lemma num2_cases:
  fixes n :: 2 obtains (0) \<open>n = 0\<close> | (1) \<open>n = 1\<close>
proof (cases n)
  case (of_int z)
  then consider \<open>z = 0\<close> | \<open>z = 1\<close> by fastforce
  thus ?thesis using of_int(1) 0 1 by fastforce
qed

abbreviation \<open>initial_state_input lxs \<equiv> \<lparr>
   summar = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda>_. []),
   outpu = (\<lambda>_. []),
   front = Code.abort (STR ''Frontier not initialized'') (\<lambda>_ _. antichain_from_list []),
   ocaps = (\<lambda>_. [])(0 := [\<bottom>]),
   initia = False,
   nfron = False,
   en1 = Inl,
   de1 = projl,
   is_en1 = isl,
   es = (\<lambda>_. LNil)(0 := lxs)
   \<rparr> :: (_, _, _, _) input_state\<close>

abbreviation \<open>initial_state_label_prop \<equiv> \<lparr>
   summar = default_internal_summary,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda>_. []),
   outpu = (\<lambda>_. []),
   front = Code.abort (STR ''Frontier not initialized'') (\<lambda>_ _. antichain_from_list []),
   ocaps = (\<lambda>_. []),
   initia = False,
   nfron = False,
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
   summar = increment_summary inc,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda>_. []),
   outpu = (\<lambda>_. []),
   front = Code.abort (STR ''Frontier not initialized'') (\<lambda>_ _. antichain_from_list []),
   ocaps = (\<lambda>_. []),
   initia = False,
   nfron = False
   \<rparr> :: (_, _, _) operator_state\<close>

abbreviation \<open>logic_map n \<equiv> map_op (case_option (Inl n) (\<lambda>p. Inr (n, p))) (case_option (Inl n) (\<lambda>p. Inr (n, p)))\<close>
abbreviation \<open>comp_map \<equiv> map_op (case_sum id id) (case_sum id id)\<close>

abbreviation \<open>op0 \<equiv> logic_map (0 :: 3) (ooo_input_op {|0 :: 2|} (initial_state_input (llist_of [Data \<bottom> (0, 1)])))\<close>
abbreviation \<open>op1 \<equiv> logic_map (1 :: 3) (label_propagation_op initial_state_label_prop)\<close>
abbreviation \<open>op2 \<equiv> logic_map (2 :: 3) (increment_op (0 :: 2) 0 (MyPair 0 1) (initial_state_increment (MyPair 0 1)))\<close>
abbreviation \<open>cc_op \<equiv> comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  op0
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. []) (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
    op1
    op2))))\<close>

definition \<open>my_summ = (\<lambda>l1 l2.
   if l1 = Loc (0 :: 3) (Trg (0 :: 2)) \<and> l2 = Loc (0 :: 3) (Src (0 :: 2))
   then antichain_from_list [0]
   else if l1 = Loc 0 (Src 0) \<and> l2 = Loc 1 (Trg 0)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 1)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 1)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Src 1) \<and> l2 = Loc 2 (Trg 0)
   then antichain_from_list [0]
   else if l1 = Loc 2 (Trg 0) \<and> l2 = Loc 2 (Src 0)
   then antichain_from_list [MyPair (0 :: nat) (1 :: nat)]
   else if l1 = Loc 2 (Src 0) \<and> l2 = Loc 1 (Trg 1)
   then antichain_from_list [0]
   else {}\<^sub>A)\<close>

abbreviation \<open>test_sg \<equiv> init_subgraph my_summ [(Loc 0 (Src 0), \<bottom>, 1)]\<close>
abbreviation \<open>debug_test_sg f \<equiv> map (\<lambda>(n, p). ((Loc (Rep_bit1 n) (Src (Rep_bit0 p))),
  f (pt_tr test_sg) (Loc n (Src p)))) (List.product Enum.enum Enum.enum)\<close>
value [GHC] \<open>debug_test_sg c_work\<close>
value [GHC] \<open>debug_test_sg c_pts\<close>
value [GHC] \<open>debug_test_sg c_imp\<close>
value [GHC] \<open>map (\<lambda>(n, p). (Loc (Rep_bit1 n) (Src (Rep_bit0 p)), map_option (\<lambda>(n, p). Loc (Rep_bit1 n) (Trg (Rep_bit0 p)))
  (nxt test_sg (n, p)))) (List.product (Enum.enum :: 3 list) (Enum.enum :: 2 list))\<close>

abbreviation \<open>test_P \<equiv> \<lambda>(t :: (nat, nat) myprod). \<forall>n < 2. \<not> frontier_less_equal ({}\<^sub>A :: (nat, nat) myprod antichain) (MyPair (myfst t) n)\<close>
abbreviation \<open>test_output_times \<equiv> filter test_P [MyPair 0 0]\<close>
value [GHC] test_output_times
abbreviation \<open>test_batch \<equiv> map (\<lambda>t. let cap = Cap t (0 :: nat); t1 = myfst t in (Inr [[0, 1]] :: nat \<times> nat + nat list list, cap)) test_output_times\<close>
value [GHC] test_batch
value [GHC] \<open>map (\<lambda>t. Cap t (0 :: nat)) test_output_times @ map (\<lambda>t. Cap t 1) (filter test_P [MyPair 0 0])\<close>

abbreviation \<open>test_op \<equiv> dataflow_op test_sg cc_op\<close>
value [GHC] \<open>check_prefix 10000 [((1, 0), (Inr [[0, 1]], MyPair 0 0))] test_op\<close>

notepad begin
  let ?inc = \<open>MyPair 0 1\<close>
  let ?sg = \<open>test_sg\<lparr>pt_tr := the (propagate_all (summ test_sg) (pt_tr test_sg)), upfro := (upfro test_sg)(0 := False)\<rparr>\<close>
  let ?f0 = \<open>frontier \<circ> (\<lambda>p. c_imp (pt_tr ?sg) (Loc 0 (Trg p)))\<close>
  let ?os0 = \<open>(initial_state_input (llist_of [Data \<bottom> (0, 1)]))\<lparr>front := ?f0, initia := True, nfron := True\<rparr> :: (2, nat \<times> nat + nat buf buf, nat \<times> nat,
    (nat, nat) myprod) input_state\<close>
  let ?sg.1 = \<open>?sg\<lparr>pt_tr := the (propagate_all (summ ?sg) (pt_tr ?sg)), upfro := (upfro ?sg)(1 := False)\<rparr>\<close>
  let ?f1 = \<open>frontier \<circ> (\<lambda>p. c_imp (pt_tr ?sg.1) (Loc 1 (Trg p)))\<close>
  let ?os1 = \<open>initial_state_label_prop\<lparr>front := ?f1, initia := True, nfron := True\<rparr>\<close>
  let ?sg.2 = \<open>?sg.1\<lparr>pt_tr := the (propagate_all (summ ?sg.1) (pt_tr ?sg.1)), upfro := (upfro ?sg.1)(2 := False)\<rparr>\<close>
  let ?f2 = \<open>frontier \<circ> (\<lambda>p. c_imp (pt_tr ?sg.2) (Loc 2 (Trg p)))\<close>
  let ?os2 = \<open>(initial_state_increment ?inc)\<lparr>front := ?f2, initia := True, nfron := True\<rparr>\<close>
  have \<open>step Tau test_op (dataflow_op ?sg (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      op1
      op2))))))\<close>
    apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_map_op)
            apply (unfold ooo_input_op_def)
            apply (rule step_builder_op_Read_None1)
              apply (simp_all add: init_subgraph_def)
    by simp
  also have \<open>step Tau \<dots> (dataflow_op ?sg.1 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1))
      op2))))))\<close>
    apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Inp)
            apply (rule step_Inp_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Inp)
                apply (rule step_map_op)
                 apply (unfold label_propagation_op_def)
                 apply (rule step_builder_op_Read_None1)
                   apply (simp_all add: init_subgraph_def)
    by simp
  also have \<open>step Tau \<dots> (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close>
    apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Inp)
            apply (rule step_Inp_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Inp)
                 apply (rule step_map_op)
                  apply (unfold increment_op_def)
                  apply (rule step_builder_op_Read_None1)
                    apply (simp_all add: init_subgraph_def)
    by simp
  also have \<open>step Tau \<dots> (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} (produce (?os0\<lparr>es := (es ?os0)(0 := LNil)\<rparr>) (Cap (MyPair 0 0) 0) [Inl (0, 1)])))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close> (is \<open>_ (ooo_input_op _ ?os0.1)\<close>)
    apply (rule step_Tau_dataflow_op_Tau_intro)
    apply (rule step_map_op)
     apply (rule step_comp_op_L_Tau)
       apply (rule step_map_op)
        apply (unfold ooo_input_op_def)
        apply (rule step_builder_op_Silent)
    by (simp_all add: produce_def ooo_input_op_logic_def bot_myprod_def bot_nat_def)
  also have \<open>step Tau \<dots> (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} (drop_caps ?os0.1 (map (\<lambda>t. Cap t 0) (ocaps ?os0.1 0)))))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close> (is \<open>_ (ooo_input_op _ ?os0.2)\<close>)
    apply (rule step_Tau_dataflow_op_Tau_intro)
    apply (rule step_map_op)
     apply (rule step_comp_op_L_Tau)
       apply (rule step_map_op)
        apply (unfold ooo_input_op_def)
        apply (rule step_builder_op_Silent)
    by (simp_all add: produce_def drop_caps_def ooo_input_op_logic_def)
  also have \<open>step Tau \<dots> (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (BENQ (Inr (1, 0)) (Inr (Inl (0, 1), MyPair 0 0)) (\<lambda>_. []))
  (logic_map 0 (ooo_input_op {|0|} (?os0.2\<lparr>outpu := (outpu ?os0.2)(0 := [])\<rparr>)))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close> (is \<open>_ (ooo_input_op _ ?os0.3)\<close>)
    apply (rule step_Tau_dataflow_op_Tau_intro)
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_L)
        apply (rule step_map_op)
         apply (unfold ooo_input_op_def)
         apply (rule step_builder_op_Write_Some)
             apply (simp_all add: produce_def drop_caps_def)
    by simp_all
  also have \<open>step Tau \<dots> (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0.3))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op (consumes ?os1 0 (MyPair 0 0) (Inl (0, 1)))))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close> (is \<open>_ (label_propagation_op ?os1.1)\<close>)
    apply (rule step_Tau_dataflow_op_Tau_intro)
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_R)
          apply (rule step_Inp_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Inp)
              apply (rule step_map_op)
               apply (unfold label_propagation_op_def)
               apply (rule step_builder_op_Read_Some)
                  apply simp_all
    by simp_all
  finally have wstep_Tau_1: \<open>wstep Tau test_op (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0.3))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1.1))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close>
    by simp
  let ?os1.2 = \<open>drop_cap (?os1.1\<lparr>input := (\<lambda>_. []), timestamps := [0],
  graph := (\<lambda>_ _. [])(0 := (\<lambda>_. [])(0 := [1], 1 := [0])), vertices := (\<lambda>_. [])(0 := [0, 1]),
  label := update_label ?os1.1 0 1 0\<rparr>) (Cap (MyPair 0 0) 1)\<close>
  have step_Tau_1: \<open>step Tau (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0.3))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1.1))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))
  (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
    (logic_map 0 (ooo_input_op {|0|} ?os0.3))
    (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
      (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
        (logic_map 1 (label_propagation_op ?os1.2))
        (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close>
    apply (rule step_Tau_dataflow_op_Tau_intro)
    apply (rule step_map_op)
     apply (rule step_comp_op_R_Tau)
       apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Tau)
           apply (rule step_map_op)
            apply (unfold label_propagation_op_def)
            apply (rule step_builder_op_Silent)
                apply (simp_all add: consumes_def add_caps_def drop_cap_def default_internal_summary_def)
    apply (unfold label_propagation_op_logic_def)
    by (simp add: drop_cap_def produces_def neighbors_def BENQ_def insort_union_def insort_insert_key_def)
  let ?os0.4 = \<open>fst (obtain_progress ?os0.3)\<close>
  let ?st0 = \<open>snd (obtain_progress ?os0.3)\<close>
  let ?sg.3 = \<open>?sg.2\<lparr>upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ ?sg.2) (extract_progress 0 (nxt ?sg.2) ?st0) (pt_tr ?sg.2)\<rparr>\<close>
  have step_Tau_2: \<open>step Tau (dataflow_op ?sg.2 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0.3))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1.2))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))
  (dataflow_op ?sg.3 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
    (logic_map 0 (ooo_input_op {|0|} ?os0.4))
    (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
      (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
        (logic_map 1 (label_propagation_op ?os1.2))
        (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close>
    apply (rule step_Tau_dataflow_op_Out_Inl_intro)
     apply (rule step_map_op)
    apply (rule step_comp_op_L_Out)
    apply (rule step_map_op)
    apply (unfold ooo_input_op_def)
    apply (rule step_builder_op_Write_None)
              apply (simp_all add: drop_caps_def produce_def has_progress_def obtain_progress_def)
    by simp
  let ?os1.3 = \<open>fst (obtain_progress ?os1.2)\<close>
  let ?st1 = \<open>snd (obtain_progress ?os1.2)\<close>
  let ?sg.4 = \<open>?sg.3\<lparr>upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ ?sg.3) (extract_progress 1 (nxt ?sg.3) ?st1) (pt_tr ?sg.3)\<rparr>\<close>
  have step_Tau_3: \<open>step Tau (dataflow_op ?sg.3 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0.4))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1.2))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))
  (dataflow_op ?sg.4 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
    (logic_map 0 (ooo_input_op {|0|} ?os0.4))
    (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
      (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
        (logic_map 1 (label_propagation_op ?os1.3))
        (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close>
    apply (rule step_Tau_dataflow_op_Out_Inl_intro)
     apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
        apply (rule step_Out_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Out)
              apply (rule step_map_op)
               apply (unfold label_propagation_op_def)
               apply (rule step_builder_op_Write_None)
                   apply (simp_all add: drop_cap_def consumes_def add_caps_def has_progress_def obtain_progress_def)
    by simp
  let ?sg.5 = \<open>?sg.4\<lparr>pt_tr := the (propagate_all (summ ?sg.4) (pt_tr ?sg.4)), upfro := (upfro ?sg.4)(1 := False)\<rparr>\<close>
  let ?f1.1 = \<open>frontier \<circ> (\<lambda>p. c_imp (pt_tr ?sg.5) (Loc 1 (Trg p)))\<close>
  let ?os1.4 = \<open>?os1.3\<lparr>front := ?f1.1, nfron := \<forall>p. ?f1.1 p \<noteq> front ?os1.3 p\<rparr>\<close>
  have step_Tau_4: \<open>step Tau \<dots> (dataflow_op ?sg.5 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0.4))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1.4))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close>
    apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Inp)
            apply (rule step_Inp_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Inp)
                apply (rule step_map_op)
                 apply (unfold label_propagation_op_def)
                 apply (rule step_builder_op_Read_None2[where f=\<open>?f1.1\<close>])
                    apply (simp_all add: obtain_progress_def drop_cap_def consumes_def add_caps_def)
    by simp
  (* value [GHC] \<open>front ?os1.4 0 + front ?os1.4 1\<close> *)
  (* RESULT "antichain {}" :: "(nat, nat) myprod antichain" *)
  let ?os1.5 = \<open>drop_caps (produces ?os1.4 [(Inr [[0, 1]], Cap (MyPair 0 0) 0)]) [Cap (MyPair 0 0) 0, Cap (MyPair 0 0) 1]\<close>
  have \<open>step Tau (dataflow_op ?sg.5 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
  (logic_map 0 (ooo_input_op {|0|} ?os0.4))
  (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
    (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
      (logic_map 1 (label_propagation_op ?os1.4))
      (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))
  (dataflow_op ?sg.5 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
    (logic_map 0 (ooo_input_op {|0|} ?os0.4))
    (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
      (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
        (logic_map 1 (label_propagation_op ?os1.5))
        (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close>
    sorry
(*
  also have \<open>step (Out (1, 0) (Inr [[0, 1]], MyPair 0 0)) \<dots>
    (dataflow_op ?sg.5 (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>_. [])
    (logic_map 0 (ooo_input_op {|0|} ?os0.4))
    (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>_. [])
      (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>_. [])
        (logic_map 1 (label_propagation_op (?os1.5\<lparr>outpu := (outpu ?os1.5)(0 := [])\<rparr>)))
        (logic_map 2 (increment_op 0 0 ?inc ?os2))))))))\<close>
    sorry
*)
end

end
lemma ooo_input_op_label_propagation_op_increment_op_source_op:
  defines \<open>invariant inc os1 buf1 os2 buf2 os3 buf3 \<equiv> initia os1 \<and> timely_input_stream (es os1 0) (mset (ocaps os1 0))
  \<and> (\<forall>x \<in> set (buf1 (Inr (1, 0))) \<union> set (buf2 (Inr (2, 0))) \<union> set (buf3 (Inr (1, 1))). is_Inr x)
  \<and> initia os2 \<and> summar os2 = default_internal_summary \<and> initia os3 \<and> summar os3 0 0 = [inc] \<and> ocaps os3 0 = map (\<lambda>(_, t). t + inc) (input os2 0) \<and> inc > 0\<close>
    and \<open>my_ooo_input_op os \<equiv> map_op
  (case_option (Inl (0 :: 3)) (\<lambda>(p :: 2). Inr (0 :: 3, p))) (case_option (Inl (0 :: 3)) (\<lambda>(p :: 2). Inr (0 :: 3, p)))
  (ooo_input_op {|0 :: 2|} os)\<close>
    and \<open>my_label_propagation_op os' \<equiv> map_op
  (case_option (Inl (1 :: 3)) (\<lambda>(p :: 2). Inr (1 :: 3, p))) (case_option (Inl (1 :: 3)) (\<lambda>(p :: 2). Inr (1 :: 3, p)))
  (label_propagation_op os')\<close>
    and \<open>my_increment_op inc os'' \<equiv> map_op
  (case_option (Inl (2 :: 3)) (\<lambda>(p :: 2). Inr (2 :: 3, p))) (case_option (Inl (2 :: 3)) (\<lambda>(p :: 2). Inr (2 :: 3, p)))
  (increment_op (0 :: 2) (0 :: 2) inc os'')\<close>
    and \<open>my_source_op inc os1 buf1 os2 buf2 os3 buf3 \<equiv> map_op (\<lambda>(p :: 2). (1 :: 3, p)) (\<lambda>(p :: 2). (1 :: 3, p))
    (source_op ((\<lambda>(p :: 2). undefined)))\<close>
  assumes \<open>invariant inc os1 buf1 os2 buf2 os3 buf3\<close>
  shows \<open>dataflow_op sg (map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] buf1
    (my_ooo_input_op os1)
    (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] buf3 (map_op (case_sum id id) (case_sum id id)
      (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] buf2
        (my_label_propagation_op os2)
        (my_increment_op inc os3))))))
  \<approx> my_source_op inc os1 buf1 os2 buf2 os3 buf3\<close>
  using assms(6)
proof (coinduction arbitrary: sg os1 buf1 os2 buf2 os3 rule: wbisim_coinduct_upto'')
  oops

end