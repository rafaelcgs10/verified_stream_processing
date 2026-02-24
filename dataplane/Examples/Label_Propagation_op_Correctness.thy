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
   intsum = default_internal_summary,
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
   intsum = (\<lambda>_ _. [0]),
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
   intsum = increment_summary inc,
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

abbreviation \<open>test_input \<equiv> llist_of [Data \<bottom> (0, 1), Data (MyPair 1 0) (3, 4), Data \<bottom> (1, 2), Data (MyPair 2 0) (4, 5)]\<close>
abbreviation \<open>op0 \<equiv> logic_map (0 :: 3) (ooo_input_op {|0 :: 2|} (initial_state_input test_input))\<close>
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
abbreviation \<open>test_op \<equiv> dataflow_op test_sg cc_op\<close>

value [GHC] \<open>trace_exec test_op\<close>

(*
lemma ooo_input_op_label_propagation_op_increment_op_source_op:
  defines \<open>invariant inc os1 buf1 os2 buf2 os3 buf3 \<equiv> initia os1 \<and> timely_input_stream (es os1 0) (mset (ocaps os1 0))
  \<and> (\<forall>x \<in> set (buf1 (Inr (1, 0))) \<union> set (buf2 (Inr (2, 0))) \<union> set (buf3 (Inr (1, 1))). is_Inr x)
  \<and> initia os2 \<and> intsum os2 = default_internal_summary \<and> initia os3 \<and> intsum os3 0 0 = [inc] \<and> ocaps os3 0 = map (\<lambda>(_, t). t + inc) (input os2 0) \<and> inc > 0\<close>
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
*)

end