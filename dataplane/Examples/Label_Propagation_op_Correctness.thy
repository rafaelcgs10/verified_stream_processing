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
  Dataplane.Propagation_Properties
  Dataplane.SimulationProofMethods
begin

abbreviation "loop_wire \<equiv> (case_sum (\<lambda>_. None) (\<lambda>(nid, p). case if nid = 2 \<and> p = 1 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (Inr (1 + offset, q))))"
abbreviation "comp_wire \<equiv> (case_sum (\<lambda>_. None) (\<lambda>(nid, p). case if nid = 1 \<and> p = 1 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (Inr (1 + 1 + offset, q))))"


(* Note: this is basically lemma comp_op_chns_invar from dataplane_dis:dataplane/Comp_Reasoning.thy *)
lemma comp_op_buf_cong:
  assumes \<open>wire' = wire\<close> \<open>op1' = op1\<close> \<open>op2' = op2\<close> \<open>\<forall>p \<in> inputs op2 \<inter> ran wire. buf' p = buf p\<close>
  shows \<open>comp_op wire buf op1 op2 = comp_op wire buf' op1 op2\<close>
  sorry

(* release_caps os p only removes from ocaps p those timestamps that have no matching
   (input, intsum) witness, so input_ocaps_inv is preserved. *)
lemma input_ocaps_inv_release_capsI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (release_caps os p)"
proof -
  let ?M = "concat (map (\<lambda>(p', s). map (((+) s) \<circ> snd) (input os p'))
              (concat (map (\<lambda>p'. map (\<lambda>s. (p', s)) (intsum os p' p)) enum_class.enum)))"
  let ?ts = "list_diff (ocaps os p) ?M"
  have release_eq:
    "release_caps os p = drop_caps os (map (\<lambda>t. Cap t p) ?ts)"
    unfolding release_caps_def Let_def trace_simp by simp
  have ocaps_other:
    "\<And>p'. p' \<noteq> p \<Longrightarrow> ocaps (release_caps os p) p' = ocaps os p'"
    unfolding release_eq drop_caps_def by auto
  have ocaps_p_mset:
    "mset (ocaps (release_caps os p) p) =
       mset (ocaps os p) - mset (list_diff (ocaps os p) ?M)"
    unfolding release_eq drop_caps_def by simp
  show ?thesis
    unfolding input_ocaps_inv_def
  proof (intro allI ballI)
    fix p1 p2 t s
    assume t_in: "t \<in> snd ` set (input (release_caps os p) p1)"
      and s_in: "s \<in> set (intsum (release_caps os p) p1 p2)"
    have t_in': "t \<in> snd ` set (input os p1)"
      using t_in by simp
    have s_in': "s \<in> set (intsum os p1 p2)"
      using s_in by simp
    have orig: "t -+- s \<in> set (ocaps os p2)"
      using inv t_in' s_in' unfolding input_ocaps_inv_def by blast
    show "t -+- s \<in> set (ocaps (release_caps os p) p2)"
    proof (cases "p2 = p")
      case False
      then show ?thesis using orig ocaps_other by simp
    next
      case True
      have plus_eq: "t -+- s = s + t"
        by (simp add: add.commute)
      have in_M: "t -+- s \<in> set ?M"
      proof -
        from t_in' obtain d where d_in: "(d, t) \<in> set (input os p1)"
          by auto
        have p1_enum: "p1 \<in> set enum_class.enum"
          by (simp add: enum_UNIV)
        have pair_in:
          "(p1, s) \<in> set (concat (map (\<lambda>p'. map (\<lambda>s. (p', s)) (intsum os p' p)) enum_class.enum))"
          using p1_enum s_in' True by auto
        have apply_eq: "((+) s \<circ> snd) (d, t) = s + t"
          by simp
        from pair_in apply_eq d_in have "s + t \<in> set ?M"
          by (force simp: image_iff)
        then show ?thesis using plus_eq by simp
      qed
      have count_pos:
        "count (mset (ocaps (release_caps os p) p)) (t -+- s) > 0"
      proof -
        let ?O = "mset (ocaps os p)"
        let ?Mm = "mset ?M"
        have step1: "mset (list_diff (ocaps os p) ?M) = ?O - ?Mm"
          by simp
        have countM: "count ?Mm (t -+- s) > 0"
          using in_M by (simp add: count_greater_zero_iff)
        have countO: "count ?O (t -+- s) > 0"
          using orig True by (simp add: count_greater_zero_iff)
        have "count (?O - (?O - ?Mm)) (t -+- s) > 0"
          using countM countO by simp
        then show ?thesis
          using ocaps_p_mset True step1 by simp
      qed
      then have "t -+- s \<in> set_mset (mset (ocaps (release_caps os p) p))"
        by (simp add: count_greater_zero_iff)
      then show ?thesis
        using True by simp
    qed
  qed
qed

lemma input_ocaps_inv_produces[simp]:
  "input_ocaps_inv (produces os batch) = input_ocaps_inv os"
  unfolding produces_def input_ocaps_inv_def
  by auto

(* add_caps only enlarges ocaps (and leaves input/intsum untouched),
   so any required witness remains present. *)
lemma input_ocaps_inv_add_capsI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (add_caps os caps)"
  unfolding input_ocaps_inv_def
proof (intro allI ballI)
  fix p1 p2 t s
  assume t_in: "t \<in> snd ` set (input (add_caps os caps) p1)"
    and s_in: "s \<in> set (intsum (add_caps os caps) p1 p2)"
  have t_in': "t \<in> snd ` set (input os p1)"
    using t_in unfolding add_caps_def by simp
  have s_in': "s \<in> set (intsum os p1 p2)"
    using s_in unfolding add_caps_def by simp
  have "t -+- s \<in> set (ocaps os p2)"
    using inv t_in' s_in' unfolding input_ocaps_inv_def by blast
  then show "t -+- s \<in> set (ocaps (add_caps os caps) p2)"
    unfolding add_caps_def by auto
qed

(* Adding and then dropping the same caps leaves ocaps unchanged (as multisets,
   hence as sets); input and intsum are untouched throughout, so input_ocaps_inv
   transfers directly. *)
lemma input_ocaps_inv_drop_add_capsI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (drop_caps (add_caps os caps) caps)"
  unfolding input_ocaps_inv_def
proof (intro allI ballI)
  fix p1 p2 t s
  assume t_in: "t \<in> snd ` set (input (drop_caps (add_caps os caps) caps) p1)"
    and s_in: "s \<in> set (intsum (drop_caps (add_caps os caps) caps) p1 p2)"
  have t_in': "t \<in> snd ` set (input os p1)"
    using t_in unfolding drop_caps_def add_caps_def by simp
  have s_in': "s \<in> set (intsum os p1 p2)"
    using s_in unfolding drop_caps_def add_caps_def by simp
  have orig: "t -+- s \<in> set (ocaps os p2)"
    using inv t_in' s_in' unfolding input_ocaps_inv_def by blast
  have ocaps_mset:
    "mset (ocaps (drop_caps (add_caps os caps) caps) p2) = mset (ocaps os p2)"
    unfolding drop_caps_def add_caps_def by simp
  then have set_eq:
    "set (ocaps (drop_caps (add_caps os caps) caps) p2) = set (ocaps os p2)"
    by (metis set_mset_mset)
  show "t -+- s \<in> set (ocaps (drop_caps (add_caps os caps) caps) p2)"
    using orig set_eq by simp
qed

(* Same as input_ocaps_inv_drop_add_capsI, but with produces interposed between
   add_caps and drop_caps. produces only modifies outpu and produ, so input,
   intsum, and ocaps remain untouched. *)
lemma input_ocaps_inv_drop_produces_add_capsI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (drop_caps (produces (add_caps os caps) batch) caps)"
  unfolding input_ocaps_inv_def
proof (intro allI ballI)
  fix p1 p2 t s
  assume t_in: "t \<in> snd ` set (input (drop_caps (produces (add_caps os caps) batch) caps) p1)"
    and s_in: "s \<in> set (intsum (drop_caps (produces (add_caps os caps) batch) caps) p1 p2)"
  have t_in': "t \<in> snd ` set (input os p1)"
    using t_in unfolding drop_caps_def produces_def add_caps_def by simp
  have s_in': "s \<in> set (intsum os p1 p2)"
    using s_in unfolding drop_caps_def produces_def add_caps_def by simp
  have orig: "t -+- s \<in> set (ocaps os p2)"
    using inv t_in' s_in' unfolding input_ocaps_inv_def by blast
  have ocaps_mset:
    "mset (ocaps (drop_caps (produces (add_caps os caps) batch) caps) p2) = mset (ocaps os p2)"
    unfolding drop_caps_def produces_def add_caps_def by simp
  then have set_eq:
    "set (ocaps (drop_caps (produces (add_caps os caps) batch) caps) p2) = set (ocaps os p2)"
    by (metis set_mset_mset)
  show "t -+- s \<in> set (ocaps (drop_caps (produces (add_caps os caps) batch) caps) p2)"
    using orig set_eq by simp
qed

(* label_prop_label_record_update only modifies the label field; input, intsum,
   and ocaps are untouched, so input_ocaps_inv transfers trivially. *)
lemma input_ocaps_inv_label_prop_label_record_updateI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (label_prop_label_record_update os event_t vertex assigned_label)"
  using inv unfolding input_ocaps_inv_def label_prop_label_record_update_def by simp

(* input_tl only drops the head of input os p; the remaining input is a subset of
   the original. intsum and ocaps are untouched, so any witness for an element
   still present transfers. *)
lemma input_ocaps_inv_input_tlI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (input_tl os p)"
  unfolding input_ocaps_inv_def
proof (intro allI ballI)
  fix p1 p2 t s
  assume t_in: "t \<in> snd ` set (input (input_tl os p) p1)"
    and s_in: "s \<in> set (intsum (input_tl os p) p1 p2)"
  have t_in': "t \<in> snd ` set (input os p1)"
    using t_in unfolding input_tl_def
    by (auto split: if_splits dest: in_set_tlD)
  have s_in': "s \<in> set (intsum os p1 p2)"
    using s_in unfolding input_tl_def by simp
  have orig: "t -+- s \<in> set (ocaps os p2)"
    using inv t_in' s_in' unfolding input_ocaps_inv_def by blast
  show "t -+- s \<in> set (ocaps (input_tl os p) p2)"
    using orig unfolding input_tl_def by simp
qed

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

lemma path_weight_introI:
  assumes G: "Graph.graph weights"
    and P: "graph.path weights l1 l2 xs"
    and S: "s = graph.sum_path_weights xs"
    and M: "\<And>(ys :: ('a :: finite \<times> 'b :: {monoid_add,order} \<times> 'a) list). graph.path weights l1 l2 ys \<Longrightarrow> \<not> graph.sum_path_weights ys < s"
  shows "s \<in>\<^sub>A graph.path_weight weights l1 l2"
proof -
  have ms: "s \<in> minimal_antichain {x. graph.path_weightp weights l1 l2 x}"
    unfolding minimal_antichain_def
    using P S M by (auto simp: graph.path_weightp_def[OF G])
  show ?thesis
    using ms graph.in_path_weight[OF G] by blast
qed

lemma loop_path_weight_non_zero:
  "MyPair 0 1 \<in>\<^sub>A graph.path_weight (antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list)) (Loc 1 (Trg 0)) (Loc 1 (Trg 1))"
proof -
  let ?rs = \<open>raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list\<close>
  let ?df = \<open>G (initial_state_input (LNil :: ((nat, nat) myprod, nat \<times> nat) event llist))
    initial_state_label_prop (initial_state_increment (MyPair 0 1))\<close>
  have D0: \<open>dataflow_topology (antichain_from_list \<circ>\<circ> dataflow_tree_to_graph ?df) (-+-)\<close>
    using dataflow_topology_from_tree.dataflow_topology_axioms[of ?df]
    by (simp add: comp_def)
  have raw: \<open>dataflow_tree_to_graph ?df = raw_summary\<close>
    by (rule dataflow_tree_to_graph_raw_summary)
  have G0: \<open>Graph.graph (antichain_from_list \<circ>\<circ> dataflow_tree_to_graph ?df)\<close>
    using dataflow_topology.axioms(1)[OF D0] .
  have graph_eq: \<open>(antichain_from_list \<circ>\<circ> dataflow_tree_to_graph ?df) = (antichain_from_list \<circ>\<circ> raw_summary)\<close>
    using raw by (simp add: comp_def)
  note G = G0[unfolded graph_eq]
  have edge_10_s1: \<open>0 \<in>\<^sub>A (antichain_from_list \<circ>\<circ> raw_summary) (Loc 1 (Trg 0)) (Loc 1 (Src 1))\<close>
    unfolding raw_summary_def comp_def
    by (simp add: antichain_from_list_singleton enum_num1_def zero_myprod_def)
  have edge_s1_21: \<open>0 \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) (Loc 1 (Src 1)) (Loc 2 (Trg 1))\<close>
    unfolding raw_summary_def comp_def
    by (simp add: antichain_from_list_singleton enum_num1_def zero_myprod_def)
  have diff3_01[simp]: \<open>(0 :: 3) \<noteq> 1\<close> \<open>(1 :: 3) \<noteq> 0\<close>
    by (simp_all add: Numeral_Type.bit1.of_int_eq)
  have diff3_12[simp]: \<open>(1 :: 3) \<noteq> 2\<close> \<open>(2 :: 3) \<noteq> 1\<close>
    by (simp_all add: Numeral_Type.bit1.of_int_eq)
  have diff3_02[simp]: \<open>(0 :: 3) \<noteq> 2\<close> \<open>(2 :: 3) \<noteq> 0\<close>
    by (simp_all add: Numeral_Type.bit1.of_int_eq)
  have edge_21_2s1: \<open>MyPair 0 1 \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) (Loc 2 (Trg 1)) (Loc 2 (Src 1))\<close>
    by (simp add: raw_summary_def antichain_from_list_singleton enum_num1_def zero_myprod_def)
  have edge_2s1_11: \<open>0 \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) (Loc 2 (Src 1)) (Loc 1 (Trg 1))\<close>
    unfolding raw_summary_def comp_def
    by (simp add: antichain_from_list_singleton enum_num1_def zero_myprod_def)
  have edge_2s1_11: \<open>0 \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) (Loc 2 (Src 1)) (Loc 1 (Trg 1))\<close>
    unfolding raw_summary_def comp_def
    by (simp add: antichain_from_list_singleton enum_num1_def zero_myprod_def)
  define xs :: "((3, 2) location \<times> (nat, nat) myprod \<times> (3, 2) location) list" where
    "xs = [(Loc 1 (Trg 0), MyPair 0 0, Loc 1 (Src 1)),
           (Loc 1 (Src 1), MyPair 0 0, Loc 2 (Trg 1)),
           (Loc 2 (Trg 1), MyPair 0 1, Loc 2 (Src 1)),
           (Loc 2 (Src 1), MyPair 0 0, Loc 1 (Trg 1))]"
  have path_ex: "graph.path (antichain_from_list \<circ>\<circ> raw_summary) (Loc 1 (Trg 0)) (Loc 1 (Trg 1)) xs"
    unfolding xs_def
    apply (rule path_ConsI[OF G])
     apply (rule path_ConsI[OF G])
      apply (rule path_ConsI[OF G])
       apply (rule path_ConsI[OF G])
        apply (rule graph.path.intros(1)[OF G])
        apply (rule refl)
       apply (rule edge_2s1_11[unfolded zero_myprod_def])
      apply (rule edge_21_2s1)
     apply (rule edge_s1_21[unfolded zero_myprod_def])
    apply (rule edge_10_s1[unfolded zero_myprod_def])
    done
  have sum_eq: "graph.sum_path_weights xs = MyPair 0 1"
    unfolding xs_def by simp
  have lt_imp_mysnd_zero: "\<And>s. s < (MyPair 0 1 :: (nat, nat) myprod) \<Longrightarrow> mysnd s = 0"
    by (case_tac s) (auto simp: less_myprod_def less_eq_myprod_def)
  define S where "S = {Loc 1 (Trg 0) :: (3, 2) location, Loc 1 (Src 0), Loc 1 (Src 1), Loc 2 (Trg 1)}"
  have S_in: "Loc 1 (Trg 0) \<in> S"
    unfolding S_def by simp
  have S_not_T1: "Loc 1 (Trg 1) \<notin> S"
    unfolding S_def by simp
  have diff2_01[simp]: "(0 :: 2) \<noteq> 1" "(1 :: 2) \<noteq> 0"
    by (simp_all add: Numeral_Type.bit0.of_int_eq)
  note rs_simps = raw_summary_def comp_def antichain_from_list_singleton zero_myprod_def enum_num1_def
  have rs_1T0: "\<And>l3 lbl. lbl \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) (Loc 1 (Trg 0)) l3 \<Longrightarrow>
       l3 = Loc 1 (Src 0) \<or> l3 = Loc 1 (Src 1)"
    subgoal for l3 lbl using loc_3_2_cases[of l3]
      by (elim disjE; hypsubst_thin; simp add: rs_simps) done
  have rs_1S0: "\<And>l3 lbl. \<not> lbl \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) (Loc 1 (Src 0)) l3"
    subgoal for l3 lbl using loc_3_2_cases[of l3]
      by (elim disjE; hypsubst_thin; simp add: rs_simps) done
  have rs_1S1: "\<And>l3 lbl. lbl \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) (Loc 1 (Src 1)) l3 \<Longrightarrow>
       l3 = Loc 2 (Trg 1)"
    subgoal for l3 lbl using loc_3_2_cases[of l3]
      by (elim disjE; hypsubst_thin; simp add: rs_simps) done
  have in_antichain_sg: "\<And>x y :: (nat, nat) myprod. x \<in>\<^sub>A antichain {y} \<Longrightarrow> x = y"
    by (metis empty_iff finite.emptyI finite_insert in_antichain_minimal_antichain
        minimal_antichain_singleton singletonD)
  have rs_2T1: "\<And>l3 lbl. lbl \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) (Loc 2 (Trg 1)) l3 \<Longrightarrow>
       mysnd lbl = 1"
    subgoal for l3 lbl using loc_3_2_cases[of l3]
      apply (elim disjE; hypsubst_thin; simp add: rs_simps)
      apply (drule in_antichain_sg; simp)
      done
    done
  have edges_S_step:
    "l2 \<in> S \<Longrightarrow>
         lbl \<in>\<^sub>A (antichain_from_list \<circ>\<circ> ?rs) l2 l3 \<Longrightarrow>
         mysnd lbl = 0 \<Longrightarrow> l3 \<in> S" for l2 lbl l3
    unfolding S_def
    using rs_1T0 rs_1S0 rs_1S1 rs_2T1 by fastforce
  have invariant:
    "graph.path (antichain_from_list \<circ>\<circ> ?rs) (Loc 1 (Trg 0)) l ys \<Longrightarrow>
     mysnd (graph.sum_path_weights ys) = 0 \<Longrightarrow> l \<in> S" for l ys
  proof (induct "Loc 1 (Trg 0) :: (3,2) location" l ys rule: graph.path.induct[OF G, consumes 1])
    case (1 l2)
    show ?case using S_in 1 by simp
  next
    case (2 l2 xs lbl l3)
    have split: "graph.sum_path_weights (xs @ [(l2, lbl, l3)]) = graph.sum_path_weights xs + lbl"
      by (rule graph.sum_path_weights_append_singleton[OF G])
    from 2(4) split have m1: "mysnd (graph.sum_path_weights xs) = 0" and m2: "mysnd lbl = 0"
      by (simp_all add: mysnd_add)
    from 2(2)[OF m1] have l2_in: "l2 \<in> S" .
    show ?case
      by (rule edges_S_step[OF l2_in 2(3) m2])
  qed
  have min_lem: "\<And>ys. graph.path (antichain_from_list \<circ>\<circ> ?rs) (Loc 1 (Trg 0)) (Loc 1 (Trg 1)) ys \<Longrightarrow>
                  \<not> graph.sum_path_weights ys < MyPair 0 1"
  proof
    fix ys assume p: "graph.path (antichain_from_list \<circ>\<circ> ?rs) (Loc 1 (Trg 0)) (Loc 1 (Trg 1)) ys"
    assume lt: "graph.sum_path_weights ys < MyPair 0 1"
    from lt_imp_mysnd_zero[OF lt] have m: "mysnd (graph.sum_path_weights ys) = 0" .
    from invariant[OF p m] have "Loc 1 (Trg 1) \<in> S" .
    with S_not_T1 show False by contradiction
  qed
  have step: "graph.sum_path_weights xs \<in>\<^sub>A graph.path_weight (antichain_from_list \<circ>\<circ> ?rs) (Loc 1 (Trg 0)) (Loc 1 (Trg 1))"
    using path_weight_introI[OF G path_ex HOL.refl] min_lem[unfolded sum_eq[symmetric]]
    by blast
  show ?thesis
    using step sum_eq by simp
qed



(* TODO: Move. *)
lemma un_Choice_loop_op_buf_cong:
  fixes wire
  defines \<open>R \<equiv> (\<lambda>op1 op2. \<exists>buf buf' op. op1 = loop_op wire buf op \<and> op2 = loop_op wire buf' op
  \<and> (\<forall>p. p \<in> inputs (op :: ('i, 'o, 'd) op) \<and> p \<in> ran wire \<longrightarrow> buf' p = buf p))\<close>
  assumes bufs_eq: \<open>\<forall>p \<in> inputs (op :: ('i, 'o, 'd) op) \<inter> ran wire. buf' p = buf p\<close>
    and op': \<open>op' |\<in>| un_Choice (loop_op wire buf op)\<close>
  obtains op'' where \<open>op'' |\<in>| un_Choice (loop_op wire buf' op)\<close> \<open>op.congclp R op' op''\<close>
proof atomize_elim
  consider (read_outside) p f where \<open>op' = Read p (\<lambda>x. loop_op wire buf (f x))\<close>
    \<open>Read p f |\<in>| choices op\<close> \<open>p \<notin> ran wire\<close>
  | (read_inside) p f where \<open>op' = Silent (loop_op wire (BTL p buf) (f (BHD p buf)))\<close>
    \<open>Read p f |\<in>| choices op\<close> \<open>p \<in> ran wire\<close> \<open>buf p \<noteq> []\<close>
  | (write_outside) op'' p x where \<open>op' = Write (loop_op wire buf op'') p x\<close>
    \<open>Write op'' p x |\<in>| choices op\<close> \<open>wire p = None\<close>
  | (write_inside) op'' p x q where \<open>op' = Silent (loop_op wire (BENQ q x buf) op'')\<close>
    \<open>Write op'' p x |\<in>| choices op\<close> \<open>wire p = Some q\<close>
  | (silent) op'' where \<open>op' = Silent (loop_op wire buf op'')\<close>
    \<open>Silent op'' |\<in>| choices op\<close>
    using op' by (subst (asm) (6) loop_op.code)
      (auto split: op.splits option.splits if_splits dest: no_Choice_in_choices[simplified])
  thus \<open>\<exists>op''. op'' |\<in>| un_Choice (loop_op wire buf' op) \<and> op.congclp R op' op''\<close>
  proof cases
    case read_outside
    let ?op'' = \<open>Read p (\<lambda>x. loop_op wire buf' (f x))\<close>
    have \<open>R (loop_op wire buf (f x)) (loop_op wire buf' (f x))\<close> for x unfolding R_def
      using bufs_eq read_outside inputs_after_choices inputs_sub_op_Read mem_simps(4)
        sub_op.intros(2) sub_op_Read_inputs by metis
    hence \<open>op.congclp R op' ?op''\<close>
      using op.cong_base op.cong_Read[OF refl] unfolding rel_fun_def read_outside(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using read_outside(2-) by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  next
    case read_inside
    let ?x = \<open>BHD p buf\<close>
    let ?y = \<open>BHD p buf'\<close>
    let ?op'' = \<open>Silent (loop_op wire (BTL p buf') (f ?y))\<close>
    have \<open>?x = ?y\<close>
      using bufs_eq read_inside(2,3) Read_choices_inputs mem_simps(4) BHD_def by metis
    moreover have \<open>\<forall>p' \<in> inputs (f ?x) \<inter> ran wire. BTL p buf' p' = BTL p buf p'\<close>
      using bufs_eq read_inside(2) inputs_after_choices inputs_sub_op_Read mem_simps(4)
        sub_op.intros(2) sub_op_Read_inputs BTL_access BTL_diff_access by metis
    ultimately have \<open>R (loop_op wire (BTL p buf) (f ?x)) (loop_op wire (BTL p buf') (f ?y))\<close>
      unfolding R_def by auto
    hence \<open>op.congclp R op' ?op''\<close> using op.cong_Silent[OF op.cong_base]
      unfolding read_inside(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using read_inside(2-) bufs_eq Read_choices_inputs by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  next
    case write_outside
    let ?op'' = \<open>Write (loop_op wire buf' op'') p x\<close>
    have \<open>R (loop_op wire buf op'') (loop_op wire buf' op'')\<close> unfolding R_def
      using bufs_eq write_outside(2) inputs_after_choices mem_simps(4) op.set(2) by metis
    hence \<open>op.congclp R op' ?op''\<close> using op.cong_Write[OF op.cong_base refl refl]
      unfolding write_outside(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using write_outside(2-) by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  next
    case write_inside
    let ?op'' = \<open>Silent (loop_op wire (BENQ q x buf') op'')\<close>
    have \<open>R (loop_op wire (BENQ q x buf) op'') (loop_op wire (BENQ q x buf') op'')\<close>
      using bufs_eq write_inside(2) inputs_after_choices mem_simps(4) op.set(2)
      unfolding R_def BENQ_def by force
    hence \<open>op.congclp R op' ?op''\<close> using op.cong_Silent[OF op.cong_base]
      unfolding write_inside(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using write_inside(2-) by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  next
    case silent
    let ?op'' = \<open>Silent (loop_op wire buf' op'')\<close>
    have \<open>R (loop_op wire buf op'') (loop_op wire buf' op'')\<close>
      using bufs_eq silent inputs_after_choices mem_simps(4) op.set(4) unfolding R_def by metis
    hence \<open>op.congclp R op' ?op''\<close> using op.cong_Silent[OF op.cong_base]
      unfolding silent(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using silent(2-) by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  qed
qed

(* TODO: Move. *)
lemma loop_op_buf_cong:
  assumes \<open>wire' = wire\<close> \<open>(op' :: ('i, 'o, 'd) op) = op\<close> \<open>\<forall>p \<in> inputs op \<inter> ran wire. buf' p = buf p\<close>
  shows \<open>loop_op wire buf op = loop_op wire' buf' op'\<close>
proof (insert assms, hypsubst_thin, coinduction arbitrary: buf buf' op rule: op.coinduct_upto)
  case (Eq_op buf buf' op)
  define R :: \<open>('i, 'o, 'd) op \<Rightarrow> ('i, 'o, 'd) op \<Rightarrow> bool\<close> where
    \<open>R = (\<lambda>op1 op2. \<exists>buf buf' op. op1 = loop_op wire buf op \<and> op2 = loop_op wire buf' op
  \<and> (\<forall>p. p \<in> inputs op \<and> p \<in> ran wire \<longrightarrow> buf' p = buf p))\<close>
  have \<open>\<forall>op'. op' |\<in>| un_Choice (loop_op wire buf op) \<longrightarrow> (\<exists>op''.
  op'' |\<in>| un_Choice (loop_op wire buf' op) \<and> op.congclp R op' op'')\<close>
    using un_Choice_loop_op_buf_cong[where op=op] Eq_op unfolding R_def by (metis (lifting))
  moreover have \<open>\<forall>op'. op' |\<in>| un_Choice (loop_op wire buf' op) \<longrightarrow> (\<exists>op''.
  op'' |\<in>| un_Choice (loop_op wire buf op) \<and> op.congclp R op'' op')\<close>
  proof (intro allI impI)
    fix op'
    assume op': \<open>op' |\<in>| un_Choice (loop_op wire buf' op)\<close>
    obtain op'' where op'': \<open>op'' |\<in>| un_Choice (loop_op wire buf op)\<close> \<open>op.congclp R op' op''\<close>
      using un_Choice_loop_op_buf_cong[OF _ op', where buf'=buf] Eq_op unfolding R_def by auto
    moreover have \<open>op.congclp R op'' op'\<close> by (rule op.cong_sym[OF op''(2)])
    ultimately show \<open>\<exists>op''. op'' |\<in>| un_Choice (loop_op wire buf op) \<and> op.congclp R op'' op'\<close>
      by blast
  qed
  ultimately show ?case by (fastforce simp add: rel_set_def R_def)
qed




lemma
  fixes  os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> 
  defines
    \<open>INV \<equiv> \<lambda> os_label_prop os L.  
    os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr> \<and>
    label_prob_ty2_check os_label_prop (curry cbufs 1) \<and>
    (\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))) \<and> 
    dataplane_tracker_inv os cbufs sg \<and>
    (\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    (\<forall> t \<in> set (timestamps os_label_prop). \<not> frontier_less_equal (exit_scope myfst (front (os 1) 0 + front (os 1) 1)) t \<longrightarrow> labels_stable (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    (\<forall> t \<in> myfst ` snd ` set (input (os 1) 0) \<union> myfst ` snd ` set (input (os 1) 1). frontier_less_equal (exit_scope myfst (front (os 1) 1)) t) \<and>
    label_prop_upd_inv os_label_prop \<and> input_ocaps_inv (os 1)\<close>
  assumes \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary \<and> nxt sg = graph_to_nxt (summ sg)\<close>
    \<open>INV os_label_prop os L\<close>
    \<open>T \<noteq> []\<close>
  shows  "\<exists> os_label_prop' os' L'. (step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op (os_label_prop :: (nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state)))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os 2) :: (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state))))))
       (loop_op loop_wire ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2,1) := [], Inr (1,1) := []))
       (comp_map
         (comp_op
           comp_wire
           ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2,1) := [], Inr (1,1) := []))
           (logic_map (1 :: 3) (label_propagation_op (os_label_prop')))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os' 2))))))) \<and>
       INV os_label_prop' os' L'"
  using assms(3) apply -
  apply (induct "labels_measure (all_edges os_label_prop (Max (set T))) (min_label os_label_prop (Max (set T)))" arbitrary: os_label_prop os L rule: less_induct)
  subgoal premises prems for os_label_prop os L
    apply (intro exI conjI)
     apply (rule rtranclp_trans)
    using prems
    oops

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
    \<open>(\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t))\<close>

\<open>(\<forall> t \<in> set (timestamps os_label_prop). \<not> frontier_less_equal (exit_scope myfst (front (os 1) 0 + front (os 1) 1)) t \<longrightarrow> labels_stable (all_edges os_label_prop t) (min_label os_label_prop t))\<close>
\<open>\<forall> t \<in> myfst ` snd ` set (input (os 1) 0) \<union> myfst ` snd ` set (input (os 1) 1). frontier_less_equal (exit_scope myfst (front (os 1) 1)) t\<close>
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
    and label_prop_inv = SIM1(15,16,17,18,19,20)
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
      subgoal for d t xs
        apply (intro exI conjI relcomppI)
           apply (rule rtranclp.rtrancl_refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def)
        apply (rule exI[of _ S])
        apply (rule exI[of _ SO])
        apply (rule exI[of _ SP])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(0 := (os 0)\<lparr>outpu := (outpu (os 0))(0 := xs)\<rparr>)\<close>])
        apply (rule exI[of _ \<open>os_input\<lparr>outpu := (outpu os_input)(0 := xs)\<rparr>\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ \<open>BENQ (1, 0) (d, t) cbufs\<close>])
        apply (intro exI conjI)
                            apply (simp add: dataflow_tree_to_operator_def)
                            defer
                            apply (rule refl)
        using subgraph_inv(1) apply simp
                           apply (simp_all add: operator_state.defs(3) subgraph_inv(2) os_inv)
        using os_inv(1,5)
                    apply (simp add: ty1_check_def operator_state.defs(3) BENQ_def)
                    apply (frule spec[of _ 0])
                    apply fastforce
        using os_inv(1,4-6)
                   apply (simp add: ty1_check_def label_prob_ty2_check_def operator_state.defs(3) BENQ_def)
                   apply (drule spec[of _ 0])
                   apply simp
                  apply (rule dataplane_tracker_inv_update_outputs[OF dataplane_inv _ _ _ _ G, where nid=0 and xs=\<open>[(d, t)]\<close> and ys=xs and p=0])
                     apply simp
                    apply (simp add: fun_upd_def)
                   apply (simp add: BENQ_def)
                  apply (simp add: subgraph_inv(1) raw_summary_def antichain_from_list_singleton)
                 apply (subgoal_tac \<open>outputs_at_target (summ sg) (os(0 := (os 0)\<lparr>outpu := (outpu (os 0))(0 := xs)\<rparr>)) >> BENQ (1, 0) (d, t) cbufs
  = outputs_at_target (summ sg) os >> cbufs\<close>)
                  apply (simp add: csets_inv(1) buffers_inv os_inv(4,7) operator_state.defs(3))
                 apply (simp add: outputs_at_target_raw_summary subgraph_inv(1) BENQ_def BULK_BENQ_def fun_eq_iff)
                apply (simp add: csets_inv(2))
               apply (rule input_stream_inv)
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) apply (simp add: os_inv(4,7) operator_state.defs(3))
            apply (simp add: label_prop_inv(3))
        using label_prop_inv(4) apply simp
        using label_prop_inv(5) apply (simp add: os_inv(4,7) operator_state.defs(3))
         apply (rule label_prop_inv(6))
        apply (clarsimp intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>] arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule arg_cong2[where f=\<open>\<lambda>buf op. comp_op _ buf _ op\<close>])
         apply (fastforce simp add: BENQ_def)
        apply (rule loop_op_buf_cong[OF refl])
         apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
         apply (rule comp_op_buf_cong[OF refl refl refl])
         apply (clarsimp simp add: BENQ_def ran_def split: sum.splits if_splits)
         apply (metis prod.exhaust sumE)
        apply (clarsimp simp add: BENQ_def ran_def split: sum.splits if_splits)
        apply (metis prod.exhaust sumE)
        done
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
          apply (rule exI[of _ "D"])
          apply (rule exI[of _ lxs])
          apply (rule exI[of _ "os(1 := drop_caps
                       (produces (os 1)
                         (label_prop_output_batch os_label_prop
                           (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))
                       (map (\<lambda>t. Cap t 0) (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))"])
          apply (rule exI[of _ "drop_caps
                       (produces os_label_prop
                         (label_prop_output_batch os_label_prop
                           (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))
                       (map (\<lambda>t. Cap t 0) (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)))"])
          apply (rule exI[of _ cbufs])
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
                                    apply (drule bspec, simp)
                                     apply simp
                                    subgoal for a b
                                      apply (cases b; cases t'; simp; hypsubst_thin?)
                                      subgoal for t1 t2 t3
                                        apply (subgoal_tac "\<not> frontier_less_equal (exit_scope myfst (front (os 1) 1)) t2")
                                        subgoal
                                          using frontier_less_equal_trans 
                                          by (metis (no_types, lifting) label_prop_inv(3)  Un_iff image_eqI img_snd myprod.sel(1))
                                        subgoal
                                          using exit_scope_plus_distrib
                                          by (metis not_frontier_less_equal_sum)
                                        done
                                      done
                                    subgoal for a b
                                      apply (cases b; cases t'; simp; hypsubst_thin?)
                                      subgoal for t1 t2 t3
                                        apply (subgoal_tac "\<not> frontier_less_equal (exit_scope myfst (front (os 1) 1)) t2")
                                        subgoal
                                          using frontier_less_equal_trans 
                                          by (metis (no_types, lifting) label_prop_inv(3)  Un_iff image_eqI img_snd myprod.sel(1))
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
                        by auto
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
            apply (rule exI[of _ G])
            apply (rule exI[of _ V])
            apply (rule exI[of _ L])
            apply (simp add: operator_state.defs)
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
          subgoal premises aux
            apply (rule iffD1[OF dataplane_tracker_inv_clean, rotated 2, of _ _ sg "upfro sg"])
              apply (rule dataplane_tracker_inv_produces_drops[OF D, where nid=1 and os=os 
                  and drops = "\<lambda> p. if p = 1
                         then []
                         else filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)"
                  and produs="map (\<lambda> t . (0, MyPair t 0, 1)) (rmdups {} (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))"
                  and oputs="(\<lambda> p. if p = 1 then [] else map (\<lambda>t. (en2 os_label_prop (components_from_labels (all_edges os_label_prop t) (min_label os_label_prop t)), (MyPair t 0)))
                          (rmdups {} (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)))))"])
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
                using label_prop_inv(4)[unfolded buffers_inv, simplified]
                by (metis UnI1 myprod.collapse)               
              done
            subgoal 
              apply (clarsimp simp add: operator_state.defs os_inv(4))
              subgoal for p x
                using label_prop_inv(4)[unfolded buffers_inv, simplified]
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
            using input_stream_inv timely_input_stream_expires_le 
            by auto
          subgoal
            using label_prop_inv(1)
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
            using label_prop_inv(5) by simp
          subgoal premises aux
            using label_prop_inv(6) apply -
            unfolding input_ocaps_inv_def drop_caps_def
            apply (auto simp add: filter_False os_inv(7)[rule_format, unfolded raw_summary_def, simplified])
            subgoal 
              by fastforce
            subgoal
              apply (drule spec2[of _  0 1])
              apply simp
              apply (drule bspec[of _ ])
               apply assumption
              apply (simp add: filter_True comp_def )
              done
            subgoal for a b
              apply (drule spec2[of _  0 0])
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
                apply (auto intro: frontier_less_equal_antichain_plusI2)
                done
              done
            subgoal for a b
              apply (drule spec2[of _  0 0])
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
                apply (auto intro: frontier_less_equal_antichain_plusI2)
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
                apply (rule exI[of _ D])
                apply (rule exI[of _ lxs])
                apply (rule exI[of _ "os(1 := release_caps
                       (drop_caps
                         (produces
                           (add_caps (input_tl (os 1) 0)
                             (map snd
                               (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                                 (myfst t) l1 l2 t)))
                           (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t))
                         (map snd
                           (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                       1)"])
                apply (rule exI[of _ "release_caps
                       (drop_caps
                         (produces
                           (add_caps (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (map snd
                               (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                                 (myfst t) l1 l2 t)))
                           (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t))
                         (map snd
                           (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                       1"])
                apply (rule exI[of _ cbufs])
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
                          using label_prop_inv(5)[unfolded os_inv(4) operator_state.defs] by simp
                        subgoal by simp
                        subgoal
                          apply simp
                          apply (rule arg_cong2[where f=cinsert])
                          subgoal
                            apply (simp add: insert_commute ccs_insert_symmetric)
                            apply (subst ccs_insert_swap)
                            apply auto
                            done
                          subgoal
                            apply (subst (1 3) cUn_assoc)
                            apply (rule arg_cong2[where f=cUn])
                            subgoal
                              by simp
                            subgoal
                              apply (subst (1) icoll_LCons_Data)
                              subgoal
                                using input_stream_inv timely_input_stream_expires_le 
                                by auto
                              subgoal 
                                apply (subst (3) cimage_cUn)
                                apply (subst (2) cUn_assoc)
                                apply (rule arg_cong2[where f=cUn])
                                 apply (simp add:  csets_inv(2))
                                apply (subst (1) cfilter_False)
                                subgoal
                                  unfolding label_prop_neighbor_batch_def
                                  by auto
                                subgoal
                                  apply simp
                                  apply (rule cimage_cong)
                                  subgoal
                                    by simp
                                  subgoal for t''
                                    apply (cases "t \<le> t''")
                                    subgoal
                                      apply (subst all_edges_eq_le[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                                      subgoal using label_prop_inv(5)[unfolded os_inv(4) operator_state.defs] by simp
                                      subgoal 
                                        using myfst_mono by blast
                                      subgoal by simp
                                      subgoal
                                        apply (subst insert_commute)
                                        apply (simp add: ccs_insert_symmetric)
                                        done
                                      done
                                    subgoal
                                      apply (subst all_edges_eq_not_le[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                                      subgoal
                                        by (metis MyPair_mono bot_nat_0.extremum myprod.exhaust_sel)
                                      subgoal
                                        by simp
                                      subgoal
                                        apply simp
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      subgoal
                        using label_prop_inv(4)[rule_format, of t] apply -
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
                  apply (rule exI[of _ "G(myfst t := (map_entry v1 (Cons v2) (G (myfst t)))(v2 := Cons v1 (G (myfst t) v2)))"])
                  apply (rule exI[of _ "map_entry (myfst t) (append [v1, v2]) V"])
                  apply (rule exI[of _ "L(myfst t := (L (myfst t))(l1 := l2))"])
                  apply (simp del: filter.simps)
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
                  apply (rule dataplane_tracker_inv_release_caps_update[OF D])
                    apply (rule dataplane_tracker_inv_add_caps_produces_drop_caps_update[OF D])
                  using dataplane_inv apply simp
                  using G apply simp
                  using subgraph_inv(2) apply assumption 
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
                      apply (rule  label_prop_inv(6)[unfolded input_ocaps_inv_def, rule_format, of _ 0 0, simplified])
                      subgoal
                        using aux(2,3) 
                        by (simp add: os_inv(4) operator_state.defs)
                      subgoal
                        by (simp add: zero_myprod_def os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                      done
                    done
                  subgoal 
                    using G
                    by (smt (verit) Label_Propagation_op.intsum_add_caps array_rules(3,4) graph_summar_nt_intsum_cong intsum_drop_caps intsum_input_tl
                        intsum_produces)
                  using subgraph_inv(2) apply assumption 
                  done
                subgoal premises aux
                  using input_stream_inv by simp
                subgoal
                  apply safe
                  subgoal for t''
                    apply (rule labels_inv_input0_preserved[where xs=xs])
                    using label_prop_inv(1) apply blast
                    subgoal
                      using label_prop_inv(5) by assumption
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
                    apply (subst (asm) label_prop_edge_record_update_def)
                    apply simp      
                    apply (elim disjE)
                    subgoal
                      apply (subgoal_tac "frontier_less_equal (exit_scope myfst (front (os 1) 1)) t'")
                      subgoal
                        by (simp add: exit_scope_plus_distrib frontier_less_equal_antichain_plusI2)
                      subgoal
                        using aux(2) label_prop_inv(3)[rule_format] by (auto simp add: os_inv(4) operator_state.defs)
                      done
                    subgoal
                      apply (subgoal_tac "\<not> myfst t \<le> t'")
                      subgoal
                        apply (rule labels_stable_input0_preserved)
                              apply (rule label_prop_inv(2)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of t'])
                               apply (simp add: os_inv(4) operator_state.defs)
                              apply assumption+
                        using aux[unfolded os_inv(4) operator_state.defs, simplified] apply (auto simp add: label_prop_edge_record_update_def  os_inv(4) operator_state.defs)
                        done
                      subgoal
                        using aux(2) apply -
                        using label_prop_inv(3)[rule_format, of "myfst t"] apply -
                        apply (drule meta_mp)
                        subgoal
                          by (auto simp add: os_inv(4) operator_state.defs)
                        subgoal
                          by (metis exit_scope_plus_distrib frontier_less_equal_antichain_plusI2 frontier_less_equal_trans)
                        done
                      done
                    done
                  done
                subgoal premises aux
                  using aux(2) label_prop_inv(3) 
                  by (auto simp add:  os_inv(4) operator_state.defs input_tl_def)
                subgoal
                  using label_prop_inv(4) apply -
                  apply simp
                  unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                  by (fastforce dest!: in_set_list_diffD  simp add: os_inv(4)  operator_state.defs input_tl_def release_caps_def drop_caps_def split: if_splits)
                subgoal
                  apply (rule label_prop_upd_inv_input0_preserved)
                         apply (rule label_prop_inv(5))
                        apply (simp_all add: operator_state.defs os_inv(4))
                  unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                  by (auto simp add: operator_state.defs os_inv(4)  input_tl_def release_caps_def drop_caps_def produces_def)
                subgoal premises aux
                  apply simp
                  apply (rule input_ocaps_inv_release_capsI)
                  apply (rule input_ocaps_inv_drop_produces_add_capsI)
                  using label_prop_inv(6) input_ocaps_inv_input_tlI apply fast
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
              subgoal for v l
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
                apply (rule exI[of _ "os(1 := release_caps
                       (drop_caps
                         (produces
                           (add_caps (input_tl (os 1) 1)
                             (map snd
                               (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t)))
                           (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t))
                         (map snd (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t)))
                       1)"])
                apply (rule exI[of _ "release_caps
                       (drop_caps
                         (produces
                           (add_caps (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l))
                             (map snd
                               (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t)))
                           (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t))
                         (map snd (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t)))
                       1"])
                apply (rule exI[of _ cbufs])
                apply (rule exI[of _ sg])
                apply (intro conjI)
                subgoal
                  by (simp add: operator_state.defs dataflow_tree_to_operator_def os_inv(1))
                subgoal premises aux
                  using aux(2,3) apply -
                  apply (simp  del: filter.simps add: label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
                  apply (rule arg_cong2[where f=set_spec_op])
                   apply (clarsimp simp del: filter.simps del: disjCI simp add: inputs_at_target_def BULK_BENQ_def operator_state.defs outputs_at_target_raw_summary subgraph_inv buffers_inv csets_inv(1) os_inv(4))
                  subgoal
                    apply (simp add: cUn_assoc)
                    apply (rule arg_cong2[where f=cUn])
                    subgoal
                      by simp
                    subgoal
                      apply (subst (3) cimage_cUn)
                      apply (simp add: cUn_assoc)
                      apply (rule arg_cong2[where f=cUn])
                      subgoal
                        by (simp add: csets_inv(2))
                      subgoal
                        apply (subst (1) cfilter_False)
                        subgoal
                          unfolding label_prop_label_batch_def label_prop_neighbor_batch_def
                          by auto
                        subgoal
                          apply simp
                          apply (rule cimage_cong)
                          subgoal
                            unfolding input_tl_def
                            by simp
                          subgoal for tt
                            unfolding input_tl_def
                            by simp
                          done
                        done
                      done
                    done
                  subgoal
                    by simp
                  done
                subgoal
                  using subgraph_inv(1) by assumption
                subgoal
                  using subgraph_inv(2) by assumption
                subgoal
                  using os_inv(2) by simp
                subgoal
                  by (simp add: os_inv(3,4) operator_state.defs)
                subgoal
                  apply (rule exI[of _ T])
                  apply (rule exI[of _ G])
                  apply (rule exI[of _ V])
                  apply (rule exI[of _ "label (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l))"])
                  apply simp
                  apply (simp add: operator_state.defs)
                  unfolding release_caps_def drop_caps_def produces_def add_caps_def input_tl_def label_prop_label_record_update_def
                  by (simp add: operator_state.defs os_inv(4))
                    (* show but finishes *)
                subgoal
                  using os_inv(1,5)
                  by (simp add:  operator_state.defs)
                subgoal
                  using os_inv(2,4,6) apply -
                  apply simp
                  apply (rule label_prob_ty2_check_producesI)
                    apply simp
                    apply (rule label_prob_ty2_check_input_tlI)
                    apply (auto simp add: operator_state.defs label_prop_label_batch_def label_prop_neighbor_batch_def)
                  done
                subgoal
                  using os_inv(7) by simp
                subgoal
                  apply (rule dataplane_tracker_inv_release_caps_update[OF D])
                    apply (rule dataplane_tracker_inv_add_caps_produces_drop_caps_update[OF D])
                  subgoal
                    using dataplane_inv by simp
                  subgoal
                    using G by simp
                  subgoal
                    using subgraph_inv(2) by assumption
                  subgoal
                    unfolding label_prop_label_batch_def label_prop_neighbor_batch_def
                    apply (clarsimp simp add: os_inv(4) operator_state.defs)
                    using label_prop_inv(6)[unfolded input_ocaps_inv_def os_inv(7)[rule_format] raw_summary_def, simplified, rule_format, of "(d, t)" 1 1 0, simplified]
                    apply (metis (no_types, lifting) dual_order.eq_iff less_eq_myprod_def list.set_intros(1) myprod.sel(1,2) zero_myprod_def)
                    done
                  subgoal premises
                    using G
                    by (smt (verit, best) Label_Propagation_op.intsum_add_caps fun_upd_other fun_upd_same graph_summar_nt_intsum_cong intsum_drop_caps intsum_input_tl intsum_produces)
                  subgoal
                    using subgraph_inv(2) by assumption
                  done
                subgoal
                  using input_stream_inv by simp
                subgoal
                  apply safe
                  subgoal for ta
                    apply simp
                    apply (rule labels_inv_input1_preserved_record_update_tl[
                          of os_label_prop d t v l "myfst t"
                          "label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)" ta,
                          simplified])
                       apply (rule label_prop_inv(1)[rule_format])
                      apply (rule label_prop_inv(5))
                     apply simp_all
                    done
                  done
                subgoal
                  apply safe
                  subgoal for t'
                    apply simp
                    apply (rule labels_stable_input1_preserved_record_update_tl)
                    using label_prop_inv(2) apply fast
                    using label_prop_inv(3)[rule_format, of "myfst t"] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (simp add: os_inv(4) operator_state.defs)
                    subgoal
                      by (metis (no_types, lifting) exit_scope_plus_distrib frontier_less_equal_antichain_plusI2 frontier_less_equal_trans)
                    done
                  done
                subgoal
                  unfolding input_tl_def
                  using label_prop_inv(3)
                  by (simp add: image_iff os_inv(4) operator_state.defs)
                subgoal
                  using label_prop_inv(4)
                  unfolding release_caps_def drop_caps_def add_caps_def input_tl_def
                  by (auto dest!: in_set_list_diffD simp add: label_prop_label_batch_def label_prop_neighbor_batch_def image_iff os_inv(4) operator_state.defs)
                subgoal
                  apply simp
                  apply (rule label_prop_upd_inv_input1_preserved[])
                           apply (rule label_prop_inv(5))
                          apply (simp_all add: label_prop_label_record_update_def input_tl_def image_iff os_inv(4) operator_state.defs)
                  done
                subgoal
                  apply simp
                  apply (rule input_ocaps_inv_release_capsI)
                  apply (rule input_ocaps_inv_drop_produces_add_capsI)
                  apply (rule input_ocaps_inv_input_tlI)
                  using label_prop_inv(6) apply -
                  apply (simp add: os_inv(4) operator_state.defs)
                  done
                done
              done
            done
          done
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
        apply (insert dataplane_inv subgraph_inv(1))
        apply (unfold dataplane_tracker_inv_def propagation_inv_def)
        apply (elim exE conjE; hypsubst_thin)
        apply (rule FalseE)
        apply (rule propagate_all_terminates[OF D, unfolded not_def, rule_format])
        by (auto simp add: raw_summary_def)
      subgoal 
        sorry
      subgoal for d t xs
        apply (intro exI conjI)
         apply (rule rtranclp.rtrancl_refl)
        apply (intro relcomppI)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def[simplified])
        apply (rule exI[of _ \<open>cinsert ((1, 0), d, t) S\<close>])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(0 := xs)\<rparr>)\<close>])
        apply (rule exI[of _ \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(0 := xs)\<rparr>\<close>])
        apply (rule exI[of _ cbufs])
        apply (rule exI[of _ sg])
        apply (intro exI conjI)
                         apply (simp add: dataflow_tree_to_operator_def os_inv(1))
        subgoal
          apply (simp add: subgraph_inv outputs_at_target_raw_summary csets_inv(1,2) buffers_inv os_inv(4) operator_state.defs(3))
          apply (rule arg_cong2[where f=set_spec_op])
           apply (rule arg_cong2[where f=cinsert])
            apply simp_all
          apply (rule arg_cong2[where f=cUn])
           apply simp
          apply (rule cimage_cong)
          subgoal
            by simp
          subgoal premises for tt
            unfolding all_edges_def all_vertices_def set_neighbors
            by simp
          done
                       apply (rule subgraph_inv(1))
                      apply (rule subgraph_inv(2))
                     apply (simp add: os_inv(2))
                    apply (simp add: os_inv(3))
                   apply (simp add: os_inv(4) operator_state.defs(3))
        using os_inv(1,5) apply simp
        using os_inv(6) unfolding label_prob_ty2_check_def apply simp
        using os_inv(7) apply simp
               apply (rule dataplane_tracker_inv_update_outputs_outside[OF dataplane_inv _ _ G])
                apply (simp add: fun_upd_def)
               apply (simp add: subgraph_inv(1) raw_summary_def)
              apply (subgoal_tac \<open>outputs_at_target (summ sg) (os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(0 := xs)\<rparr>)) (1, 0)
  = outputs_at_target (summ sg) os (1, 0)\<close>)
               apply (simp add: csets_inv(1) buffers_inv BULK_BENQ_def all_edges_def all_vertices_def neighbors_def)
               apply (simp add: subgraph_inv(1) outputs_at_target_raw_summary)
               apply (simp add: input_stream_inv)
              apply (simp add: subgraph_inv os_inv(4) operator_state.defs outputs_at_target_raw_summary)
        subgoal
          using label_prop_inv
          by (simp_all add: all_edges_def all_vertices_def min_label_def neighbors_def labels_inv_def labels_stable_def)

        subgoal premises aux
          apply safe
          using label_prop_inv(2)
          by (simp add: all_edges_def all_vertices_def min_label_def neighbors_def labels_inv_def labels_stable_def)

        subgoal premises aux
          using label_prop_inv(3)
          by auto
        subgoal premises aux
          using label_prop_inv(4)
          by auto
        subgoal premises aux
          using label_prop_inv(5) 
          unfolding label_prop_upd_inv_def 
          by (auto del: disjCI simp add: )
        subgoal premises aux
          using label_prop_inv(6) 
          unfolding input_ocaps_inv_def
          by auto
        done
      done
  qed
next
  case SIM2
  thm SIM2(3,4,5,6,7,8,9)
  note subgraph_inv = SIM2(1,2)
    and os_inv = SIM2(3,4,5,6,7,8,9)
    and buffers_inv = SIM2(10)
    and dataplane_inv = SIM2(11)
    and csets_inv = SIM2(12,13)
    and input_stream_inv = SIM2(14)
    and label_prop_inv = SIM2(15,16,17,18,19,20)
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
    define R where "R = ?R"
    show ?thesis 
      apply -
      unfolding R_def[symmetric]
      unfolding wsim_def
      apply simp
      apply (intro allI impI)
      apply (repeat_new \<open>erule conjE step_set_spec_op_elim; simp?; hypsubst_thin?\<close>;
          clarsimp split: if_splits option.splits dest!: num2_neq simp flip: ooo_input_op_def label_propagation_op_def increment_op_def; hypsubst_thin?)
      subgoal for nid p WCC t
        apply (clarsimp simp flip: cin.rep_eq simp add: image_iff buffers_inv csets_inv(1,2))
        apply (subst (asm) disj_assoc[symmetric])
        apply (erule disjE)
        subgoal
          apply (intro exI conjI)
           apply (rule wstep_trans(1))
            apply (rule relpowp_imp_rtranclp[
                where n="length (outpu (os 1) 0)"]) 
            apply (rule step_set_op_steps_Out_intro[where xs="outpu (os 1) 0"  and p="(1, 0)"])
              apply (rule steps_Tau_dataflow_op_steps_Out_intro[where xs="outpu (os 1) 0" and nid = 1 and p = 0])
               apply (subst dataflow_tree_to_operator_def)
               apply simp
               apply (rule steps_map_op[where xs="map _ (outpu (os 1) 0)", rotated 2])
                 apply (rule steps_comp_op_R_Out[where xs="map _ (outpu (os 1) 0)" and p="Inr (1, 0)"])
                    apply (rule steps_Out_loop_op_intro[where xs="map _ (outpu (os 1) 0)" and p="Inr (1, 0)"])
                       apply (rule steps_map_op[where xs="map _ (outpu (os 1) 0)" , rotated 2])
                         apply (rule steps_comp_op_L_Out[where xs="map _ (outpu (os 1) 0)"])
                             apply (rule steps_map_op[where xs="map _ (outpu (os 1) 0)", rotated 2])
                              apply (rule steps_label_propagation_op_Write_Some[where ys=Nil])
                              apply simp
                              apply (rule refl)+
                              apply (simp add: os_inv(4) operator_state.defs)
                              apply (rule refl)+
                             apply force
                            apply fastforce
                           apply (rule refl)+
                         apply fastforce
                        apply (rule refl)+
                       apply fastforce
                      apply fastforce
                     apply (rule refl)+
                 apply fastforce
                apply (rule refl)+
               apply fastforce
              apply (rule refl)+
           apply (rule step_set_op_intro_Out)
              apply (rule refl)+
             apply force
            apply simp
           apply (rule refl)+
          apply (intro relcomppI)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_sym)
          apply (rule wb_upto_b_base)
          apply (unfold R_def[simplified])
          apply (rule exI[of _ "cUn (Pair (1, 0) |`| cset_from_list (outpu (os 1) 0)) S"])
          apply (rule exI[of _ "cinsert ((nid, p), WCC, t) D"])
          apply (rule exI[of _ lxs])
          apply (rule exI[of _ "os(1 := (os 1)\<lparr>outpu := (outpu os_label_prop)(0 := [])\<rparr>)"])
          apply (rule exI[of _ "os_label_prop\<lparr>outpu := (outpu os_label_prop)(0 := [])\<rparr>"])
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ sg])
          apply (intro conjI)
          subgoal
            by (simp add: label_propagation_op_def operator_state.defs dataflow_tree_to_operator_def os_inv(1))
          subgoal premises
            apply (rule arg_cong2[where f=set_spec_op])
             apply simp_all
            apply (subst cUn_commute)
            apply (rule arg_cong2[where f=cUn])
             apply simp
            apply (rule cimage_cong)
            subgoal
              by (simp  del: filter.simps add: subgraph_inv outputs_at_target_raw_summary csets_inv(2) label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
            subgoal
              by (simp  del: filter.simps add: subgraph_inv all_edges_def all_vertices_def csets_inv(2) outputs_at_target_raw_summary label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
            done
          subgoal
            using subgraph_inv(1) by assumption
          subgoal
            using subgraph_inv(2) by assumption
          subgoal
            using os_inv by simp
          subgoal
            using os_inv by simp
          subgoal
            apply (rule exI[of _ T])
            apply (rule exI[of _ G])
            apply (rule exI[of _ V])
            apply (rule exI[of _ L])
            apply (simp add: os_inv(4) operator_state.defs os_inv(1))
            done
          subgoal
            using os_inv(5)
            by (simp add:  os_inv(4) operator_state.defs os_inv(1))
          subgoal
            using os_inv(6) 
            by (simp add: label_prob_ty2_check_def os_inv(4) operator_state.defs os_inv(1))
          subgoal
            using os_inv(7) 
            by simp
          subgoal
            apply (rule dataplane_tracker_inv_update_outputs_outside[OF dataplane_inv, where nid=1 and p=0 and xs=Nil])
            subgoal
              apply (clarsimp simp add: os_inv(4) operator_state.defs os_inv(1))
              apply (metis (no_types, lifting) array_rules(3,4))
              done
            subgoal
              by (simp add: subgraph_inv raw_summary_def)
            subgoal
              using G by assumption
            done
          subgoal
            by (simp add: input_stream_inv)
          subgoal
            using label_prop_inv(1)
            by auto
          subgoal
            using label_prop_inv(2)
            by simp
          subgoal
            using label_prop_inv(3)
            by simp
          subgoal
            using label_prop_inv(4)
            by simp          
          subgoal
            using label_prop_inv(5)
            by simp
          subgoal
            using label_prop_inv(6) unfolding input_ocaps_inv_def
            by simp
          done
        subgoal premises prems
          using timely_input_stream_advances_frontier[OF input_stream_inv, of t] apply -
          apply clarsimp
          subgoal premises stream_move for n

            apply (intro exI conjI[rotated])
             apply (intro relcomppI)
               apply (rule bisim_refl)
              defer
              apply (rule wbisim_refl)
             apply (rule wstep_trans(1))
              apply (rule transitive_closurep_trans'(2))
               apply (rule relpowp_imp_rtranclp[
                  where n="n + 
                           (length (outpu (os 0) 0)) + length (filter is_Data (ltaken n lxs)) + 
                           (length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n lxs))) +
                           (length (input (os 1) 0)) + length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n lxs))"]) 
               apply (simp only: relpowp_add)
               apply (intro relcomppI)
                        apply (rule step_n_Taus_set_op)
                         apply (rule step_tau_pow_dataflow_op)
                         apply (subst dataflow_tree_to_operator_def)
                         apply simp
                         apply (rule step_tau_pow_map_op)
                         apply (rule step_taus_L_pow_comp_op_steps_intro)
                          apply (rule step_tau_pow_map_op)
                          apply (rule step_compower_ooo_input_op_iterates_n[where p=0])
            subgoal
              using input_stream_inv 
              by (simp add: os_inv(1) operator_state.defs)
            subgoal
              by simp
            subgoal
              using os_inv(3)
              by (simp add: os_inv(1) operator_state.defs)
            subgoal
              using stream_move
              by (simp add: os_inv(1) operator_state.defs)
                           apply (rule refl)+

                       apply (rule step_n_Taus_set_op)
                        apply (rule step_tau_pow_dataflow_op)
                        apply (rule step_tau_pow_map_op)
                        apply (rule step_tau_Out_pow_comp_op_steps_intro[where xs="map (\<lambda> (t, d). Inr (t, d)) (outpu (os 0) 0)" and p="Inr (0, 0)"])
                           apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 0) (Inr x)) (outpu (os 0) 0)"])
                             apply (rule refl)+
                            apply simp
                           apply (rule steps_ooo_input_op_Write_Some[where ys="map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))" and xs="outpu (os 0) 0" and p=0])
                              apply simp
                             apply (simp add: operator_state.defs os_inv(1))
                            apply (rule refl)+
                          apply simp
                         apply simp
                        apply (rule refl)+

                      apply (rule step_n_Taus_set_op)
                       apply (rule step_tau_pow_dataflow_op)
                       apply simp
                       apply (rule step_tau_pow_map_op)
                       apply (rule step_tau_Out_pow_comp_op_steps_intro[where p="Inr (0, 0)" and xs="map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))"])
                          apply (rule steps_map_op[where xs="map (\<lambda> e. case e of Data t d \<Rightarrow> Out (Some 0) (Inr (Inl d, t))) (filter is_Data (ltaken n lxs))"])
                            apply (rule refl)+
            subgoal
              by (auto simp add: comp_def split: IO.splits event.splits)

                          apply (rule steps_ooo_input_op_Write_Some[where xs="map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))" and ys=Nil and p=0])
                             apply simp
                            apply (simp add: operator_state.defs os_inv(1))
                           apply (rule refl)+
            subgoal
              by (auto simp add: comp_def split: IO.splits event.splits)
            subgoal
              by simp
                        apply simp
                       apply (rule refl)+

                     apply (rule step_n_Taus_set_op)
                      apply (rule step_tau_pow_dataflow_op)
                      apply simp
                      apply (rule step_tau_pow_map_op)
                      apply (rule step_tau_Inp_pow_comp_op_steps_intro[where n="length (cbufs (1, 0))" and p="Inr (1, 0)" and xs="map (\<lambda> x. Inr x) (cbufs (1, 0))"])
                           apply (rule steps_Inp_loop_op_intro[where p="Inr (1, 0)" and xs="map Inr (cbufs (1, 0))"])
                              apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (cbufs (1, 0))"])
                                apply (rule refl)+
                               apply fastforce
                              apply (rule steps_comp_op_L_Inp[where xs="map Inr (cbufs (1, 0))"and p="Inr (1, 0)"])
                                apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 0) (_ x)) (cbufs (1, 0))" ])
                                apply (rule refl)+
                                apply force
                                apply (rule steps_label_propagation_op_Read_Some)
                                apply (rule refl)+
                              apply simp
            subgoal
              by (auto simp add: ran_def split: sum.splits)
                            apply (rule refl)+
                          apply simp
            subgoal
              by (auto simp add: ran_def split: sum.splits)
            subgoal
              unfolding BULK_BENQ_def
              by simp
            subgoal
              unfolding BULK_BENQ_def
              by simp
                      apply (rule refl)+

                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply simp
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_tau_Inp_pow_comp_op_steps_intro[where n="length (outpu (os 0) 0)" and p="Inr (1, 0)" and xs="map (\<lambda> x. Inr x) (outpu (os 0) 0)"])
                          apply (rule steps_Inp_loop_op_intro[where p="Inr (1, 0)" and xs="map Inr (outpu (os 0) 0)"])
                             apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (outpu (os 0) 0)"])
                               apply (rule refl)+
                              apply fastforce
                             apply (rule steps_comp_op_L_Inp[where xs="map Inr (outpu (os 0) 0)"and p="Inr (1, 0)"])
                                apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 0) (_ x)) (outpu (os 0) 0)" ])
                                apply (rule refl)+
                                apply fastforce
                                apply (rule steps_label_propagation_op_Read_Some)
                                apply (rule refl)+
                             apply simp
            subgoal
              by (auto simp add: ran_def split: sum.splits)
                           apply (rule refl)+
                         apply simp
            subgoal
              by (auto simp add: ran_def split: sum.splits)
            subgoal
              unfolding BULK_BENQ_def
              by simp
            subgoal
              unfolding BULK_BENQ_def
              by simp
                     apply (rule refl)+

                   apply (rule step_n_Taus_set_op)
                    apply (rule step_tau_pow_dataflow_op)
                    apply simp
                    apply (rule step_tau_pow_map_op)
                    apply (rule step_tau_Inp_pow_comp_op_steps_intro[where p="Inr (1, 0)" and xs="map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))"])
                         apply (rule steps_Inp_loop_op_intro[where p="Inr (1, 0)" and xs="map _ (filter is_Data (ltaken n lxs))"])
                            apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (filter is_Data (ltaken n lxs))"])
                              apply (rule refl)+
                             apply fastforce
                            apply (rule steps_comp_op_L_Inp[where xs="map Inr (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs)))"and p="Inr (1, 0)"])
                               apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 0) (Inr x)) (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs)))" ])
                                apply (rule refl)+
                                apply fastforce
                               apply (rule steps_label_propagation_op_Read_Some)
                               apply (rule refl)+
                            apply simp
                            apply fastforce
            subgoal
              by (auto simp add: ran_def split: sum.splits)
                          apply (rule refl)+
                         apply simp
                         apply (simp split: event.splits)
                        apply simp
            subgoal
              by (auto simp add: ran_def split: sum.splits)
            subgoal
              unfolding BULK_BENQ_def
              by simp
            subgoal
              unfolding BULK_BENQ_def
              by simp
                    apply (rule refl)+

                  apply (rule step_n_Taus_set_op)
                   apply (rule step_tau_pow_dataflow_op)
                   apply simp
                   apply (rule step_tau_pow_map_op)
                   apply (rule step_taus_R_pow_comp_op_steps_intro)
                    apply (rule step_taus_loop_op_steps_intro)
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_taus_L_pow_comp_op_steps_intro)
                      apply (rule step_tau_pow_map_op)
                      apply (rule step_compower_label_propagation_op_input0_eq_alt[where msgs="input (os 1) 0" and ys="cbufs (1, 0) @ outpu (os 0) 0 @ map (\<lambda>ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))"])
            subgoal
              unfolding input_fold_consumes 
              by (simp add: os_inv(4) operator_state.defs)
                        apply simp
                       apply (simp add: os_inv(3,4) operator_state.defs)
            subgoal sorry
                      apply (rule refl)+


      apply (rule step_n_Taus_set_op)
                   apply (rule step_tau_pow_dataflow_op)
                   apply (rule step_tau_pow_map_op)
                   apply (rule step_taus_R_pow_comp_op_steps_intro)
                    apply (rule step_taus_loop_op_steps_intro)
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_taus_L_pow_comp_op_steps_intro)
                      apply (rule step_tau_pow_map_op)
                      apply (rule step_compower_label_propagation_op_input0_eq_alt[where msgs="cbufs (1, 0)" and ys="outpu (os 0) 0 @ map (\<lambda>ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))"])
            subgoal
              unfolding input_fold_consumes 
              by (simp add: os_inv(4) operator_state.defs input_fold_consumes)
                        apply simp
                       apply (simp add: os_inv(3,4) operator_state.defs)
            subgoal sorry
                      apply (rule refl)+


      apply (rule step_n_Taus_set_op)
                   apply (rule step_tau_pow_dataflow_op)
                   apply (rule step_tau_pow_map_op)
                   apply (rule step_taus_R_pow_comp_op_steps_intro)
                    apply (rule step_taus_loop_op_steps_intro)
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_taus_L_pow_comp_op_steps_intro)
                      apply (rule step_tau_pow_map_op)
                      apply (rule step_compower_label_propagation_op_input0_eq_alt[where msgs="outpu (os 0) 0" and ys="map (\<lambda>ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))"])
            subgoal
              unfolding input_fold_consumes 
              by (simp add: os_inv(4) operator_state.defs input_fold_consumes)
                        apply simp
                       apply (simp add: os_inv(3,4) operator_state.defs)
            subgoal sorry
                      apply (rule refl)+

      apply (rule step_n_Taus_set_op)
                   apply (rule step_tau_pow_dataflow_op)
                   apply (rule step_tau_pow_map_op)
                   apply (rule step_taus_R_pow_comp_op_steps_intro)
                    apply (rule step_taus_loop_op_steps_intro)
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_taus_L_pow_comp_op_steps_intro)
                      apply (rule step_tau_pow_map_op)
                      apply (rule step_compower_label_propagation_op_input0_eq_alt[where msgs="map (\<lambda>ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))" and ys="Nil"])
            subgoal
              unfolding input_fold_consumes 
              by (simp add: os_inv(4) operator_state.defs input_fold_consumes)
                        apply simp
                       apply (simp add: os_inv(3,4) operator_state.defs)
            subgoal sorry
                   apply (rule refl)+

              apply (rule step_Taus_set_op)
               apply (rule step_Taus_dataflow_op_Taus_intro)
               apply (rule step_star_map_op)
               apply (rule step_comp_op_R_Tau_start)

            find_theorems raw_summary

            term "antichain_from_list \<circ>\<circ> raw_summary"

            term "intsum (os 1)"

            oops


end
            apply (rule step_taus_loop_)
            apply (rule step_star_map_op)
            apply (rule step_comp_op_L_Tau_start)
            apply (rule step_star_map_op)

            find_theorems step Tau loop_op rtranclp

end


            find_theorems initia os
 
                        prefer 3
                        apply simp
                       prefer 3
            apply simp

                     
            thm step_compower_label_propagation_op_input0[unfolded cimage_cUn, simplified]

            find_theorems cUn cimage

            thm step_compower_label_propagation_op_input0_eq

            oops


end
            sorry
          done
        done
      done
  qed
qed

end
