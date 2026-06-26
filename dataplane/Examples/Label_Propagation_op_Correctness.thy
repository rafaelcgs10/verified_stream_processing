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
  "../Correctness/Propagates"
  "../Correctness/OCapsReorder"
  "../Correctness/Consumes"
  "HOL-ex.Sketch_and_Explore"
  Dataplane.Timely_Dataflow_Op
  Dataplane.Bots
  "../Correctness/Timely_Collections"
  Dataplane.Propagation_Properties
  Dataplane.SimulationProofMethods
begin

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

(* Note: this is basically lemma comp_op_chns_invar from dataplane_dis:dataplane/Comp_Reasoning.thy *)
lemma comp_op_buf_cong:
  assumes \<open>wire' = wire\<close> \<open>op1' = op1\<close> \<open>op2' = op2\<close> \<open>\<forall>p \<in> inputs op2 \<inter> ran wire. buf' p = buf p\<close>
  shows \<open>comp_op wire buf op1 op2 = comp_op wire' buf' op1' op2'\<close>
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

lemma inputs_ocaps_inv_consumes:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (consumes os p t d)\<close>
  unfolding input_ocaps_inv_def
proof (intro allI ballI)
  fix p1 p2 t1 s
  assume t1: \<open>t1 \<in> snd ` set (input (consumes os p t d) p1)\<close>
    and \<open>s \<in> set (intsum (consumes os p t d) p1 p2)\<close>
  hence s: \<open>s \<in> set (intsum os p1 p2)\<close> unfolding consumes_def add_caps_def by simp
  consider (input) \<open>t1 \<in> snd ` set (input os p1)\<close> | (consumed) \<open>p1 = p\<close> \<open>t1 = t\<close>
    using t1 unfolding consumes_def add_caps_def BENQ_def by (auto split: if_splits)
  thus \<open>t1 -+- s \<in> set (ocaps (consumes os p t d) p2)\<close>
  proof cases
    case input
    thus ?thesis using assms s unfolding input_ocaps_inv_def consumes_def add_caps_def by auto
  next
    case consumed
    thus ?thesis using s unfolding consumes_def add_caps_def by force
  qed
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

(* FIXME: move me *)
lemma step_Tau_pow_eqI:
  "op = op' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* op op'"
  by auto

lemma loop_move_all_data:
  assumes I: "intsum (os 2) = increment_summary (MyPair 0 1)"
    and N: "initia (os 2)"
    and C1: "input_ocaps_inv (os 2)"
  shows  "(step Tau)\<^sup>*\<^sup>*
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
           (logic_map (1 :: 3) (label_propagation_op (fold (\<lambda>(d, t) os. consumes os 1 t d) (map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
                 (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu (os 2) 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (1, 1)) (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))))))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (((drop_caps
                 (produces (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu os_label_prop 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (2, 1)) (os 2)))
                   (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1)) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
                 (map (\<lambda>t. Cap t 1) (ocaps (os 2) 1 @  (map (\<lambda>(d, t). t -+- MyPair 0 (Suc 0)) (cbufs (2, 1) @ outpu os_label_prop 1)))))\<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>)))))))"
  apply (cases "input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1")
  subgoal premises prems
    apply (cases "cbufs (1, 1) @ outpu (os 2) 1")
    subgoal
      using prems apply -
      apply (cases "ocaps (os 2) 1")
      subgoal
        apply (clarsimp simp add: produces_def drop_caps_def)
        apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
            apply (rule refl)+
        subgoal
          apply (clarsimp simp add: prems increment_op_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)
          done
        apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
           apply (rule refl)+
        subgoal
          by (auto simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (rule step_Tau_pow_eqI)
        apply (rule arg_cong2[where f="loop_op loop_wire"])
         apply simp
        apply (rule arg_cong[where f=comp_map])
        apply (rule arg_cong3[where f="comp_op comp_wire"])
          apply simp
        subgoal
          using prems apply -
          apply clarsimp
          apply (rule arg_cong[where f="logic_map 1"])
          apply (rule arg_cong[where f="label_propagation_op"])
          apply (auto simp add: fold_consumes produ_consumes_fold inter_consumes_fold consu_consumes_fold intsum_consumes_fold intro!: operator_state_eqI )
          done
        apply (rule arg_cong[where f="logic_map 2"])
        apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
        using prems apply -
        apply (auto simp add: produces_def drop_caps_def intro!: operator_state_eqI)
        done
      subgoal
        apply (rule converse_rtranclp_into_rtranclp) 
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Tau)
             apply (rule step_map_op)
              apply (rule step_increment_op_Silent)
                     apply simp
                    apply (rule refl)+
        using N apply assumption
              apply (rule refl)+
             apply simp
            apply (rule refl)+
          apply simp
         apply (rule refl)+
        apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
            apply (rule refl)+
        subgoal
          using prems by (fastforce simp add: prems increment_op_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
           apply (rule refl)+
        subgoal
          by (auto simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (rule step_Tau_pow_eqI)
        apply (rule arg_cong2[where f="loop_op loop_wire"])
         apply simp
        apply (rule arg_cong[where f=comp_map])
        apply (rule arg_cong3[where f="comp_op comp_wire"])
          apply simp
        subgoal
          using prems apply -
          apply clarsimp
          apply (rule arg_cong[where f="logic_map 1"])
          apply (rule arg_cong[where f="label_propagation_op"])
          apply (auto simp add: fold_consumes produ_consumes_fold inter_consumes_fold consu_consumes_fold intsum_consumes_fold intro!: operator_state_eqI )
          done
        apply (rule arg_cong[where f="logic_map 2"])
        apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
        using prems apply -
        apply (auto simp add: produces_def drop_caps_def intro!: operator_state_eqI)
        done
      done
    subgoal premises prems2
      apply (cases "ocaps (os 2) 1")
      subgoal
        apply (rule rtranclp_trans)
         apply (rule relpowp_imp_rtranclp[where n="length (outpu (os 2) 1)"]) 
         apply (rule step_tau_Out_pow_loop_op_steps_intro[where xs="map Inr (outpu (os 2) 1)"])
            apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Inr _) (Inr x)) ( outpu (os 2) 1)"])
              apply (rule refl)+
             apply force
            apply (rule steps_comp_op_R_Out[where xs="map Inr ( outpu (os 2) 1)"])
               apply (rule steps_map_op[where xs="map (\<lambda> x. Out _ (_ x)) ( outpu (os 2) 1)"])
                 apply (rule refl)+
                apply force
               apply (rule steps_increment_op_Write_Some[where ys=Nil])
                 apply simp
                apply (rule refl)+
            apply simp
            apply blast
           apply simp
          apply simp
         apply (rule refl)+

        apply (rule rtranclp_trans)
         apply (rule relpowp_imp_rtranclp[where n="length (cbufs (1, 1)) + length (outpu (os 2) 1)"]) 
         apply (rule step_tau_Inp_pow_loop_op_steps_intro[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1)"])
              apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl _) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1)"])
                apply (rule refl)+
               apply force
              apply (rule steps_comp_op_L_Inp[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1)"])
                 apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 1) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1)"])
                   apply (rule refl)+
                  apply simp
                 apply blast
                apply (rule refl)+
              apply (simp add: prems2)
             apply simp
        subgoal
          by (auto simp add: ran_def split: sum.splits)
           apply (simp add: BULK_BENQ_def)
          apply (simp add: BULK_BENQ_def)
         apply (rule refl)+

        apply (simp add: BULK_BENQ_def)
        apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
           apply (rule refl)+
        subgoal
          by (auto simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (rule step_Tau_pow_eqI)
        apply (rule arg_cong2[where f="loop_op loop_wire"])
         apply simp
        apply (rule arg_cong[where f=comp_map])
        apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
            apply (rule refl)+
        subgoal
          apply (clarsimp simp add: prems2 prems increment_op_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)
          using prems apply blast
          done
        apply (rule arg_cong3[where f="comp_op comp_wire"])
          apply simp
        subgoal
          using prems apply -
          apply clarsimp
          apply (rule arg_cong[where f="logic_map 1"])
          apply (rule arg_cong[where f="label_propagation_op"])
          apply (auto simp add: fold_consumes produ_consumes_fold inter_consumes_fold consu_consumes_fold intsum_consumes_fold intro!: operator_state_eqI )
          done
        subgoal
          apply (rule arg_cong[where f="logic_map 2"])
          apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
          using prems apply -
          apply (auto simp add: produces_def drop_caps_def C1 intro!: operator_state_eqI)
          done
        done
      subgoal premises prems3
        apply (rule rtranclp_trans)
         apply (rule converse_rtranclp_into_rtranclp) 
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Tau)
              apply (rule step_map_op)
               apply (rule step_increment_op_Silent)
        using prems3    apply simp
                     apply (rule refl)+
        using N apply assumption
               apply (rule refl)+
              apply simp
             apply (rule refl)+
           apply simp
          apply (rule refl)+

         apply (rule rtranclp_trans)
          apply (rule relpowp_imp_rtranclp[where n="length (outpu (os 2) 1)"]) 
          apply (rule step_tau_Out_pow_loop_op_steps_intro[where xs="map Inr (outpu (os 2) 1)"])
             apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Inr _) (Inr x)) ( outpu (os 2) 1)"])
               apply (rule refl)+
              apply force
             apply (rule steps_comp_op_R_Out[where xs="map Inr ( outpu (os 2) 1)"])
                apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 1) (_ x)) ( outpu (os 2) 1)"])
                  apply (rule refl)+
                 apply force
                apply (rule steps_increment_op_Write_Some[where ys=Nil])
                  apply simp
                 apply (rule refl)+
        using prems apply (fastforce simp add: prems2 prems prems3 comp_def split_beta filter_empty_conv)[1]
               apply (rule refl)+
             apply simp
             apply blast
            apply simp
           apply simp
          apply (rule refl)+

         apply (rule relpowp_imp_rtranclp[where n="length (cbufs (1, 1)) + length (outpu (os 2) 1)"]) 
         apply (rule step_tau_Inp_pow_loop_op_steps_intro[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1)"])
              apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl _) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1)"])
                apply (rule refl)+
               apply force
              apply (rule steps_comp_op_L_Inp[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1)"])
                 apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 1) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1)"])
                   apply (rule refl)+
                  apply simp
                 apply blast
                apply (rule refl)+
              apply (simp add: prems2)
             apply simp
        subgoal
          by (auto simp add: ran_def split: sum.splits)
           apply (simp add: BULK_BENQ_def)
          apply (simp add: BULK_BENQ_def)
         apply (rule refl)+

        apply (simp add: BULK_BENQ_def)
        apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
           apply (rule refl)+
        subgoal
          by (auto simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (rule step_Tau_pow_eqI)
        apply (rule arg_cong2[where f="loop_op loop_wire"])
         apply simp
        apply (rule arg_cong[where f=comp_map])
        apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
            apply (rule refl)+
        subgoal
          apply (clarsimp simp add: prems2 prems increment_op_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)
          using prems apply blast
          done
        apply (rule arg_cong3[where f="comp_op comp_wire"])
          apply simp
        subgoal
          using prems apply -
          apply clarsimp
          apply (rule arg_cong[where f="logic_map 1"])
          apply (rule arg_cong[where f="label_propagation_op"])
          apply (auto simp add: fold_consumes produ_consumes_fold inter_consumes_fold consu_consumes_fold intsum_consumes_fold intro!: operator_state_eqI )
          done
        subgoal
          apply (rule arg_cong[where f="logic_map 2"])
          apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
          using prems apply -
          apply (auto simp add: produces_def drop_caps_def C1 intro!: operator_state_eqI)
          done
        done
      done
    done
  subgoal premises prems for x xs
    apply (rule rtranclp_trans)
     apply (rule relpowp_imp_rtranclp[where n="length (outpu (os_label_prop) 1)"]) 
     apply (rule step_taus_loop_op_steps_intro)
      apply (rule step_tau_pow_map_op)
      apply (rule step_tau_Out_pow_comp_op_steps_intro[where xs="map Inr (outpu (os_label_prop) 1)" and p="Inr (1, 1)"])
         apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 1) (Inr x)) (outpu (os_label_prop) 1)"])
           apply (rule refl)+
          apply simp
         apply (rule steps_label_propagation_op_Write_Some[where ys=Nil])
           apply simp
          apply (rule refl)+
        apply simp
       apply simp
      apply (rule refl)+

    apply (rule rtranclp_trans)
     apply (rule relpowp_imp_rtranclp[where n="length (cbufs (2, 1)) + length (outpu (os_label_prop) 1)"]) 
     apply (rule step_taus_loop_op_steps_intro)
      apply (rule step_tau_pow_map_op)
      apply (rule step_tau_Inp_pow_comp_op_steps_intro[where xs="map Inr (cbufs (2, 1) @ outpu (os_label_prop) 1)" and p="Inr (2, 1)"])
           apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 1) (Inr x)) (cbufs (2, 1) @ outpu (os_label_prop) 1)"])
             apply (rule refl)+
            apply simp
           apply (rule steps_increment_op_Read_Some)
            apply (rule refl)+
          apply simp
         apply simp
        apply (simp add: BULK_BENQ_def)
       apply (simp add: BULK_BENQ_def)
      apply (rule refl)+

    apply (rule converse_rtranclp_into_rtranclp) 
     apply (rule step_Tau_loop_op)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Tau)
         apply (rule step_map_op)
          apply (rule step_increment_op_Silent)
    subgoal    
      apply (cases "input (os 2) 1")
      subgoal
        using prems apply -
        apply (clarsimp simp add:  I intsum_consumes_fold split: prod.splits)
        done
      subgoal for x xs
        apply (cases x)
        subgoal for d t
          using prems apply -
          apply (clarsimp simp add:  I intsum_consumes_fold split: prod.splits)
          apply hypsubst_thin
          using C1[unfolded input_ocaps_inv_def, rule_format, rotated, of "MyPair 0 1" 1 1, unfolded I, of t] apply -
          apply simp
          done
        done
      done
                apply (rule refl)+
           apply (simp add: N)
          apply (rule refl)+
         apply simp
        apply (rule refl)+
      apply simp
     apply (rule refl)+
    apply (simp flip: map_append)

    apply (rule rtranclp_trans)
     apply (rule rtranclp_trans)
      apply (rule relpowp_imp_rtranclp[where n="length (input (os 2) 1) + length (outpu (os 2) 1) + length (cbufs (2, 1)) + length (outpu (os_label_prop) 1)"]) 
      apply (rule step_tau_Out_pow_loop_op_steps_intro[where xs="map Inr (outpu (os 2) 1) @ map (\<lambda>(d, t). Inr (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1)"])
         apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Inr _) (Inr x)) (outpu (os 2) 1) @ map (\<lambda>(d, t). Out (Inr _) (Inr (d, t -+- MyPair 0 (Suc 0)))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1) "])
           apply (rule refl)+
          apply force
         apply (rule steps_comp_op_R_Out[where xs="map Inr (outpu (os 2) 1) @ map (\<lambda>(d, t). Inr (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1)"])
            apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 1) (Inr x)) ( outpu (os 2) 1) @ map (\<lambda>(d, t). Out (Some 1) (Inr (d, t -+- MyPair 0 (Suc 0)))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1)"])
              apply (rule refl)+
             apply force
            apply (rule steps_increment_op_Write_Some[where ys=Nil])
              apply simp
             apply (rule refl)+
            apply simp
            apply (simp add: comp_def split_beta filter_True input_fold_consumes)
           apply (rule refl)+
         apply force
        apply simp
       apply simp
      apply (rule refl)+
     apply (simp flip: map_append)

     apply (rule relpowp_imp_rtranclp[where n="length (cbufs (1, 1)) + length (outpu (os 2) 1) + length (input (os 2) 1) + length (cbufs (2, 1)) + length (outpu (os_label_prop) 1)"]) 
     apply (rule step_tau_Inp_pow_loop_op_steps_intro[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1))"])
          apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl _) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1) @ map (\<lambda>(d, t). Inp (Inl _) (Inr (d, t -+- MyPair 0 (Suc 0)))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1)"])
            apply (rule refl)+
           apply force
          apply (rule steps_comp_op_L_Inp[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1))"])
             apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 1) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1))"])
               apply (rule refl)+
              apply simp
             apply blast
            apply (rule refl)+
          apply simp
    subgoal
      by (simp add: prems split: prod.splits)
         apply simp
    subgoal
      by (auto simp add: ran_def split: sum.splits)
    subgoal
      by (simp add: BULK_BENQ_def)
    subgoal
      by (auto simp add: ran_def BULK_BENQ_def)
     apply (rule refl)+
    apply (simp flip: map_append concat_append filter_append add: I intsum_consumes_fold comp_def split_beta filter_True filter_False input_fold_consumes)
    apply (rule step_Tau_pow_eqI)
    apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
       apply (rule refl)+
    subgoal
      apply (clarsimp simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
      using prems apply (force simp add: prems BULK_BENQ_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)+
      done
    apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
        apply (rule refl)+
    subgoal
      apply (clarsimp simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
      using prems apply (force simp add: prems BULK_BENQ_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)+
      done
    apply (rule arg_cong2[where f="loop_op loop_wire"])
     apply simp
    apply (rule arg_cong[where f=comp_map])
    apply (rule arg_cong3[where f="comp_op comp_wire"])
      apply simp
     apply simp
    apply (rule arg_cong[where f="logic_map 2"])
    apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
    using prems apply -
    apply (auto simp add: prems  produces_def drop_caps_def C1 intro!: operator_state_eqI split: if_splits)
      apply (auto simp add: filter_empty_conv comp_def split_beta map_concat)
    done
  done

lemma loop_label_prop_input1:
  assumes N: "initia os_label_prop"
  shows  "(step Tau)\<^sup>*\<^sup>*
         (loop_op loop_wire cbufs
           (comp_map
             (comp_op
               comp_wire
               cbufs
               (logic_map (1 :: 3) (label_propagation_op (os_label_prop :: (nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state)))
               (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os 2) :: (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state))))))
         (loop_op loop_wire cbufs
           (comp_map
             (comp_op
               comp_wire
               cbufs
               (logic_map (1 :: 3) (label_propagation_op (fst (label_prop_input1_batched os_label_prop (input os_label_prop 1)))))
               (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))"
  apply (rule relpowp_imp_rtranclp[where n="length (input os_label_prop 1)"]) 
  apply (rule step_taus_loop_op_steps_intro)
   apply (rule step_tau_pow_map_op)
   apply (rule step_taus_L_pow_comp_op_steps_intro)
    apply (rule step_tau_pow_map_op)
    apply (rule step_compower_label_propagation_op_input1_eq_alt[where ys=Nil])
       apply simp
      apply simp
  using N apply assumption
    apply (rule refl)+
  done

abbreviation "CONSUMES p \<equiv> fold (\<lambda>(d, t) os. consumes os p t d)"

lemma CONSUMES_CONSUMES:
  "CONSUMES p xs (CONSUMES p ys os) =
   CONSUMES p (ys @ xs) os"
  unfolding fold_consumes
  by simp

lemma timestamps_CONSUMES[simp]:
  \<open>timestamps (CONSUMES p xs os) = timestamps os\<close>
  unfolding fold_consumes by simp

lemma graph_CONSUMES[simp]:
  \<open>label_propagation_state.graph (CONSUMES p xs os) = label_propagation_state.graph os\<close>
  unfolding fold_consumes by simp

lemma vertices_CONSUMES[simp]:
  \<open>vertices (CONSUMES p xs os) = vertices os\<close>
  unfolding fold_consumes by simp

lemma label_CONSUMES[simp]:
  \<open>label (CONSUMES p xs os) = label os\<close>
  unfolding fold_consumes by simp

lemma de1_CONSUMES[simp]:
  \<open>de1 (CONSUMES p xs os) = de1 os\<close>
  by simp

lemma all_vertices_CONSUMES[simp]:
  \<open>all_vertices (CONSUMES p xs os) = all_vertices os\<close>
  unfolding all_vertices_def by simp

lemma all_edges_CONSUMES[simp]:
  \<open>all_edges (CONSUMES p xs os) = all_edges os\<close>
  unfolding all_edges_def all_vertices_def neighbors_def by simp

lemma min_label_CONSUMES[simp]:
  \<open>min_label (CONSUMES p xs os) = min_label os\<close>
  unfolding min_label_def by simp

lemma input_CONSUMES:
  \<open>input (CONSUMES p xs os) = (input os)(p := input os p @ xs)\<close>
  unfolding fold_consumes by simp

lemma label_prop_upd_inv_CONSUMES_port1I:
  assumes inv: \<open>label_prop_upd_inv os\<close>
    and xs_inv: \<open>\<And>d t. (d, t) \<in> set xs \<Longrightarrow>
      myfst t \<in> set (timestamps os) \<and>
      fst (de1 os d) \<in> all_vertices os (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow> snd (de1 os d) \<in> cc_of (all_edges os q) (fst (de1 os d)))\<close>
  shows \<open>label_prop_upd_inv (CONSUMES (1 :: 2) xs os)\<close>
proof -
  let ?os' = \<open>CONSUMES (1 :: 2) xs os\<close>
  have input_eq: \<open>set (input ?os' 1) = set (input os 1) \<union> set xs\<close>
    by (simp add: input_CONSUMES)
  show ?thesis
    using inv xs_inv
    unfolding label_prop_upd_inv_def
    apply (auto simp add: input_eq)
    done
qed

definition label_prop_input1_loop_updates where
  \<open>label_prop_input1_loop_updates cbufs os_label_prop os =
    (let
      cbufs' = cbufs((2, 1) := [], (1, 1) := []);
      os_label_prop_consumed =
        CONSUMES 1
          (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
          (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>);
      os_label_prop' =
        fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1));
      os2' =
        drop_caps
          (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
            (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
          (map (\<lambda>t. Cap t 1)
            (ocaps (os 2) 1 @
              map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
                (cbufs (2, 1) @ outpu os_label_prop 1)))
          \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>;
      os' = os(2 := os2')
     in (cbufs', os_label_prop', os'))\<close>

lemma label_prop_input1_loop_updates_clears[simp]:
  assumes \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>cbufs' (1, 1) = []\<close>
    and \<open>cbufs' (2, 1) = []\<close>
    and \<open>input os_label_prop' 1 = []\<close>
    and \<open>input (os' 2) 1 = []\<close>
    and \<open>outpu (os' 2) 1 = []\<close>
  using assms
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


subsection \<open>Auxiliary lemmas for loop_updates termination\<close>

text \<open>
  The recursive branch after @{thm label_prop_input1_loop_updates_clears} can only be
  taken when the batched input-1 processing produced a non-empty port-1 output.  The
  following lemmas decompose that fact down to a strict label update and then lift it
  back to a strict decrease of @{const labels_measure}.
\<close>

lemma timestamps_label_prop_input1_step_state[simp]:
  \<open>timestamps (label_prop_input1_step_state os d t) = timestamps os\<close>
  unfolding label_prop_input1_step_state_def label_prop_label_record_update_def input_tl_def
  by (simp add: Let_def)

lemma all_edges_label_prop_input1_step_state[simp]:
  \<open>all_edges (label_prop_input1_step_state os d t) = all_edges os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma timestamps_fst_label_prop_input1_batched[simp]:
  \<open>timestamps (fst (label_prop_input1_batched os msgs)) = timestamps os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma all_edges_fst_label_prop_input1_batched[simp]:
  \<open>all_edges (fst (label_prop_input1_batched os msgs)) = all_edges os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)


lemma min_label_mono_time:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>t \<in> set (timestamps os)\<close>
    and \<open>t \<le> q\<close>
  shows \<open>min_label os q v \<le> min_label os t v\<close>
  using assms
  unfolding min_label_def
  by (intro Min.boundedI) auto


lemma label_prop_neighbor_batch_nonemptyD:
  fixes old_os neighbor_os label_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_neighbor_batch old_os neighbor_os label_os relevant_times vertex new_label event_time \<noteq> []\<close>
  obtains cur_t v' where
    \<open>cur_t \<in> set relevant_times\<close>
    \<open>v' \<in> set (neighbors neighbor_os cur_t vertex)\<close>
    \<open>new_label < min_label old_os cur_t vertex\<close>
    \<open>new_label < min_label label_os cur_t v'\<close>
proof -
  let ?batch_at = \<open>\<lambda>cur_t.
    if min_label old_os cur_t vertex > new_label
    then map (\<lambda>v'. (en1 old_os (v', new_label), Cap (MyPair cur_t (mysnd event_time)) 1))
      (filter (\<lambda>v'. min_label label_os cur_t v' > new_label)
        (neighbors neighbor_os cur_t vertex))
    else []\<close>
  have \<open>\<exists>cur_t\<in>set relevant_times. ?batch_at cur_t \<noteq> []\<close>
    using assms unfolding label_prop_neighbor_batch_def Let_def
    by (auto simp: concat_eq_Nil_conv)
  then obtain cur_t where cur_t_in: \<open>cur_t \<in> set relevant_times\<close>
    and batch_at_nonempty: \<open>?batch_at cur_t \<noteq> []\<close>
    by auto

  then have old_guard: \<open>new_label < min_label old_os cur_t vertex\<close>
    by (auto split: if_splits)
  have filter_nonempty:
    \<open>filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex) \<noteq> []\<close>
    using batch_at_nonempty old_guard by simp
  then obtain v' where filt_in:
    \<open>v' \<in> set (filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex))\<close>
    by (cases \<open>filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex)\<close>) auto
  then have v'_in: \<open>v' \<in> set (neighbors neighbor_os cur_t vertex)\<close>
    and label_guard: \<open>new_label < min_label label_os cur_t v'\<close>
    by auto
  show ?thesis
    using that[OF cur_t_in v'_in old_guard label_guard] .
qed





lemma label_prop_label_batch_nonemptyD:
  fixes old_os updated_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_label_batch old_os updated_os event_t vertex new_label event_time \<noteq> []\<close>
  obtains cur_t v' where
    \<open>cur_t \<in> set (timestamps old_os)\<close>
    \<open>event_t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors old_os cur_t vertex)\<close>
    \<open>new_label < min_label old_os cur_t vertex\<close>
    \<open>new_label < min_label updated_os cur_t v'\<close>
proof -
  obtain cur_t v' where cur_t_in: \<open>cur_t \<in> set (filter ((\<le>) event_t) (timestamps old_os))\<close>
    and v'_in: \<open>v' \<in> set (neighbors old_os cur_t vertex)\<close>
    and old_guard: \<open>new_label < min_label old_os cur_t vertex\<close>
    and updated_guard: \<open>new_label < min_label updated_os cur_t v'\<close>
    using assms unfolding label_prop_label_batch_def
    by (elim label_prop_neighbor_batch_nonemptyD)
  have cur_t_ts: \<open>cur_t \<in> set (timestamps old_os)\<close>
    and event_le: \<open>event_t \<le> cur_t\<close>
    using cur_t_in by auto
  show ?thesis
    using that[OF cur_t_ts event_le v'_in old_guard updated_guard] .
qed

lemma label_prop_neighbor_batch_memberD:
  fixes old_os neighbor_os label_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_neighbor_batch old_os neighbor_os label_os
    relevant_times vertex new_label event_time)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set relevant_times\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
  using assms unfolding label_prop_neighbor_batch_def
  by (auto simp: Let_def split: if_splits)

lemma label_prop_label_batch_memberD:
  fixes old_os updated_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_label_batch old_os updated_os event_t vertex new_label event_time)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set (timestamps old_os)\<close>
    \<open>event_t \<le> cur_t\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
proof -
  obtain cur_t where cur_t_in: \<open>cur_t \<in> set (filter ((\<le>) event_t) (timestamps old_os))\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
    using assms unfolding label_prop_label_batch_def
    by (elim label_prop_neighbor_batch_memberD)
  show ?thesis
    using that cur_t_in cap_eq by auto
qed

lemma label_prop_input1_step_batch_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
proof -
  obtain cur_t where cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
    and time_le: \<open>myfst t \<le> cur_t\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
    using assms unfolding label_prop_input1_step_batch_def Let_def
    by (elim label_prop_label_batch_memberD)
  show ?thesis
    using that[OF cur_t_in time_le cap_eq] .
qed


lemma label_prop_input1_step_batch_unfold:
  \<open>label_prop_input1_step_batch os d t =
    label_prop_label_batch os
      (label_prop_label_record_update (input_tl os 1) (myfst t) (fst (de1 os d))
        (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))))
      (myfst t) (fst (de1 os d)) (snd (de1 os d)) t\<close>
  unfolding label_prop_input1_step_batch_def Let_def by simp

lemma label_prop_input1_step_batch_nonempty_unfoldD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  shows \<open>label_prop_label_batch os
    (label_prop_label_record_update (input_tl os 1) (myfst t) (fst (de1 os d))
      (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))))
    (myfst t) (fst (de1 os d)) (snd (de1 os d)) t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  using assms[unfolded label_prop_input1_step_batch_unfold] by assumption

lemma label_prop_input1_step_batch_nonemptyD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  obtains v l cur_t v' where
    \<open>de1 os d = (v, l)\<close>
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors os cur_t v)\<close>
    \<open>l < min_label os cur_t v\<close>
    \<open>l < min_label
      (label_prop_label_record_update (input_tl os 1) (myfst t) v (min (min_label os (myfst t) v) l))
      cur_t v'\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?updated = \<open>label_prop_label_record_update (input_tl os 1) (myfst t) ?v
    (min (min_label os (myfst t) ?v) ?l)\<close>
  have de1_eq: \<open>de1 os d = (?v, ?l)\<close>
    by simp
  have batch_nonempty:
    \<open>label_prop_label_batch os ?updated (myfst t) ?v ?l t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
    by (rule label_prop_input1_step_batch_nonempty_unfoldD[OF assms])


  show ?thesis
  proof (rule label_prop_label_batch_nonemptyD[OF batch_nonempty])
    fix cur_t v'
    assume cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
      and time_le: \<open>myfst t \<le> cur_t\<close>
      and v'_in: \<open>v' \<in> set (neighbors os cur_t ?v)\<close>
      and old_guard: \<open>?l < min_label os cur_t ?v\<close>
      and updated_guard: \<open>?l < min_label ?updated cur_t v'\<close>
    show thesis
      using that[OF de1_eq cur_t_in time_le v'_in old_guard updated_guard] .
  qed
qed



lemma label_prop_input1_step_batch_nonempty_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> []\<close>
    and ts_t: \<open>myfst t \<in> set (timestamps os)\<close>
  obtains v l where
    \<open>de1 os d = (v, l)\<close>
    \<open>l < min_label os (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os 1) (myfst t) v l)
      (myfst t) v < min_label os (myfst t) v\<close>
proof -
  obtain v l cur_t v' where de1_eq: \<open>de1 os d = (v, l)\<close>
    and cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
    and time_le: \<open>myfst t \<le> cur_t\<close>
    and v'_in: \<open>v' \<in> set (neighbors os cur_t v)\<close>
    and strict_cur: \<open>l < min_label os cur_t v\<close>
    using label_prop_input1_step_batch_nonemptyD[OF assms(1)] by metis
  have mono: \<open>min_label os cur_t v \<le> min_label os (myfst t) v\<close>
    using min_label_mono_time[OF ts_t time_le] .
  have strict_myfst: \<open>l < min_label os (myfst t) v\<close>
    using strict_cur mono by linarith
  let ?updated = \<open>label_prop_label_record_update (input_tl os 1) (myfst t) v l\<close>
  have label_eq: \<open>label ?updated = (label os)(myfst t := (label os (myfst t))(v := l))\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have ts_eq: \<open>timestamps ?updated = timestamps os\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have l_in_set: \<open>l \<in> insert (label ?updated (myfst t) v)
      ((\<lambda>t'. label ?updated t' v) ` {t' \<in> set (timestamps ?updated). t' \<le> myfst t})\<close>
    using label_eq by simp
  have min_le_l: \<open>min_label ?updated (myfst t) v \<le> l\<close>
    using l_in_set unfolding min_label_def by (intro Min_le) auto
  have strict_update: \<open>min_label ?updated (myfst t) v < min_label os (myfst t) v\<close>
    using min_le_l strict_myfst by linarith
  show ?thesis
    using that[OF de1_eq strict_myfst strict_update] .
qed


lemma fst_label_prop_input1_batched_Cons_prefix:
  \<open>fst (label_prop_input1_batched os ((d, t) # pre)) =
    fst (label_prop_input1_batched (label_prop_input1_step_state os d t) pre)\<close>
  by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) pre\<close>) simp

lemma label_prop_input1_batched_batch_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
  obtains pre d t post os_pre where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  show ?case
  proof (cases \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>)
    case True
    show ?thesis
      by (rule Cons.prems(1)[of Nil d t msgs os]) (simp_all add: msg_eq True)
  next
    case False
    have tail_member:
      \<open>(x, cap) \<in> set (snd (label_prop_input1_batched (label_prop_input1_step_state os d t) msgs))\<close>
      using Cons.prems(2) False unfolding msg_eq
      by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs\<close>) simp
    show ?thesis
    proof (rule Cons.hyps[OF _ tail_member])
      fix pre da ta post os_pre
      assume msgs_tail: \<open>msgs = pre @ (da, ta) # post\<close>
        and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched (label_prop_input1_step_state os d t) pre)\<close>
        and member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre da ta)\<close>
      have msgs_eq: \<open>msg # msgs = (d, t) # pre @ (da, ta) # post\<close>
        using msgs_tail msg_eq by simp
      have os_pre_eq': \<open>os_pre = fst (label_prop_input1_batched os ((d, t) # pre))\<close>
        using os_pre_eq fst_label_prop_input1_batched_Cons_prefix[of os d t pre] by simp
      show thesis
      proof (rule Cons.prems(1)[of \<open>(d, t) # pre\<close> da ta post os_pre])
        show \<open>msg # msgs = ((d, t) # pre) @ (da, ta) # post\<close>
          using msgs_tail msg_eq by simp

        show \<open>os_pre = fst (label_prop_input1_batched os ((d, t) # pre))\<close>
          using os_pre_eq' .
        show \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre da ta)\<close>
          using member .
      qed


    qed
  qed
qed


lemma label_prop_input1_batched_produced_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(p, pt, n) \<in> set (map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
    (snd (label_prop_input1_batched os msgs)))\<close>
  obtains
    \<open>p = 1\<close>
    \<open>n = 1\<close>
    \<open>myfst pt \<in> set (timestamps os)\<close>
    \<open>MyPair (myfst pt) 0 \<le> pt\<close>
proof -
  obtain x cap where batch_member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and triple_eq: \<open>(p, pt, n) = (case cap of Cap t p \<Rightarrow> (p, t, 1))\<close>
    using assms by auto
  obtain pre d t post os_pre where os_pre_eq:
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using batch_member by (elim label_prop_input1_batched_batch_memberD)
  obtain cur_t where cur_t_pre: \<open>cur_t \<in> set (timestamps os_pre)\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
    using step_member by (elim label_prop_input1_step_batch_memberD)
  have cur_t: \<open>cur_t \<in> set (timestamps os)\<close>
    using cur_t_pre os_pre_eq by simp
  have fields: \<open>p = 1\<close> \<open>n = 1\<close> \<open>pt = MyPair cur_t (mysnd t)\<close>
    using triple_eq cap_eq by simp_all
  have pt_ts: \<open>myfst pt \<in> set (timestamps os)\<close>
    using fields cur_t by simp
  have pt_ge: \<open>MyPair (myfst pt) 0 \<le> pt\<close>
    using fields by simp
  show ?thesis
    using that[OF fields(1) fields(2) pt_ts pt_ge] .
qed


lemma outpu_fst_label_prop_input1_batched_nonemptyD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
  obtains x cap where
    \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    \<open>out cap = (1 :: 2)\<close>
proof -
  have filter_nonempty:
    \<open>filter (\<lambda>(x, cap). out cap = (1 :: 2)) (snd (label_prop_input1_batched os msgs)) \<noteq> []\<close>
    using assms by auto
  then obtain pair where pair_in:
    \<open>pair \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched os msgs)))\<close>
    by (cases \<open>filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched os msgs))\<close>) auto
  obtain x cap where pair: \<open>pair = (x, cap)\<close>
    by (cases pair)
  have batch_in: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and cap_out: \<open>out cap = (1 :: 2)\<close>
    using pair_in unfolding pair by auto
  show ?thesis
    using that[OF batch_in cap_out] .
qed


lemma label_prop_input1_batched_snd_member_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
  obtains pre d t post os_pre v l where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>de1 os_pre d = (v, l)\<close>
    \<open>myfst t \<in> set (timestamps os)\<close>
    \<open>l < min_label os_pre (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l)
      (myfst t) v < min_label os_pre (myfst t) v\<close>
proof -
  obtain pre d t post os_pre where msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_batch_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using member by (elim label_prop_input1_batched_batch_memberD)
  have step_batch_nonempty: \<open>label_prop_input1_step_batch os_pre d t \<noteq> []\<close>
    using step_batch_member by auto
  have dt_in_msgs: \<open>(d, t) \<in> set msgs\<close>
    using msgs_eq by simp
  have dt_in_input: \<open>(d, t) \<in> set (input os 1)\<close>
    using dt_in_msgs msgs_input by auto
  have ts_t_os: \<open>myfst t \<in> set (timestamps os)\<close>
    using dt_in_input INV unfolding label_prop_upd_inv_def by metis
  have ts_t_pre: \<open>myfst t \<in> set (timestamps os_pre)\<close>
    using ts_t_os os_pre_eq by simp
  obtain v l where de1_eq: \<open>de1 os_pre d = (v, l)\<close>
    and strict: \<open>l < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l)
        (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_batch_nonempty ts_t_pre
    by (elim label_prop_input1_step_batch_nonempty_strict_updateD)
  show ?thesis
    using that[OF msgs_eq os_pre_eq de1_eq ts_t_os strict update_strict] .
qed

lemma min_label_fst_label_prop_input1_batched_strict_timestamped_if_snd_member:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
  obtains q v where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
  oops



lemma label_prop_input1_batched_outpu_nonempty_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
  obtains pre d t post os_pre v l where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>de1 os_pre d = (v, l)\<close>
    \<open>myfst t \<in> set (timestamps os)\<close>
    \<open>l < min_label os_pre (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l)
      (myfst t) v < min_label os_pre (myfst t) v\<close>
proof -
  obtain x cap where batch_member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and cap_out: \<open>out cap = (1 :: 2)\<close>
    using assms(1,2) by (elim outpu_fst_label_prop_input1_batched_nonemptyD)
  obtain pre d t post os_pre where msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_batch_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using batch_member by (elim label_prop_input1_batched_batch_memberD)
  have step_batch_nonempty: \<open>label_prop_input1_step_batch os_pre d t \<noteq> []\<close>
    using step_batch_member by auto
  have dt_in_msgs: \<open>(d, t) \<in> set msgs\<close>
    using msgs_eq by simp
  have dt_in_input: \<open>(d, t) \<in> set (input os 1)\<close>
    using dt_in_msgs msgs_input by auto
  have ts_t_os: \<open>myfst t \<in> set (timestamps os)\<close>
    using dt_in_input INV unfolding label_prop_upd_inv_def by metis
  have ts_t_pre: \<open>myfst t \<in> set (timestamps os_pre)\<close>
    using ts_t_os os_pre_eq by simp
  obtain v l where de1_eq: \<open>de1 os_pre d = (v, l)\<close>
    and strict: \<open>l < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l)
        (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_batch_nonempty ts_t_pre
    by (elim label_prop_input1_step_batch_nonempty_strict_updateD)
  show ?thesis
    using that[OF msgs_eq os_pre_eq de1_eq ts_t_os strict update_strict] .
qed


lemma min_label_label_prop_label_record_update_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes l_le: \<open>l \<le> min_label os t v\<close>
  shows \<open>min_label (label_prop_label_record_update (input_tl os 1) t v l) q x \<le> min_label os q x\<close>
proof -
  let ?os' = \<open>label_prop_label_record_update (input_tl os 1) t v l\<close>
  have ts_eq: \<open>timestamps ?os' = timestamps os\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have label_eq: \<open>label ?os' = (label os)(t := (label os t)(v := l))\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  show ?thesis
  proof (cases \<open>x = v\<close>)
    case False
    have \<open>\<And>t'. label ?os' t' x = label os t' x\<close>
      using False label_eq by (auto simp: fun_upd_def)
    then show ?thesis
      unfolding min_label_def using ts_eq by simp
  next
    case True
    have l_le_label_t: \<open>l \<le> label os t v\<close>
    proof -
      have \<open>min_label os t v \<le> label os t v\<close>
        unfolding min_label_def by (intro Min_le) auto
      then show ?thesis using l_le by simp
    qed
    let ?S = \<open>insert (label os q v) ((\<lambda>t'. label os t' v) ` {t' \<in> set (timestamps os). t' \<le> q})\<close>
    let ?S' = \<open>insert (label ?os' q v) ((\<lambda>t'. label ?os' t' v) ` {t' \<in> set (timestamps ?os'). t' \<le> q})\<close>
    have S'_eq: \<open>?S' = insert (label ?os' q v) ((\<lambda>t'. label ?os' t' v) ` {t' \<in> set (timestamps os). t' \<le> q})\<close>
      using ts_eq by simp
    have fin_S: \<open>finite ?S\<close> by auto
    have fin_S': \<open>finite ?S'\<close> by auto
    have ne_S: \<open>?S \<noteq> {}\<close> by auto
    have bound: \<open>Min ?S' \<le> Min ?S\<close>
    proof (rule Min.boundedI[OF fin_S ne_S])
      fix y assume y_in: \<open>y \<in> ?S\<close>
      then consider (q_lbl) \<open>y = label os q v\<close>
        | (t_lbl) t' where \<open>t' \<in> set (timestamps os)\<close> \<open>t' \<le> q\<close> \<open>y = label os t' v\<close>
        by blast
      then show \<open>Min ?S' \<le> y\<close>
      proof cases
        case q_lbl
        show ?thesis
        proof (cases \<open>q = t\<close>)
          case True
          have \<open>label ?os' q v = l\<close> using True label_eq by simp
          then have \<open>l \<in> ?S'\<close> by auto
          then have \<open>Min ?S' \<le> l\<close> using fin_S' by (intro Min_le) auto
          also have \<open>l \<le> y\<close> using l_le_label_t q_lbl True by simp
          finally show ?thesis .
        next
          case False
          have \<open>label ?os' q v = label os q v\<close>
            using False label_eq by simp
          then have \<open>y \<in> ?S'\<close> using q_lbl by auto
          then show ?thesis using fin_S' by (intro Min_le) auto
        qed
      next
        case (t_lbl t')
        show ?thesis
        proof (cases \<open>t' = t\<close>)
          case True
          have lbl_t: \<open>label ?os' t v = l\<close> using label_eq by simp
          have t_mem: \<open>t \<in> {t'' \<in> set (timestamps ?os'). t'' \<le> q}\<close>
            using ts_eq t_lbl(1,2) True by simp
          have \<open>l \<in> ?S'\<close>
            using lbl_t t_mem image_eqI[where x=t and f=\<open>\<lambda>t'. label ?os' t' v\<close>] by auto
          then have \<open>Min ?S' \<le> l\<close> using fin_S' by (intro Min_le) auto
          also have \<open>l \<le> y\<close> using l_le_label_t t_lbl(3) True by simp
          finally show ?thesis .
        next
          case False
          have lbl_eq: \<open>label ?os' t' v = label os t' v\<close>
            using False label_eq by (simp add: fun_upd_def)
          have t'_mem: \<open>t' \<in> {t'' \<in> set (timestamps ?os'). t'' \<le> q}\<close>
            using ts_eq t_lbl(1,2) by simp
          have \<open>y \<in> ?S'\<close>
            using lbl_eq t'_mem t_lbl(3) image_eqI[where x=t' and f=\<open>\<lambda>t''. label ?os' t'' v\<close>] by auto
          then show ?thesis using fin_S' by (intro Min_le) auto
        qed
      qed
    qed
    have \<open>min_label ?os' q v = Min ?S'\<close>
      unfolding min_label_def by simp
    moreover have \<open>min_label os q v = Min ?S\<close>
      unfolding min_label_def by simp
    ultimately show ?thesis using bound True by simp
  qed
qed

lemma min_label_label_prop_input1_step_state_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  shows \<open>min_label (label_prop_input1_step_state os d t) q x \<le> min_label os q x\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?new = \<open>min (min_label os ?t1 ?v) ?l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 ?v ?new\<close>
  let ?batch = \<open>label_prop_label_batch os ?os'' ?t1 ?v ?l t\<close>
  have step_eq:
    \<open>label_prop_input1_step_state os d t =
       release_caps (drop_caps (produces (add_caps ?os'' (map snd ?batch)) ?batch) (map snd ?batch)) 1\<close>
    unfolding label_prop_input1_step_state_def Let_def by simp
  have new_le: \<open>?new \<le> min_label os ?t1 ?v\<close>
    by simp
  have \<open>min_label (label_prop_input1_step_state os d t) q x = min_label ?os'' q x\<close>
    unfolding step_eq by simp
  also have \<open>\<dots> \<le> min_label os q x\<close>
    using min_label_label_prop_label_record_update_le[OF new_le] .
  finally show ?thesis .
qed

lemma min_label_fst_label_prop_input1_batched_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  shows \<open>min_label (fst (label_prop_input1_batched os msgs)) q x \<le> min_label os q x\<close>
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons a ms)
  obtain d t where a_eq: \<open>a = (d, t)\<close> by (cases a) auto
  have unfold:
    \<open>fst (label_prop_input1_batched os (a # ms)) =
       fst (label_prop_input1_batched (label_prop_input1_step_state os d t) ms)\<close>
    using a_eq fst_label_prop_input1_batched_Cons_prefix[of os d t ms] by simp
  have ih: \<open>min_label (fst (label_prop_input1_batched (label_prop_input1_step_state os d t) ms)) q x
             \<le> min_label (label_prop_input1_step_state os d t) q x\<close>
    using Cons.hyps[of \<open>label_prop_input1_step_state os d t\<close>] by simp
  also have \<open>\<dots> \<le> min_label os q x\<close>
    using min_label_label_prop_input1_step_state_le[of os d t q x] .
  finally show ?case using unfold by simp
qed


lemma labels_inv_label_prop_input1_step_stateI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and input1: \<open>input os 1 = (d, t) # xs\<close>
  shows \<open>labels_inv (all_edges (label_prop_input1_step_state os d t) q)
    (min_label (label_prop_input1_step_state os d t) q)\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  let ?t1 = \<open>myfst t\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 v
    (min (min_label os ?t1 v) l)\<close>
  have step_eq: \<open>label_prop_input1_step_state os d t =
    release_caps (drop_caps (produces (add_caps ?os''
      (map snd (label_prop_label_batch os ?os'' ?t1 v l t)))
      (label_prop_label_batch os ?os'' ?t1 v l t))
      (map snd (label_prop_label_batch os ?os'' ?t1 v l t))) 1\<close>
    using de1_eq unfolding label_prop_input1_step_state_def Let_def by simp
  have \<open>labels_inv (all_edges ?os'' q) (min_label ?os'' q)\<close>
    by (rule labels_inv_input1_preserved_record_update_tl[OF labels inv _ de1_eq refl refl])
      (use input1 in simp)
  then show ?thesis
    unfolding step_eq by simp
qed

lemma label_prop_upd_inv_label_prop_input1_step_stateI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes inv: \<open>label_prop_upd_inv os\<close>
    and input1: \<open>input os 1 = (d, t) # xs\<close>
  shows \<open>label_prop_upd_inv (label_prop_input1_step_state os d t)\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  let ?t1 = \<open>myfst t\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 v
    (min (min_label os ?t1 v) l)\<close>
  have step_eq: \<open>label_prop_input1_step_state os d t =
    release_caps (drop_caps (produces (add_caps ?os''
      (map snd (label_prop_label_batch os ?os'' ?t1 v l t)))
      (label_prop_label_batch os ?os'' ?t1 v l t))
      (map snd (label_prop_label_batch os ?os'' ?t1 v l t))) 1\<close>
    using de1_eq unfolding label_prop_input1_step_state_def Let_def by simp
  have os''_inv: \<open>label_prop_upd_inv ?os''\<close>
    by (rule label_prop_upd_inv_input1_preserved[OF inv input1 _ de1_eq refl])
      (use input1 in \<open>simp_all add: label_prop_label_record_update_def input_tl_def\<close>)

  then show ?thesis
    unfolding step_eq by simp
qed

lemma labels_inv_fst_label_prop_input1_batched_prefixI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 1 = msgs @ rest\<close>
    and labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
  shows \<open>labels_inv (all_edges (fst (label_prop_input1_batched os msgs)) q)
    (min_label (fst (label_prop_input1_batched os msgs)) q)\<close>
  using input_eq labels inv
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have input1: \<open>input os 1 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have labels_step: \<open>\<And>q. labels_inv (all_edges ?step q) (min_label ?step q)\<close>
    by (rule labels_inv_label_prop_input1_step_stateI[OF Cons.prems(2) Cons.prems(3) input1])
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI[OF Cons.prems(3) input1])
  have input_step: \<open>input ?step 1 = msgs @ rest\<close>
    using input1 by simp
  have ih: \<open>labels_inv (all_edges (fst (label_prop_input1_batched ?step msgs)) q)
    (min_label (fst (label_prop_input1_batched ?step msgs)) q)\<close>
    by (rule Cons.hyps[OF input_step labels_step inv_step])
  then show ?case
    using msg_eq
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp

qed

lemma labels_inv_fst_label_prop_input1_batched_inputI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
  shows \<open>labels_inv (all_edges (fst (label_prop_input1_batched os (input os 1))) q)
    (min_label (fst (label_prop_input1_batched os (input os 1))) q)\<close>
  by (rule labels_inv_fst_label_prop_input1_batched_prefixI[where rest=Nil])
    (use assms in simp_all)

lemma fst_label_prop_input1_batched_append:
  \<open>fst (label_prop_input1_batched os (xs @ ys)) =
   fst (label_prop_input1_batched (fst (label_prop_input1_batched os xs)) ys)\<close>
proof (induct xs arbitrary: os)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  obtain d t where a_eq: \<open>a = (d, t)\<close> by (cases a)
  have step_eq:
    \<open>fst (label_prop_input1_batched os ((d, t) # (xs @ ys))) =
     fst (label_prop_input1_batched (label_prop_input1_step_state os d t) (xs @ ys))\<close>
    using fst_label_prop_input1_batched_Cons_prefix[of os d t \<open>xs @ ys\<close>] by simp
  have step_eq2:
    \<open>fst (label_prop_input1_batched os ((d, t) # xs)) =
     fst (label_prop_input1_batched (label_prop_input1_step_state os d t) xs)\<close>
    using fst_label_prop_input1_batched_Cons_prefix[of os d t xs] by simp
  show ?case
    using a_eq step_eq step_eq2
      Cons.hyps[of \<open>label_prop_input1_step_state os d t\<close>]
    by simp
qed

(* preservation lemma for label_prop_upd_inv through batched *)
lemma label_prop_upd_inv_fst_label_prop_input1_batched_preserved:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_upd_inv os\<close>
  shows \<open>label_prop_upd_inv (fst (label_prop_input1_batched os msgs))\<close>
  oops

lemma min_label_fst_label_prop_input1_batched_strict_if_output_nonempty:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
  obtains q v where
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
  oops


lemma min_label_fst_label_prop_input1_batched_strict_timestamped_if_output_nonempty:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
  obtains q v where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
proof -
  obtain pre d t post os_pre v l where
    msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and de1_pre_eq: \<open>de1 os_pre d = (v, l)\<close>
    and strict_pre: \<open>l < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l) (myfst t) v
        < min_label os_pre (myfst t) v\<close>
    apply (rule label_prop_input1_batched_outpu_nonempty_strict_updateD[OF out_empty out_nonempty, OF INV msgs_input])
    apply simp
    done   
  have de1_os_eq: \<open>de1 os d = (v, l)\<close>
    using de1_pre_eq os_pre_eq by simp
  have dt_in_msgs: \<open>(d, t) \<in> set msgs\<close>
    using msgs_eq by simp
  have dt_in_input: \<open>(d, t) \<in> set (input os 1)\<close>
    using dt_in_msgs msgs_input by auto
  have ts_t: \<open>myfst t \<in> set (timestamps os)\<close>
    and v_vertex_raw: \<open>fst (de1 os d) \<in> all_vertices os (myfst t)\<close>
    using dt_in_input INV unfolding label_prop_upd_inv_def by metis+
  have v_in_all: \<open>v \<in> all_vertices os (myfst t)\<close>
    using v_vertex_raw de1_os_eq by simp
  have v_in_edge: \<open>v \<in> edge_vertices (all_edges os (myfst t))\<close>
    using v_in_all edge_vertices_all_edges[OF INV] by simp

  let ?step = \<open>label_prop_input1_step_state os_pre d t\<close>
  let ?new = \<open>min (min_label os_pre (myfst t) v) l\<close>
  have new_eq_l: \<open>?new = l\<close> using strict_pre by simp
  have step_min:
    \<open>min_label ?step (myfst t) v =
       min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v ?new) (myfst t) v\<close>
    unfolding label_prop_input1_step_state_def Let_def
    using de1_pre_eq by simp
  have step_strict_pre:
    \<open>min_label ?step (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_min new_eq_l update_strict by simp

  have fst_unfold:
    \<open>fst (label_prop_input1_batched os msgs) =
     fst (label_prop_input1_batched ?step post)\<close>
    using msgs_eq os_pre_eq
      fst_label_prop_input1_batched_append[of os pre \<open>(d, t) # post\<close>]
      fst_label_prop_input1_batched_Cons_prefix[of os_pre d t post]
    by simp

  have step_le_os:
    \<open>min_label os_pre (myfst t) v \<le> min_label os (myfst t) v\<close>
    using os_pre_eq min_label_fst_label_prop_input1_batched_le[of os pre \<open>myfst t\<close> v]
    by simp

  have tail_le_step:
    \<open>min_label (fst (label_prop_input1_batched ?step post)) (myfst t) v
       \<le> min_label ?step (myfst t) v\<close>
    using min_label_fst_label_prop_input1_batched_le[of ?step post \<open>myfst t\<close> v] .

  have strict_full:
    \<open>min_label (fst (label_prop_input1_batched os msgs)) (myfst t) v < min_label os (myfst t) v\<close>
  proof -
    have \<open>min_label (fst (label_prop_input1_batched os msgs)) (myfst t) v
            = min_label (fst (label_prop_input1_batched ?step post)) (myfst t) v\<close>
      using fst_unfold by simp
    also have \<open>\<dots> \<le> min_label ?step (myfst t) v\<close>
      using tail_le_step .
    also have \<open>\<dots> < min_label os_pre (myfst t) v\<close>
      using step_strict_pre .
    also have \<open>\<dots> \<le> min_label os (myfst t) v\<close>
      using step_le_os .
    finally show ?thesis .
  qed

  show ?thesis
    using that[OF ts_t v_in_edge strict_full] .
qed

lemma labels_measure_strict_decrease_if_pointwise_le_and_less:
  fixes A :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and labels: \<open>labels_inv A l\<close>
    and labels': \<open>labels_inv A l'\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
    and strict: \<open>\<exists>v\<in>edge_vertices A. l' v < l v\<close>
  shows \<open>labels_measure A l' < labels_measure A l\<close>
proof -
  have rank_le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> rank A (l' v) \<le> rank A (l v)\<close>
    using le finite_edges
    unfolding rank_def
    by (intro card_mono; force)

  obtain v where v_in: \<open>v \<in> edge_vertices A\<close> and strict_v: \<open>l' v < l v\<close>
    using strict by auto
  have l'_in: \<open>l' v \<in> edge_vertices A\<close>
    using labels' v_in unfolding labels_inv_def cc_of_def by auto
  have rank_strict: \<open>rank A (l' v) < rank A (l v)\<close>
  proof -
    let ?S' = \<open>{y \<in> edge_vertices A. y < l' v}\<close>
    let ?S = \<open>{y \<in> edge_vertices A. y < l v}\<close>
    have subset: \<open>?S' \<subset> ?S\<close>
      using l'_in strict_v by auto
    moreover have \<open>finite ?S\<close>
      using finite_edges by auto
    ultimately show ?thesis
      unfolding rank_def by (simp add: psubset_card_mono)
  qed
  show ?thesis
    unfolding labels_measure_def
    by (rule sum_strict_mono_ex1[OF finite_edges]) (auto intro: rank_le v_in rank_strict)
qed


lemma labels_measure_strict_decrease_if_pointwise_le_and_less_same_edges:
  fixes A A' :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and labels: \<open>labels_inv A l\<close>
    and labels': \<open>labels_inv A l'\<close>
    and edges_eq: \<open>A' = A\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
    and strict: \<open>\<exists>v\<in>edge_vertices A. l' v < l v\<close>
  shows \<open>labels_measure A' l' < labels_measure A l\<close>
  using labels_measure_strict_decrease_if_pointwise_le_and_less
    [OF finite_edges labels labels' le strict]
    edges_eq by simp


lemma finite_all_vertices:
  shows \<open>finite (all_vertices os t)\<close>
  unfolding all_vertices_def by simp

lemma finite_edge_vertices_all_edges:
  shows \<open>finite (edge_vertices (all_edges os t))\<close>
proof -
  have \<open>edge_vertices (all_edges os t) \<subseteq> all_vertices os t\<close>
    by (rule edge_vertices_all_edges_subset_all_vertices)
  then show ?thesis
    using finite_all_vertices[of os t] by (rule finite_subset)
qed

lemma labels_measure_le_if_pointwise_le_same_edges:
  fixes A A' :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and edges_eq: \<open>A' = A\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
  shows \<open>labels_measure A' l' \<le> labels_measure A l\<close>
proof -
  have rank_le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> rank A (l' v) \<le> rank A (l v)\<close>
    using le finite_edges
    unfolding rank_def
    by (intro card_mono; force)
  have \<open>(\<Sum>v\<in>edge_vertices A. rank A (l' v)) \<le> (\<Sum>v\<in>edge_vertices A. rank A (l v))\<close>
    by (rule sum_mono) (auto intro: rank_le)
  then show ?thesis
    using edges_eq unfolding labels_measure_def by simp

qed


lemma labels_measure_fst_label_prop_input1_batched_le_at_timestamp:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
  shows \<open>labels_measure (all_edges os' t) (min_label os' t)
      \<le> labels_measure (all_edges os t) (min_label os t)\<close>
proof -
  have edges_eq: \<open>all_edges os' t = all_edges os t\<close>
    using os'_def by simp
  have finite_edges: \<open>finite (edge_vertices (all_edges os t))\<close>
    by (rule finite_edge_vertices_all_edges)
  have pointwise:
    \<open>\<And>v. v \<in> edge_vertices (all_edges os t) \<Longrightarrow> min_label os' t v \<le> min_label os t v\<close>
    using os'_def min_label_fst_label_prop_input1_batched_le[of os msgs t]
    by simp
  show ?thesis
    by (rule labels_measure_le_if_pointwise_le_same_edges
        [OF finite_edges edges_eq pointwise])
qed


lemma labels_measure_fst_label_prop_input1_batched_strict_at_some_timestamp_if_output_nonempty:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
    and out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu os' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os t) (min_label os t)\<close>
    and labels_os': \<open>\<And>t. labels_inv (all_edges os' t) (min_label os' t)\<close>
  obtains q where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
proof -
  have out_batch: \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    using os'_def out_nonempty by simp
  obtain q v where q_in: \<open>q \<in> set (timestamps os)\<close>
    and v_in: \<open>v \<in> edge_vertices (all_edges os q)\<close>
    and strict_v: \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
    using min_label_fst_label_prop_input1_batched_strict_timestamped_if_output_nonempty
      [OF out_empty out_batch INV msgs_input]
    by blast
  have pointwise:
    \<open>\<And>v. v \<in> edge_vertices (all_edges os q) \<Longrightarrow> min_label os' q v \<le> min_label os q v\<close>
    using os'_def min_label_fst_label_prop_input1_batched_le[of os msgs q]
    by simp
  have strict_ex:
    \<open>\<exists>v\<in>edge_vertices (all_edges os q). min_label os' q v < min_label os q v\<close>
    using os'_def v_in strict_v by auto
  have edges_eq: \<open>all_edges os' q = all_edges os q\<close>
    using os'_def by simp
  have finite_edges: \<open>finite (edge_vertices (all_edges os q))\<close>
    by (rule finite_edge_vertices_all_edges)
  have labels: \<open>labels_inv (all_edges os q) (min_label os q)\<close>
    using labels_os .
  have labels': \<open>labels_inv (all_edges os q) (min_label os' q)\<close>
    using labels_os'[of q] edges_eq by simp
  have strict_measure:
    \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
    by (rule labels_measure_strict_decrease_if_pointwise_le_and_less_same_edges
        [OF finite_edges labels labels' edges_eq pointwise strict_ex])
  show ?thesis
    using that[OF q_in strict_measure] .
qed


lemma sum_list_strict_mono_ex1:
  fixes xs :: \<open>'a list\<close>
    and f g :: \<open>'a \<Rightarrow> nat\<close>
  assumes le: \<open>\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x\<close>
    and strict: \<open>\<exists>x\<in>set xs. f x < g x\<close>
  shows \<open>sum_list (map f xs) < sum_list (map g xs)\<close>
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have le_a: \<open>f a \<le> g a\<close>
    using Cons.prems(1) by simp
  have le_tail: \<open>\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x\<close>
    using Cons.prems(1) by simp
  have tail_le: \<open>sum_list (map f xs) \<le> sum_list (map g xs)\<close>
    using le_tail
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons b ys)
    have head_le: \<open>f b \<le> g b\<close>
      using Cons.prems by simp
    have tail_le': \<open>sum_list (map f ys) \<le> sum_list (map g ys)\<close>
      using Cons.hyps Cons.prems by simp
    show ?case
      using head_le tail_le' by simp
  qed

  from Cons.prems(2) consider (head) \<open>f a < g a\<close> | (tail) \<open>\<exists>x\<in>set xs. f x < g x\<close>
    by auto
  then show ?case
  proof cases
    case head
    then show ?thesis
      using tail_le by simp
  next
    case tail
    have tail_strict: \<open>sum_list (map f xs) < sum_list (map g xs)\<close>
      using Cons.hyps[OF le_tail tail] .
    then show ?thesis
      using le_a by simp
  qed
qed


lemma labels_measure_sum_fst_label_prop_input1_batched_decreases_if_output_nonempty:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
    and out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu os' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os t) (min_label os t)\<close>
    and labels_os': \<open>\<And>t. labels_inv (all_edges os' t) (min_label os' t)\<close>
  shows \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os' t) (min_label os' t))
          (timestamps os'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os t) (min_label os t))
          (timestamps os))\<close>
proof -
  have ts_eq: \<open>timestamps os' = timestamps os\<close>
    using os'_def by simp
  have pointwise:
    \<open>\<And>t. t \<in> set (timestamps os) \<Longrightarrow>
      labels_measure (all_edges os' t) (min_label os' t)
        \<le> labels_measure (all_edges os t) (min_label os t)\<close>
    using labels_measure_fst_label_prop_input1_batched_le_at_timestamp[OF os'_def]
    by simp
  obtain q where q_in: \<open>q \<in> set (timestamps os)\<close>
    and strict_q: \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
    using labels_measure_fst_label_prop_input1_batched_strict_at_some_timestamp_if_output_nonempty
      [OF os'_def out_empty out_nonempty INV msgs_input labels_os labels_os']
    by blast
  have strict_ex:
    \<open>\<exists>t\<in>set (timestamps os). labels_measure (all_edges os' t) (min_label os' t)
      < labels_measure (all_edges os t) (min_label os t)\<close>
    using q_in strict_q by blast
  have \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os' t) (min_label os' t))
          (timestamps os))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os t) (min_label os t))
          (timestamps os))\<close>
    by (rule sum_list_strict_mono_ex1[OF pointwise strict_ex])
  then show ?thesis
    using ts_eq by simp
qed


lemma labels_inv_label_prop_input1_loop_updatesI:
  fixes os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES: \<open>(cbufs', os_label_prop', os') =
      label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and msgs_inv: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  shows \<open>labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed (input ?consumed 1))\<close>
    using UPDATES
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
  proof (rule label_prop_upd_inv_CONSUMES_port1I)
    show \<open>label_prop_upd_inv ?base\<close>
      using INV by simp
  next
    fix d t
    assume m: \<open>(d, t) \<in> set ?msgs\<close>
    show \<open>myfst t \<in> set (timestamps ?base) \<and>
      fst (de1 ?base d) \<in> all_vertices ?base (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow> snd (de1 ?base d) \<in> cc_of (all_edges ?base q) (fst (de1 ?base d)))\<close>
      using msgs_inv[OF m] by simp
  qed
  have labels_consumed: \<open>\<And>t. labels_inv (all_edges ?consumed t) (min_label ?consumed t)\<close>
    using labels_os by simp
  show ?thesis
    using os_label_prop'_eq labels_inv_fst_label_prop_input1_batched_inputI
      [OF labels_consumed inv_consumed, of t]
    by simp
qed

lemma label_prop_input1_loop_updates_sum_measure_decrease_if_label_output_nonempty:
  fixes os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES: \<open>(cbufs', os_label_prop', os') =
      label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and out_nonempty: \<open>outpu os_label_prop' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and msgs_inv: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  shows \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop' t) (min_label os_label_prop' t))
          (timestamps os_label_prop'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop t) (min_label os_label_prop t))
          (timestamps os_label_prop))\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed (input ?consumed 1))\<close>
    using UPDATES
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have consumed_outpu: \<open>outpu ?consumed 1 = []\<close>
    unfolding fold_consumes by simp
  have msgs_input_self: \<open>set (input ?consumed 1) \<subseteq> set (input ?consumed 1)\<close>
    by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
  proof (rule label_prop_upd_inv_CONSUMES_port1I)
    show \<open>label_prop_upd_inv ?base\<close>
      using INV by simp
  next
    fix d t
    assume m: \<open>(d, t) \<in> set ?msgs\<close>
    show \<open>myfst t \<in> set (timestamps ?base) \<and>
      fst (de1 ?base d) \<in> all_vertices ?base (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow> snd (de1 ?base d) \<in> cc_of (all_edges ?base q) (fst (de1 ?base d)))\<close>
      using msgs_inv[OF m] by simp
  qed
  have labels_consumed: \<open>\<And>t. labels_inv (all_edges ?consumed t) (min_label ?consumed t)\<close>
    using labels_os by simp
  have labels_os': \<open>\<And>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updatesI[OF UPDATES INV msgs_inv labels_os])
  have consumed_decrease:
    \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop' t) (min_label os_label_prop' t))
        (timestamps os_label_prop'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges ?consumed t) (min_label ?consumed t))
        (timestamps ?consumed))\<close>
    using labels_measure_sum_fst_label_prop_input1_batched_decreases_if_output_nonempty
      [of os_label_prop' ?consumed \<open>input ?consumed 1\<close>]
      os_label_prop'_eq consumed_outpu out_nonempty inv_consumed msgs_input_self labels_consumed labels_os'
    by simp
  have consumed_same:
    \<open>sum_list (map (\<lambda>t. labels_measure (all_edges ?consumed t) (min_label ?consumed t))
        (timestamps ?consumed)) =
      sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop t) (min_label os_label_prop t))
        (timestamps os_label_prop))\<close>
    unfolding fold_consumes min_label_def all_edges_def all_vertices_def neighbors_def
    by simp
  show ?thesis
    using consumed_decrease consumed_same by simp
qed



lemma loop_move_all_data_label_prop_input1:
  assumes NO: "initia os_label_prop"
    and I: "intsum (os 2) = increment_summary (MyPair 0 1)"
    and N: "initia (os 2)"
    and C1: "input_ocaps_inv (os 2)"
  shows  "(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op (os_label_prop :: (nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state)))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os 2) :: (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state))))))
     (loop_op loop_wire ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2, 1) := [], Inr (1, 1) := []))
       (comp_map
         (comp_op
           comp_wire
           ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2, 1) := [], Inr (1, 1) := []))
           (logic_map (1 :: 3) (label_propagation_op (fst (label_prop_input1_batched
                      (CONSUMES 1 (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
                        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))
                      (input
                        (CONSUMES 1 (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
                          (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))
                        1)))))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (drop_caps (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2)) (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1)) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
                 (map (\<lambda>t. Cap t 1) (ocaps (os 2) 1 @ map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0)) (cbufs (2, 1) @ outpu os_label_prop 1)))
                \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>))))))"
  apply (rule rtranclp_trans)
   apply (rule loop_move_all_data)
  using I apply assumption
  using N apply assumption
  using C1 apply assumption
  apply (rule rtranclp_trans)
   apply (rule loop_label_prop_input1)
   apply (simp add: NO)
  apply (simp flip: map_append fold_append only: CONSUMES_CONSUMES)
  apply (rule step_Tau_pow_eqI)
  apply (simp only: append_assoc)
  done

lemma loop_move_all_data_label_prop_input1_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES:
    \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and NO: \<open>initia os_label_prop\<close>
    and I: \<open>intsum (os 2) = increment_summary (MyPair 0 1)\<close>
    and N: \<open>initia (os 2)\<close>
    and C1: "input_ocaps_inv (os 2)"
  shows  \<open>(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop'))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os' 2))))))\<close>
proof -
  let ?buf = \<open>case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))\<close>
  let ?buf' = \<open>?buf(Inr (2, 1) := [], Inr (1, 1) := [])\<close>
  let ?os_label_prop_consumed =
    \<open>CONSUMES 1
      (cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
      (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  let ?os_label_prop_new =
    \<open>fst (label_prop_input1_batched ?os_label_prop_consumed (input ?os_label_prop_consumed 1))\<close>
  let ?os2_new =
    \<open>drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
  have old_step: \<open>(step Tau)\<^sup>*\<^sup>*
      (loop_op loop_wire ?buf
        (comp_map
          (comp_op comp_wire ?buf
            (logic_map (1 :: 3) (label_propagation_op os_label_prop))
            (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))
      (loop_op loop_wire ?buf'
        (comp_map
          (comp_op comp_wire ?buf'
            (logic_map (1 :: 3) (label_propagation_op ?os_label_prop_new))
            (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ?os2_new)))))\<close>
    using loop_move_all_data_label_prop_input1[where os=os and os_label_prop=os_label_prop and cbufs=cbufs]
      NO I N C1 by blast
  have buf_eq:
    \<open>case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)) = ?buf'\<close>
    using UPDATES unfolding label_prop_input1_loop_updates_def Let_def
    by (auto simp add: fun_eq_iff split: sum.splits prod.splits)
  have states_eq:
    \<open>os_label_prop' = ?os_label_prop_new \<and> os' 2 = ?os2_new\<close>
    using UPDATES unfolding label_prop_input1_loop_updates_def Let_def by simp
  have target_eq:
    \<open>loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
      (comp_map
        (comp_op comp_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
          (logic_map (1 :: 3) (label_propagation_op os_label_prop'))
          (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os' 2))))) =
     loop_op loop_wire ?buf'
      (comp_map
        (comp_op comp_wire ?buf'
          (logic_map (1 :: 3) (label_propagation_op ?os_label_prop_new))
          (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ?os2_new))))\<close>
    using buf_eq states_eq by metis

  show ?thesis
    using old_step target_eq by metis

qed

lemma label_prop_input1_loop_updates_timestmaps:
  "label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os') \<Longrightarrow>
   timestamps os_label_prop' = timestamps os_label_prop"
  unfolding label_prop_input1_loop_updates_def
  by clarsimp

function loop_updates where
  "loop_updates (cbufs :: 3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf) os_label_prop (os :: 3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state) = (
   if label_prop_upd_inv os_label_prop \<and> (\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
      (myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @ input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop))
   then
     let (cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os in
     if input os_label_prop' 1 = []
     then (cbufs', os_label_prop', os')
     else loop_updates cbufs' os_label_prop' os'
   else (cbufs((2, 1) := [], (1, 1) := []), os_label_prop, os)
   )"

  by auto
termination
  apply (relation "measure (\<lambda>(cbufs, os_label_prop, os). sum_list (map (\<lambda> t. labels_measure (all_edges os_label_prop t) (min_label os_label_prop t)) (timestamps os_label_prop))) ")
   apply simp
  subgoal for cbufs os_label_prop os x cbufs' y os_label_prop' os'
    apply (clarsimp del: disjCI split: prod.splits)
    apply (rule label_prop_input1_loop_updates_sum_measure_decrease_if_label_output_nonempty[rotated, where cbufs'=cbufs' and cbufs=cbufs and os=os])
    subgoal
      apply (rule ccontr)
      apply (metis label_prop_input1_loop_updates_clears(3))
      done
       apply simp_all
    subgoal sorry
    done
  done 


declare loop_updates.simps[simp del]

lemma step_tau_pow_loop_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES:
    \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and NO: \<open>initia os_label_prop\<close>
    and I: \<open>intsum (os 2) = increment_summary (MyPair 0 1)\<close>
    and N: \<open>initia (os 2)\<close>
    and C1: "input_ocaps_inv (os 2)"
    and L: \<open>label_prop_upd_inv os_label_prop\<close>
    and M: \<open>\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and T: \<open>(myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @ input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop))\<close>
  shows  \<open>(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop'))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os' 2))))))\<close>
  using assms apply -
  apply (induct cbufs os_label_prop os rule: loop_updates.induct)
  apply simp
  subgoal premises prems for cbufs os_label_prop os
    using prems(2-) apply -
    apply (subst (asm) loop_updates.simps)
    apply (clarsimp split: prod.splits if_splits)
    subgoal
      apply (rule loop_move_all_data_label_prop_input1_updates)
          apply (rule sym)
          apply assumption+
        apply simp_all
      done
    subgoal for cbufs' os_label_prop' os'
      apply (rule rtranclp_trans)
       apply (rule loop_move_all_data_label_prop_input1_updates)
           apply (rule sym)
           apply assumption+
         apply simp_all
      apply (rule prems(1)[simplified, OF refl])
                apply simp_all
             apply (subst loop_updates.simps)
             apply simp
            apply (metis (no_types, lifting) label_prop_input1_loop_updates_clears(3))+
      done
    done
  done

lemma step_tau_pow_loop_updates_alt:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes NO: \<open>initia os_label_prop\<close>
    and I: \<open>intsum (os 2) = increment_summary (MyPair 0 1)\<close>
    and N: \<open>initia (os 2)\<close>
    and C1: "input_ocaps_inv (os 2)"
    and L: \<open>label_prop_upd_inv os_label_prop\<close>
    and M: \<open>\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and T: \<open>(myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @ input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop))\<close>
  shows  \<open>(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (fst (loop_updates cbufs os_label_prop os) x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (fst (loop_updates cbufs os_label_prop os) x)))
           (logic_map (1 :: 3) (label_propagation_op (fst (snd (loop_updates cbufs os_label_prop os)))))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((snd (snd (loop_updates cbufs os_label_prop os))) 2))))))\<close>
proof -
  let ?res = \<open>loop_updates cbufs os_label_prop os\<close>
  have updates: \<open>(fst ?res, fst (snd ?res), snd (snd ?res)) = ?res\<close>
    by (cases ?res) simp
  show ?thesis
    by (rule step_tau_pow_loop_updates[OF updates NO I N C1 L M T])
qed

lemma loop_op_label_propagation_op_increment_op:
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


lemma fst_label_prop_input1_loop_updates[simp]:
  \<open>fst (label_prop_input1_loop_updates cbufs os_label_prop os) =
   cbufs((2, 1) := [], (1, 1) := [])\<close>
  unfolding label_prop_input1_loop_updates_def Let_def by simp

lemma fst_loop_updates[simp]:
  \<open>fst (loop_updates cbufs os_label_prop os) = cbufs((2, 1) := [], (1, 1) := [])\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  obtain cbufs' os_label_prop' os' where triple:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have cbufs'_eq: \<open>cbufs' = cbufs((2, 1) := [], (1, 1) := [])\<close>
    using triple by (metis fst_conv fst_label_prop_input1_loop_updates)
  have idemp_eq:
    \<open>(cbufs((2, 1) := [], (1, 1) := []))((2, 1) := [], (1, 1) := []) =
     cbufs((2, 1) := [], (1, 1) := [])\<close>
    by simp
  have ih_applied:
    \<open>input os_label_prop' 1 \<noteq> [] \<Longrightarrow>
     label_prop_upd_inv os_label_prop \<and>
     (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
     myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
       input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
       \<subseteq> set (timestamps os_label_prop) \<Longrightarrow>
     fst (loop_updates (cbufs((2, 1) := [], (1, 1) := [])) os_label_prop' os')
       = cbufs((2, 1) := [], (1, 1) := [])\<close>

    using 1(1)[OF _ triple[symmetric] refl refl] cbufs'_eq idemp_eq by metis
  show ?case
    by (subst loop_updates.simps) (auto simp: triple cbufs'_eq ih_applied)
qed

lemma produ_fst_snd_label_prop_input1_loop_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes os_label_prop_consumed_def:
    \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
    produ os_label_prop @
      map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
        (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
  using os_label_prop_consumed_def
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp add: fold_consumes split_beta split: capability.splits)


lemma produ_fst_snd_loop_updates_prefix:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  obtains produced where
    \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) = produ os_label_prop @ produced\<close>
    \<open>\<forall>p pt n. (p, pt, n) \<in> set produced \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
proof (induct cbufs os_label_prop os arbitrary: thesis rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
      input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
  show ?case
  proof (cases ?good)
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os =
      (cbufs((2, 1) := [], (1, 1) := []), os_label_prop, os)\<close>
      by (subst loop_updates.simps) (use False in auto)
    show ?thesis
    proof (rule "1.prems"[of Nil])
      show \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) = produ os_label_prop @ []\<close>
        using loop_eq by simp
      show \<open>\<forall>p pt n. (p, pt, n) \<in> set [] \<longrightarrow>
        p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
        by simp
    qed
  next
    case True
    obtain cbufs' :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
      and os_label_prop' :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
      and os' :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
      where step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
      map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
        (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
    let ?consumed = \<open>CONSUMES 1 ?msgs (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
    let ?produced1 = \<open>map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
      (snd (label_prop_input1_batched ?consumed (input ?consumed 1)))\<close>
    have consumed_ts: \<open>timestamps ?consumed = timestamps os_label_prop\<close>
      by simp
    have produced1_props: \<open>\<forall>p pt n. (p, pt, n) \<in> set ?produced1 \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
    proof (intro allI impI)
      fix p pt n
      assume \<open>(p, pt, n) \<in> set ?produced1\<close>
      then show \<open>p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
        by (elim label_prop_input1_batched_produced_memberD) (simp add: consumed_ts)
    qed
    have step_prod0:
      \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
        produ os_label_prop @ ?produced1\<close>
      unfolding label_prop_input1_loop_updates_def Let_def
      by (simp add: fold_consumes split_beta split: capability.splits)
    have step_prod: \<open>produ os_label_prop' = produ os_label_prop @ ?produced1\<close>
      using step_prod0 step by simp
    have step_os_label_prop':
      \<open>os_label_prop' = fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
      using step by simp
    have step_ts: \<open>timestamps os_label_prop' = timestamps os_label_prop\<close>
      using step_os_label_prop'
      unfolding label_prop_input1_loop_updates_def Let_def
      by (simp add: fold_consumes split_beta)
    show ?thesis
    proof (cases \<open>input os_label_prop' 1 = []\<close>)
      case True
      have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step True in auto)
      show ?thesis
      proof (rule "1.prems"[of \<open>?produced1 @ []\<close>])
        show \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
          produ os_label_prop @ (?produced1 @ [])\<close>
          using loop_eq step_prod by simp
        show \<open>\<forall>p pt n. (p, pt, n) \<in> set (?produced1 @ []) \<longrightarrow>
          p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
          using produced1_props by simp
      qed
    next
      case False
      obtain produced2 where rec_prod:
        \<open>produ (fst (snd (loop_updates cbufs' os_label_prop' os'))) =
          produ os_label_prop' @ produced2\<close>
        and rec_props: \<open>\<forall>p pt n. (p, pt, n) \<in> set produced2 \<longrightarrow>
          p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop') \<and> MyPair (myfst pt) 0 \<le> pt\<close>
        using "1.hyps"[OF \<open>?good\<close> step[symmetric] refl refl False]
        by blast
      have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs' os_label_prop' os'\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step False in auto)
      show ?thesis
      proof (rule "1.prems"[of \<open>?produced1 @ produced2\<close>])
        show \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
          produ os_label_prop @ (?produced1 @ produced2)\<close>
          using loop_eq rec_prod step_prod by (simp add: append_assoc)
        show \<open>\<forall>p pt n. (p, pt, n) \<in> set (?produced1 @ produced2) \<longrightarrow>
          p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
          using produced1_props rec_props step_ts by auto
      qed
    qed
  qed
qed


lemma produ_fst_snd_loop_updatesE:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
    and os_label_prop_consumed_def:
    \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  obtains produced where
    \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @
        produced\<close>
    \<open>\<forall>p pt n. (p, pt, n) \<in> set (
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @ produced) \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
proof -
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
      input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
  have good: ?good
    using INV LABELS TIMES by simp
  obtain cbufs' :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and os_label_prop' :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os' :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    where step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  let ?produced1 = \<open>map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
    (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
  have consumed_ts: \<open>timestamps os_label_prop_consumed = timestamps os_label_prop\<close>
    using os_label_prop_consumed_def by simp
  have produced1_props: \<open>\<forall>p pt n. (p, pt, n) \<in> set ?produced1 \<longrightarrow>
    p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
  proof (intro allI impI)
    fix p pt n
    assume \<open>(p, pt, n) \<in> set ?produced1\<close>
    then show \<open>p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
      by (elim label_prop_input1_batched_produced_memberD) simp
  qed
  have step_prod0:
    \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @ ?produced1\<close>
    using os_label_prop_consumed_def
    unfolding label_prop_input1_loop_updates_def Let_def
    by (simp add: fold_consumes split_beta split: capability.splits)
  have step_prod: \<open>produ os_label_prop' = produ os_label_prop @ ?produced1\<close>
    using step_prod0 step by simp
  have step_os_label_prop':
    \<open>os_label_prop' = fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
    using step by simp
  have step_ts: \<open>timestamps os_label_prop' = timestamps os_label_prop_consumed\<close>
    using step_os_label_prop' os_label_prop_consumed_def
    unfolding label_prop_input1_loop_updates_def Let_def
    by (simp add: fold_consumes split_beta)
  show ?thesis
  proof (cases \<open>input os_label_prop' 1 = []\<close>)
    case True
    have \<open>loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
      by (subst loop_updates.simps) (use good step True in auto)
    then have prod_eq: \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @ ?produced1 @ []\<close>
      using step_prod by simp
    show ?thesis
      by (rule that[OF prod_eq]) (use produced1_props in simp)
  next
    case False
    obtain produced2 where rec_prod:
      \<open>produ (fst (snd (loop_updates cbufs' os_label_prop' os'))) =
        produ os_label_prop' @ produced2\<close>
      and rec_props: \<open>\<forall>p pt n. (p, pt, n) \<in> set produced2 \<longrightarrow>
        p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop') \<and> MyPair (myfst pt) 0 \<le> pt\<close>
      by (elim produ_fst_snd_loop_updates_prefix)
    have \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs' os_label_prop' os'\<close>
      by (subst loop_updates.simps) (use good step False in auto)
    then have prod_eq: \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @ ?produced1 @ produced2\<close>
      using rec_prod step_prod by (simp add: append_assoc)
    have props: \<open>\<forall>p pt n. (p, pt, n) \<in> set (?produced1 @ produced2) \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
      using produced1_props rec_props step_ts by auto
    show ?thesis
      by (rule that[OF prod_eq props])
  qed
qed

lemma produ_fst_snd_loop_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
    and os_label_prop_consumed_def:
    \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>\<exists>produced.
    produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @
        produced \<and>
    (\<forall>p pt n. (p, pt, n) \<in> set produced \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt) \<and>
    (\<forall>p pt n. (p, pt, n) \<in> set (
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))) \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt)\<close>
proof -
  obtain produced where prod_eq:
    \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @
        produced\<close>
    and props: \<open>\<forall>p pt n. (p, pt, n) \<in> set (
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @ produced) \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
    by (rule produ_fst_snd_loop_updatesE
        [where os = os and os_label_prop = os_label_prop
          and os_label_prop_consumed = os_label_prop_consumed and cbufs = cbufs,
          OF INV LABELS TIMES os_label_prop_consumed_def])
  show ?thesis
    using prod_eq props 
    by (smt (verit, del_insts) append.assoc in_set_conv_decomp label_prop_input1_batched_produced_memberD)
qed





lemma extract_prog_three_fold:
  shows  \<open>extract_progress 0 eds (snd (obtain_progress os0)) @
   extract_progress 1 eds (snd (obtain_progress os1)) @
   extract_progress 2 eds (snd (obtain_progress os2)) =
   extract_prog [0 :: 3, 1, 2] eds (\<lambda> nid. if nid = 0 then os0 else if nid = 1 then os1 else os2)\<close>
  by (simp add: extract_prog_def)
lemma buff_sim_aux[simp]:
  "(\<lambda>p'. if Inr (1, 0) = p'
                    then drop (length (cbufs (1, 0)) -+- length (outpu (os 0) 0) -+- length (filter is_Data (ltaken n lxs)))
                          (((\<lambda>p'a. if p' = p'a then map Inr (outpu (os 0) 0) @ map (\<lambda>ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs)) else []) >>
                            case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
                            p')
                    else ((\<lambda>p'. if Inr (1, 0) = p' then map Inr (outpu (os 0) 0) @ map (\<lambda>ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs)) else []) >>
                          case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
                          p') = case_sum (\<lambda>x. []) (\<lambda>x. map Inr ((cbufs((1, 0) := [])) x))"
  apply (rule ext)+
  unfolding BULK_BENQ_def
  apply (auto split: sum.splits)
  done


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
    \<open>input_ocaps_inv (os 2)\<close>
    \<open>initia (os 2)\<close>
    and buffers_inv:
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    and dataplane_inv:
    \<open>dataplane_tracker_inv os cbufs sg\<close>
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
    \<open>\<forall>t \<in> time ` lset lxs \<union> snd ` set (chns (1, 0)) \<union> set (ocaps (os 1) 0). mysnd t = 0\<close>
    \<open>label_prop_upd_inv os_label_prop\<close>
    \<open>input_ocaps_inv (os 1)\<close>
  shows \<open>set_op S D (dataflow_op sg (G_op os_input os_label_prop (os 2) cbufs))
         \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms
proof (coinduction arbitrary: S SO SP D lxs os os_input os_label_prop cbufs chns sg T G V L
    rule: weakBisimWeakUptoBisimCong)
  case SIM1
  note subgraph_inv = SIM1(1,2)
    and os_inv = SIM1(3-11)
    and buffers_inv = SIM1(12)
    and dataplane_inv = SIM1(13)
    and csets_inv = SIM1(14,15)
    and input_stream_inv = SIM1(16)
    and label_prop_inv = SIM1(17-)
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
                            apply (simp add: dataflow_tree_to_operator_def)
        using SIM1 by (simp_all add: comp_def)
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
        using buffers_inv label_prop_inv(4) apply (simp add: BULK_BENQ_def subgraph_inv(1) outputs_at_target_raw_summary)
        using label_prop_inv(5) apply (simp add: os_inv(4,7) operator_state.defs(3))
         apply (rule label_prop_inv(6))
        apply (clarsimp simp add: dataflow_tree_to_operator_def intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>] arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule arg_cong2[where f=\<open>\<lambda>buf op. comp_op _ buf _ op\<close>])
         apply (fastforce simp add: BENQ_def)
        apply (rule loop_op_buf_cong[OF refl])
         apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
         apply (rule comp_op_buf_cong[OF refl refl refl])
         apply (simp add: ran_comp_wire BENQ_def)
        apply (simp add: ran_loop_wire BENQ_def)
        done
      subgoal for p d t
        apply (subgoal_tac \<open>p = 0\<close>)
         defer
         apply (clarsimp simp add: ran_loop_wire dest!: num2_neq(2))
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
        apply (rule exI[of _ \<open>os(1 := consumes (os 1) p t d)\<close>])
        apply (rule exI[of _ os_input])
        apply (rule exI[of _ \<open>consumes os_label_prop p t d\<close>])
        apply (rule exI[of _ \<open>BTL (1, p) cbufs\<close>])
        apply (intro exI conjI)
                            defer
                            apply (rule refl)
        using subgraph_inv(1) apply simp
                            apply (simp_all add: operator_state.defs(3) subgraph_inv(2) os_inv)
                     apply (simp add: consumes_def add_caps_def BENQ_def)
                     apply (intro conjI)
                         apply (simp add: raw_summary_def fun_eq_iff)
                        apply (rule refl)
                       apply (rule refl)
                      apply (rule refl)
                     apply (rule refl)
        using os_inv(1,5)
                    apply (simp add: ty1_check_def operator_state.defs(3) BTL_def)
                    apply blast
        using os_inv(1,4-6)
                   apply (simp add: ty1_check_def label_prob_ty2_check_def operator_state.defs(3) BTL_def BHD_def)
                   apply (erule conjE)
                   apply (rotate_tac 9)
                   apply (drule spec[of _ 0])
                   apply (simp add: Ball_def)
                   apply (meson img_fst in_fst_imageE in_set_tlD)
                  apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (1, p))\<close>])
                  apply (simp add: BHD_def)
                 apply (simp add: csets_inv(1) buffers_inv os_inv(4,7) operator_state.defs(3) consumes_def)
                apply (simp add: csets_inv(2))
               apply (rule input_stream_inv)
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) apply (simp add: os_inv(4,7) operator_state.defs(3) consumes_def)
        subgoal
          using dataplane_inv unfolding dataplane_tracker_inv_def
          apply (simp add: label_prop_inv(3))
          apply (elim exE conjE)
          subgoal premises prems for caps
            using prems(2,10-12) prems(4)[symmetric] unfolding front_inv_def imp_front_inv_def chnls_imp_front_inv_def
            apply simp
            apply (rule contrapos_pp[OF _ frontier_less_equal_exit_scope, rotated, where t1=\<open>t -+- MyPair 0 1\<close>])
             apply simp
            apply (drule spec2[of _ 1 1])
            apply (drule spec[of _ \<open>Loc 1 (Trg 1)\<close>])
            apply (drule spec2[of _ 1 0])
            apply (drule bspec[of _ _ \<open>(d, t)\<close>])
             apply (simp add: BULK_BENQ_def BHD_def)
             apply (rule disjI1)
             apply (metis list.set_sel(1))
            apply (rule frontier_less_equal_le_trans[rotated])
             apply (rule order.trans)
              apply assumption
             apply assumption
            apply (rule frontier_less_equal_ifrontier_trans[OF D, where l=\<open>Loc 1 (Trg 0)\<close>])
            using path_weight_loop_increment apply (simp add: subgraph_inv(1))
            apply simp
            done
          done
        subgoal premises prems
          using prems(2) prems(4)[symmetric] buffers_inv label_prop_inv(4) hd_in_set
          by (fastforce simp add: raw_summary_def BULK_BENQ_def BHD_def)
        using label_prop_inv(5) apply (simp add: os_inv(4,7) operator_state.defs(3) consumes_def)
          apply (subst label_prop_upd_inv_cong; simp add: BENQ_def)
         apply (rule inputs_ocaps_inv_consumes[OF label_prop_inv(6)])
        apply (clarsimp simp add: dataflow_tree_to_operator_def intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>] arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule arg_cong2[where f=\<open>\<lambda>buf op. comp_op _ buf _ op\<close>])
         apply (simp add: BTL_def fun_eq_iff map_tl split: sum.splits)
        apply (rule loop_op_buf_cong[OF refl])
         apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
         apply (rule comp_op_buf_cong[OF refl refl refl])
         apply (simp add: ran_comp_wire BTL_def)
        apply (simp add: ran_loop_wire BTL_def)
        done
      subgoal for os_input'
        apply (clarsimp simp add: ooo_input_op_logic_def split: llist.splits event.splits)
        subgoal
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.rtrancl_refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (unfold R_def)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ \<open>os(0 := drop_caps (os 0) (map (\<lambda>t. Cap t 0) (ocaps (os 0) 0)))\<close>])
          apply (rule exI[of _ os_input'])
          apply (intro exI conjI)
                              defer
                              apply (rule refl)
                              apply (rule subgraph_inv(1))
                              apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: operator_state.defs(3) drop_caps_def)
          using os_inv(2) apply simp
          using os_inv(3) apply simp
          using os_inv(4) apply simp
          using os_inv(5) apply (simp add: ty1_check_def)
          using os_inv(4,6) apply fast
          using os_inv(7) apply simp
          using os_inv(8) apply simp
          using os_inv(9) apply simp
          using buffers_inv apply fast
          using dataplane_tracker_inv_drop_caps_all[OF D G subgraph_inv(2) dataplane_inv] apply blast
                   apply (simp add: csets_inv(1) buffers_inv os_inv(1,4) operator_state.defs(3))
                  apply (simp add: csets_inv(2))
                 apply (simp add: ocaps_drop_caps_all(1))
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          apply (simp add: dataflow_tree_to_operator_def os_inv(4))
          done
        subgoal for lxs' t v w
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.rtrancl_refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (unfold R_def)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ lxs'])
          apply (rule exI[of _ \<open>os(0 := produce (os 0) (Cap t 0) [en1 os_input (v, w)])\<close>])
          apply (rule exI[of _ os_input'])
          apply (rule exI)
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ \<open>BENQ (1, 0) (en1 os_input (v, w), t) chns\<close>])
          apply (intro exI conjI)
                              defer
                              apply (rule refl)
                              apply (rule subgraph_inv(1))
                              apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: produce_def operator_state.defs(3))
          using os_inv(2) apply (simp add: produce_def)
          using os_inv(3) apply (simp add: produce_def)
          using os_inv(4) apply simp
          using os_inv(1,5) apply (simp add: produce_def ty1_check_def operator_state.defs(3))
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: produce_def)

          using os_inv(8) apply simp
          using os_inv(9) apply simp
                     apply (simp add: buffers_inv BENQ_def BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def fun_eq_iff produce_def)
                    apply (rule dataplane_tracker_inv_produce_singleton[OF D G subgraph_inv(2) dataplane_inv, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: timely_input_stream_def os_inv(1) operator_state.defs(3))
                    apply (rule refl)
                   apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3))
                  apply (simp add: csets_inv(2))
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) produce_def)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BENQ_def)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          apply (simp add: dataflow_tree_to_operator_def os_inv(4))
          done
        subgoal for lxs' t
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.rtrancl_refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (unfold R_def)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ lxs'])
          apply (rule exI[of _ \<open>os(0 := drop_cap (os 0) (Cap t 0))\<close>])
          apply (rule exI[of _ os_input'])
          apply (intro exI conjI)
                              defer
                              apply (rule refl)
                              apply (rule subgraph_inv(1))
                              apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: drop_cap_def operator_state.defs(3))
          using os_inv(2) apply (simp add: drop_cap_def)
          using os_inv(3) apply (simp add: drop_cap_def)
          using os_inv(4) apply simp
          using os_inv(5) apply (simp add: drop_cap_def ty1_check_def)
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: drop_cap_def)
          using os_inv(8) apply simp
          using os_inv(9) apply simp
                     apply (simp add: buffers_inv)
                    apply (rule dataplane_tracker_inv_drop_cap[OF D G subgraph_inv(2) dataplane_inv, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: timely_input_stream_def os_inv(1) operator_state.defs(3))
                    apply (rule refl)
                   apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
                   apply (subst (1 2) icoll_lshift)
          using timely_input_stream_expires_le input_stream_inv apply blast
          using timely_input_stream_expires_le input_stream_inv apply blast
                   apply simp
                  apply (simp add: csets_inv(2))
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) drop_cap_def)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          apply (simp add: dataflow_tree_to_operator_def os_inv(4))
          done
        subgoal for lxs' t
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.rtrancl_refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (unfold R_def)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ lxs'])
          apply (rule exI[of _ \<open>os(0 := add_cap (os 0) 0 t)\<close>])
          apply (rule exI[of _ os_input'])
          apply (intro exI conjI)
                              defer
                              apply (rule refl)
                              apply (rule subgraph_inv(1))
                              apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: add_cap_def operator_state.defs(3))
          using os_inv(2) apply (simp add: add_cap_def)
          using os_inv(3) apply (simp add: add_cap_def)
          using os_inv(4) apply simp
          using os_inv(5) apply (simp add: add_cap_def ty1_check_def)
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: add_cap_def)
          using os_inv(8) apply simp
          using os_inv(9) apply simp
                     apply (simp add: buffers_inv)
                    apply (rule dataplane_tracker_inv_add_cap[OF D dataplane_inv G, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) timely_input_stream_def)
                    apply (rule refl)
                   apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
                   apply (subst (1 2) icoll_lshift)
          using timely_input_stream_expires_le input_stream_inv apply blast
          using timely_input_stream_expires_le input_stream_inv apply blast
                   apply (simp add: add_cap_def)
                  apply (simp add: csets_inv(2))
          using input_stream_inv apply (force simp add: os_inv(1) operator_state.defs(3) add_cap_def)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def add_cap_def)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          apply (simp add: dataflow_tree_to_operator_def os_inv(4))
          done
        done
      subgoal for d t xs
        apply (intro exI conjI)
         apply (rule rtranclp.rtrancl_refl)
        apply (intro relcomppI)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def[simplified])
        apply (rule exI[of _ S])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(1 := xs)\<rparr>)\<close>])
        apply (rule exI[of _ \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := xs)\<rparr>\<close>])
        apply (rule exI[of _ \<open>BENQ (2, 1) (d, t) cbufs\<close>])
        apply (rule exI[of _ sg])
        apply (intro conjI)
                           apply (clarsimp simp add: dataflow_tree_to_operator_def os_inv(1)
            intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>]
            arg_cong[where f=\<open>map_op _ _\<close>])
                           apply (rule comp_op_buf_cong[OF refl refl])
                            apply (rule loop_op_buf_cong[OF refl])
                            apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                            apply (rule comp_op_buf_cong[OF refl refl refl])
                            apply (simp add: ran_comp_wire)
                            apply (simp add: ran_loop_wire BENQ_def)
                           apply (clarsimp simp add: BENQ_def ran_def split: sum.splits)
                           apply (metis obj_sumE prod.exhaust)
                          apply (simp add: cimage_cUn csets_inv buffers_inv outputs_at_target_raw_summary subgraph_inv(1) os_inv(1,4) operator_state.defs(3) BENQ_def BULK_BENQ_def all_edges_def all_vertices_def neighbors_def)
                         apply (rule subgraph_inv(1))
                        apply (rule subgraph_inv(2))
                       apply (simp add: os_inv(2))
                      apply (simp add: os_inv(3))
                     apply (simp add: os_inv(4) operator_state.defs(3))
        using os_inv(1,5) apply (simp add: BENQ_def ty1_check_def)
        using os_inv(6) apply (simp add: BENQ_def label_prob_ty2_check_def)
        using os_inv(7) apply simp
        using os_inv(8) apply simp
        using os_inv(9) apply simp
               apply (rule dataplane_tracker_inv_update_outputs[OF dataplane_inv _ _ _ _ G, where nid=1 and p=1 and xs=\<open>[(d, t)]\<close>])
                  apply (simp add: os_inv(4) operator_state.defs(3))
                 apply (simp add: fun_upd_def)
                apply (simp add: BENQ_def)
               apply (simp add: subgraph_inv(1) raw_summary_def antichain_from_list_singleton)
              apply (simp add: input_stream_inv)
        subgoal
          using label_prop_inv
          by (simp add: all_edges_def all_vertices_def min_label_def neighbors_def labels_inv_def labels_stable_def)
        subgoal premises aux
          apply safe
          using label_prop_inv(2)
          by (simp add: all_edges_def all_vertices_def min_label_def neighbors_def labels_inv_def labels_stable_def)
        subgoal premises aux
          using label_prop_inv(3)
          by auto
        subgoal premises aux
          using label_prop_inv(4)
          by (simp add: buffers_inv BENQ_def BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
        subgoal premises aux
          using label_prop_inv(5)
          unfolding label_prop_upd_inv_def
          by (auto del: disjCI)
        subgoal premises aux
          using label_prop_inv(6)
          unfolding input_ocaps_inv_def
          by auto
        done
      subgoal for d t
        apply (intro exI conjI relcomppI)
           apply (rule rtranclp.rtrancl_refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def[simplified])
        apply (rule exI[of _ S])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(2 := consumes (os 2) 1 t d)\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ \<open>BTL (2, 1) cbufs\<close>])
        apply (rule exI[of _ sg])
        apply (intro conjI)
                           apply (clarsimp simp add: dataflow_tree_to_operator_def os_inv(1)
            intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>]
            arg_cong[where f=\<open>map_op _ _\<close>])
                           apply (rule comp_op_buf_cong[OF refl refl])
                            apply (rule loop_op_buf_cong[OF refl])
                            apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                            apply (rule comp_op_buf_cong[OF refl refl refl])
                            apply (simp add: ran_comp_wire BTL_def map_tl)
                            apply (simp add: ran_loop_wire BTL_def)
                           apply (simp add: BTL_def ran_def split: sum.splits)
                           apply (metis prod.exhaust sum.exhaust)
                          apply (simp add: csets_inv buffers_inv BULK_BENQ_def BENQ_def BTL_def cimage_cUn)
                         apply (rule subgraph_inv(1))
                        apply (rule subgraph_inv(2))
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply force
        using os_inv(1,5) apply (simp add: ty1_check_def operator_state.defs(3) BTL_def)
        using os_inv(4,6) apply (simp add:  label_prob_ty2_check_def operator_state.defs(3) BTL_def)
        using os_inv(7) apply force
        using os_inv(8) apply (simp add: inputs_ocaps_inv_consumes)
        using os_inv(9) apply simp
               apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (2, 1))\<close>])
               apply (simp add: BHD_def)
        using input_stream_inv apply simp
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) apply (simp add: os_inv(4,7) operator_state.defs(3) consumes_def)
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def)
         apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        done
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
          using os_inv(8) apply simp
          using os_inv(9) apply simp
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
                by (metis UnCI myprod.collapse)
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
            using label_prop_inv(4) buffers_inv
            unfolding drop_caps_def release_caps_def produces_def
            by (auto simp add: BULK_BENQ_def outputs_at_target_raw_summary inputs_at_target_def subgraph_inv(1) dest!: in_set_list_diffD)
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
                         apply (simp add: buffers_inv BULK_BENQ_def inputs_at_target_def)
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
                using os_inv(8) apply simp
                using os_inv(9) apply simp
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
                subgoal premises
                  using label_prop_inv(4)
                  by (auto simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def input_tl_def release_caps_def drop_caps_def add_caps_def label_prop_edge_record_update_def label_prop_edge_batch_def label_prop_neighbor_batch_def dest!: in_set_list_diffD in_set_tlD)
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
                using os_inv(8) apply simp
                using os_inv(9) apply simp
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
                  by (auto simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def input_tl_def release_caps_def drop_caps_def add_caps_def label_prop_label_batch_def label_prop_neighbor_batch_def dest!: in_set_list_diffD)
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
      subgoal for os_incr'
        apply (clarsimp simp add: increment_op_logic_def if_splits)
        apply (intro exI conjI relcomppI)
           apply (rule rtranclp.rtrancl_refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def[simplified])
        apply (rule exI[of _ S])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(2 := os_incr')\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ cbufs])
        apply (rule exI[of _ sg])
        apply (intro conjI)
                           apply (simp add: dataflow_tree_to_operator_def os_inv(1))
                          apply (simp add: csets_inv buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def cimage_cUn)
                         apply (rule subgraph_inv(1))
                        apply (rule subgraph_inv(2))
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply force
        using os_inv(1,5) apply simp
                   apply (rule os_inv(6))
        using os_inv(7) apply force
        using os_inv(7,8) apply (clarsimp simp add: input_ocaps_inv_def drop_caps_def produces_def raw_summary_def filter_False)
        using os_inv(9) apply simp
        subgoal
          using dataplane_tracker_inv_produces_drops[OF D refl refl refl refl refl _ _ _ _ G subgraph_inv(2) dataplane_inv,
              where nid=2 and drops=\<open>(\<lambda>_. [])(1 := ocaps (os 2) 1)\<close> and produs=\<open>map (\<lambda>(_, t). (1, t + MyPair 0 1, 1)) (input (os 2) 1)\<close>
                and oputs=\<open>(\<lambda>_. [])(1 := map (\<lambda>(d, t). (d, t + MyPair 0 1)) (input (os 2) 1))\<close>]
          apply -
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using os_inv(7,8) apply (clarsimp simp add: split_beta input_ocaps_inv_def raw_summary_def)
          apply (drule meta_mp)
          using os_inv(7,8) apply (fastforce simp add: split_beta input_ocaps_inv_def raw_summary_def)

          apply (drule meta_mp)
           apply (clarsimp simp add: comp_def split_beta filter_True filter_False)
          apply (subst dataplane_tracker_inv_clean_input)
           defer
           apply assumption
          apply (clarsimp simp add: drop_caps_def produces_def comp_def split_beta fun_eq_iff)
          apply (rule conjI; clarsimp)
          subgoal for p
            by (cases \<open>p = 1\<close>; clarsimp dest!: num2_neq(2) simp add: filter_True filter_False comp_def)
          subgoal for p
            by (cases \<open>p = 1\<close>; clarsimp simp add: filter_True filter_False)
          done
        using input_stream_inv apply simp
             apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
         apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
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
        using os_inv(8) apply simp
        using os_inv(9) apply simp
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
          by (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
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
  note subgraph_inv = SIM2(1,2)
    and os_inv = SIM2(3-11)
    and buffers_inv = SIM2(12)
    and dataplane_inv = SIM2(13)
    and csets_inv = SIM2(14,15)
    and input_stream_inv = SIM2(16)
    and label_prop_inv = SIM2(17-)
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
          using os_inv(8) apply simp
          using os_inv(9) apply simp
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
            by (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
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
            using dataplane_inv[unfolded dataplane_tracker_inv_def, simplified] apply -
            apply clarsimp
            subgoal premises dt_inv for cap
              using propagate_all_frontier_change_multiplicities_c_imp_correctnessE[OF D, of "pt_tr sg" "extract_progress 0 (graph_to_nxt (antichain_from_list \<circ>\<circ> raw_summary)) (snd (obtain_progress os_input))", unfolded subgraph_inv(1), simplified]
              apply -
              apply (drule meta_mp)
              subgoal
                using dt_inv(8)[unfolded propagation_inv_def subgraph_inv(1)] by auto
              apply (drule meta_mp)
              subgoal
                using dt_inv(8)[unfolded propagation_inv_def subgraph_inv(1)] by auto
              apply (drule meta_mp)
              subgoal
                using dt_inv(8)[unfolded propagation_inv_def subgraph_inv(1)] by auto
              apply (drule meta_mp)
              subgoal 
                unfolding extract_progress_def
                apply (clarsimp simp add: obtain_progress_def subgraph_inv(1,2) set_map_filter split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
                subgoal for l t
                  using loc_3_2_cases[of l]
                  using dt_inv(7)[unfolded change_deltas_inv_def]
                  by (fastforce del: disjCI split: option.splits)
                done
              apply (drule meta_mp)
              subgoal 
                apply clarsimp
                subgoal for l t m
                  apply (subst frontier_less_equal_iff2[symmetric])
                  apply (rule frontier_less_equal_le_trans[rotated])
                   apply (rule dt_inv(5)[unfolded imp_front_inv_def, rule_format, of l])
                  apply (rule dt_inv(9)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, simplified, rule_format, where xs=Nil and x="(l, t, m)" and nid=0, simplified])
                  apply (clarsimp simp add: obtain_progress_def subgraph_inv(1,2) set_map_filter split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
                  done
                done
              apply (drule meta_mp)
              subgoal
                using raw_summary_no_self_loop by auto
              apply clarsimp
              subgoal premises first_propa for c'

                apply (intro exI conjI[rotated])
                 apply (intro relcomppI)
                   apply (rule bisim_refl)
                  defer
                  apply (rule wbisim_refl)
                 apply (rule wstep_trans(1))
                  apply (rule transitive_closurep_trans'(2))


                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=0])
                      apply (subst dataflow_tree_to_operator_def)
                      apply simp
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Out)
                          apply (rule step_map_op)
                           apply (rule step_ooo_input_op_Write_None_alt)
                            apply (rule refl)+
                          apply simp
                         apply fastforce
                        apply (rule refl)+
                      apply simp
                     apply (rule refl)+

                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
                        apply (rule step_map_op)
                         apply (rule step_comp_op_R_Inp)
                            apply (rule step_Inp_loop_op)
                             apply (rule step_map_op)
                              apply (rule step_comp_op_L_Inp)
                                apply (rule step_map_op)
                                 apply (rule step_label_propagation_op_Read_None)
                                  apply (rule refl)+
                                apply simp
                               apply (rule refl)+
                             apply simp
                            apply (auto simp add: ran_def split: sum.splits option.splits prod.splits)[1]
                           apply (auto simp add: ran_def split: sum.splits option.splits prod.splits)[1]
                          apply (rule refl)+
                        apply simp
                       apply (simp add:   subgraph_inv)
                using first_propa(1) apply assumption
                      apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule relpowp_imp_rtranclp[where n="n"]) 
                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply simp
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_taus_L_pow_comp_op_steps_intro)
                      apply (rule step_tau_pow_map_op)
                      apply (rule step_compower_ooo_input_op_iterates_n[where p=0])
                subgoal
                  using input_stream_inv 
                  by (simp add: os_inv(1) obtain_progress_def operator_state.defs)
                subgoal
                  by simp
                subgoal
                  using os_inv(3)
                  by (simp add: os_inv(1) obtain_progress_def operator_state.defs)
                subgoal
                  using stream_move
                  by (simp add: os_inv(1) obtain_progress_def operator_state.defs)
                       apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule relpowp_imp_rtranclp[where n="(length (outpu (os 0) 0)) + length (filter is_Data (ltaken n lxs))"]) 
                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_tau_Out_pow_comp_op_steps_intro[where xs="map (\<lambda> (t, d). Inr (t, d)) (outpu (os 0) 0) @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))" and p="Inr (0, 0)"])
                        apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 0) (Inr x)) (outpu (os 0) 0) @ map (\<lambda> e. case e of Data t d \<Rightarrow> Out (Some 0) (Inr (Inl d, t))) (filter is_Data (ltaken n lxs))"])
                          apply (rule refl)+
                         apply simp
                subgoal
                  by (auto simp add: comp_def split: IO.splits event.splits)
                        apply (rule steps_ooo_input_op_Write_Some[where ys="Nil" and xs="outpu (os 0) 0 @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))" and p=0])
                           apply simp
                          apply (simp add: obtain_progress_def operator_state.defs os_inv(1))
                         apply (rule refl)+
                        apply simp
                subgoal
                  by (auto simp add: comp_def split: IO.splits event.splits)
                       apply simp
                      apply fastforce
                     apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule relpowp_imp_rtranclp[where n="(length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n lxs)))"]) 
                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply simp
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_tau_Inp_pow_comp_op_steps_intro
                    [where n="(length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n lxs)))" and p="Inr (1, 0)" and xs="map Inr (cbufs (1, 0)) @ map Inr (outpu (os 0) 0) @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))"])
                          apply (rule steps_Inp_loop_op_intro[where p="Inr (1, 0)" and xs="map Inr (cbufs (1, 0)) @ map Inr (outpu (os 0) 0) @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))"])
                             apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (cbufs (1, 0)) @ map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (outpu (os 0) 0)  @ map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (filter is_Data (ltaken n lxs))"])
                               apply (rule refl)+
                              apply fastforce
                             apply (rule steps_comp_op_L_Inp[where xs="map Inr (cbufs (1, 0)) @ map Inr (outpu (os 0) 0) @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))"and p="Inr (1, 0)"])
                                apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 0) (Inr x)) (cbufs (1, 0)) @ map (\<lambda> x. Inp (Some 0) (Inr x)) (outpu (os 0) 0) @ map (\<lambda> x. Inp (Some 0) (Inr x)) (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs)))" ])
                                  apply (rule refl)+
                subgoal
                  by (auto simp add: comp_def split: IO.splits event.splits)
                                apply (rule steps_label_propagation_op_Read_Some[where p=0 and xs="cbufs (1, 0) @ outpu (os 0) 0 @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))"])
                                 apply (rule refl)+
                                apply simp
                               apply (rule refl)+
                             apply simp
                subgoal
                  by (auto simp add: comp_def ran_def split: sum.splits IO.splits event.splits)                
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

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule relpowp_imp_rtranclp[where n="(length (input (os 1) 0)) + length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n lxs))"]) 
                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply simp
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_taus_R_pow_comp_op_steps_intro)
                      apply (rule step_taus_loop_op_steps_intro)
                       apply (rule step_tau_pow_map_op)
                       apply (rule step_taus_L_pow_comp_op_steps_intro)
                        apply (rule step_tau_pow_map_op)
                        apply (rule step_compower_label_propagation_op_input0_eq_alt[where msgs="input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (\<lambda>ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))" and ys="[]"])
                subgoal
                  unfolding input_fold_consumes 
                  by (simp add: os_inv(4) operator_state.defs)
                          apply simp
                         apply (simp add: os_inv(3,4) operator_state.defs)
                        apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule step_Taus_set_op)
                     apply (rule step_Taus_dataflow_op_Taus_intro)
                     apply (rule step_star_map_op)
                     apply (rule step_comp_op_R_Tau_start)
                     apply (rule step_tau_pow_loop_updates_alt)
                           apply simp
                subgoal
                  using os_inv(7)[unfolded raw_summary_def, rule_format, of 2,  simplified] 
                  using num2_neq(1) by force
                using os_inv(9) apply simp
                using os_inv(8) apply simp
                subgoal
                  apply (simp only: CONSUMES_CONSUMES)
                  apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI)
                   apply (simp add: operator_state.defs os_inv(4) input_CONSUMES)
                  apply (simp add:  label_prop_inv(5) input_CONSUMES)
                  done
                subgoal
                  apply safe
                  subgoal for t
                    apply (rule labels_inv_fst_label_prop_input0_batched_inputI)
                      apply (simp add: operator_state.defs os_inv(4) input_CONSUMES)
                    subgoal for q
                      using label_prop_inv(1) by auto
                    subgoal
                      apply (simp only: CONSUMES_CONSUMES)
                      using label_prop_inv(5) apply simp
                      done
                    done
                  done
                subgoal
                  apply (simp only: CONSUMES_CONSUMES)
                  apply (clarsimp del: disjCI simp add: input_CONSUMES split_beta image_iff simp del: fold_append)
                  sorry 
                    apply (rule refl)

                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=0])
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Out)
                          apply (rule step_map_op)
                           apply (rule step_ooo_input_op_Write_None_alt)
                            apply (rule refl)+
                          apply simp
                         apply force
                        apply (rule refl)+
                      apply simp
                     apply fastforce
                    apply (rule refl)+


                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=1])
                      apply (rule step_map_op)
                       apply (rule step_comp_op_R_Out)
                         apply (rule step_Out_loop_op)
                           apply (rule step_map_op)
                            apply (rule step_comp_op_L_Out)
                               apply (rule step_map_op)
                                apply (rule step_label_propagation_op_Write_None_alt)
                                 apply (rule refl)+
                               apply simp
                              apply force
                             apply (rule refl)+
                           apply simp
                          apply force
                         apply (rule refl)+
                      apply simp
                     apply simp
                    apply (rule refl)+

                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=2])
                      apply (rule step_map_op)
                       apply (rule step_comp_op_R_Out)
                         apply (rule step_Out_loop_op)
                           apply (rule step_map_op)
                            apply (rule step_comp_op_R_Out)
                              apply (rule step_map_op)
                               apply (rule step_increment_op_Write_None_alt)
                                apply (rule refl)+
                              apply simp
                             apply (rule refl)+
                           apply simp
                          apply force
                         apply (rule refl)+
                      apply simp
                     apply simp
                    apply (rule refl)+
                   apply (simp add: flip: fold_append change_multiplicities_append_alt)
                sorry
              done
            done
          done
        done
      done
  qed
qed

end
