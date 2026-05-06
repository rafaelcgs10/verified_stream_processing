theory Label_Propagation_op_Correctness

imports
  Label_Propagation_op
  Ooo_Input_op
  Increment_op
  Set_op
  "../Correctness/General"
begin

no_notation shiftr (infixl \<open>>>\<close> 55)
no_syntax (ASCII) "_thenM" :: \<open>['a, 'b] \<Rightarrow> 'c\<close>  (infixl \<open>>>\<close> 54)

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
   initia = True,
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
   initia = False
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

definition \<open>raw_summary = (\<lambda>l1 l2.
   if l1 = Loc (0 :: 3) (Trg (0 :: 2)) \<and> l2 = Loc (0 :: 3) (Src (0 :: 2))
   then [0]
   else if l1 = Loc 0 (Src 0) \<and> l2 = Loc 1 (Trg 0)
   then [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 1)
   then [0]
   else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 0)
   then [0]
   else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 1)
   then [0]
   else if l1 = Loc 1 (Src 1) \<and> l2 = Loc 2 (Trg 0)
   then [0]
   else if l1 = Loc 2 (Trg 0) \<and> l2 = Loc 2 (Src 0)
   then [MyPair (0 :: nat) (1 :: nat)]
   else if l1 = Loc 2 (Src 0) \<and> l2 = Loc 1 (Trg 1)
   then [0]
   else [])\<close>

abbreviation \<open>test_sg \<equiv> init_subgraph (antichain_from_list \<circ>\<circ> raw_summary) [(Loc 0 (Src 0), \<bottom>, 1)]\<close>
abbreviation \<open>test_op \<equiv> dataflow_op test_sg cc_op\<close>

(* Why don't I get traces when I set initia to True for the increment operator? *)
value [GHC] \<open>trace_exec test_op\<close>

definition collection_le where
  \<open>collection_le lxs t = list_of (lmap (\<lambda>e. case e of Data _ d \<Rightarrow> d)
  (lfilter (\<lambda>e. case e of Data t' _ \<Rightarrow> t' \<le> t | _ \<Rightarrow> False) lxs))\<close>

lemma collection_le_LNil[simp]:
  \<open>collection_le LNil t = []\<close>
  unfolding collection_le_def by simp

lemma collection_le_LCons_Data:
  assumes \<open>lfinite (lfilter (\<lambda>e. time e \<le> t) lxs)\<close>
  shows \<open>collection_le (LCons (Data t' d) lxs) t =
  (if t' \<le> t then d # collection_le lxs t else collection_le lxs t)\<close>
proof (cases \<open>t' \<le> t\<close>)
  case True
  have \<open>lfilter (\<lambda>e. case e of Data t' _ \<Rightarrow> t' \<le> t | _ \<Rightarrow> False) lxs
  = lfilter is_Data (lfilter (\<lambda>e. time e \<le> t) lxs)\<close>
    using event.case_eq_if lfilter_cong lfilter_lfilter by (smt (verit, best))
  thus ?thesis unfolding collection_le_def using assms by simp
next
  case False
  thus ?thesis unfolding collection_le_def by simp
qed

lemma collection_le_LCons_Drop[simp]:
  \<open>collection_le (LCons (Drop t') lxs) t = collection_le lxs t\<close>
  unfolding collection_le_def by simp

lemma collection_le_LCons_Mint[simp]:
  \<open>collection_le (LCons (Mint t') lxs) t = collection_le lxs t\<close>
  unfolding collection_le_def by simp

lemma collection_le_append:
  \<open>collection_le (llist_of (xs @ ys)) t
  = collection_le (llist_of xs) t @ collection_le (llist_of ys) t\<close>
  unfolding collection_le_def by simp

lemma collection_le_lshift:
  \<open>lfinite (lfilter (\<lambda>e. time e \<le> t) lxs) \<Longrightarrow>
  collection_le (xs @@- lxs) t = collection_le (llist_of xs) t @ collection_le lxs t\<close>
proof (induction xs arbitrary: lxs rule: rev_induct)
  case (snoc x xs)
  thus ?case by (cases x) (auto simp add: collection_le_append collection_le_LCons_Data)
qed simp

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
      es = (\<lambda>_. LNil)(0 := lxs)\<rparr>\<close>
    \<open>input (os 0) = (\<lambda>_. [])\<close> \<open>initia (os 0)\<close>
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    \<open>ty1_check os_input (curry cbufs 0)\<close> \<open>ty2_check os_label_prop (curry cbufs 1)\<close>
    \<open>input_ocaps_inv (os 1)\<close>
    \<open>\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    \<open>\<not> upfro sg 1 \<longrightarrow> (initia (os 1)
      \<and> (\<forall>p. front (os 1) p = ifrontier (summ sg) (-+-) (pt_tr sg) (Loc 1 (Trg p))))\<close>
    and buffers_inv: \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    and dataplane_inv: \<open>dataplane_tracker_inv os cbufs sg\<close> (*\<open>cbufs (0, 0) = []\<close>*)
    and csets_inv:
    \<open>SP = cimage
      (\<lambda>t. ((1, 0), (Inr (ccs
        (set (collection_le (map (\<lambda>(x, t'). Data t' (projl x)) (chns (1, 0)) @@- lxs) t)
        \<union> all_edges os_label_prop (myfst t))), t)))
      (cUn (ts lxs) (cset_from_list (map snd (chns (1, 0)))))\<close>
    \<open>SO = cset_from_list (map (\<lambda>x. ((1, 0), x)) (outpu (os 1) 0))\<close>
    and input_stream_inv: \<open>timely_input_stream lxs (mset (ocaps (os 0) 0))\<close>
  shows \<open>set_op S D (dataflow_op sg
  (comp_map (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] (\<lambda>x. case x of Inl _ \<Rightarrow> [] | Inr l \<Rightarrow> map (\<lambda>(d, t). Inr (d, t)) (cbufs l))
    (logic_map (0 :: 3) (ooo_input_op {|0 :: 2|} os_input))
    (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] (\<lambda>x. case x of Inl _ \<Rightarrow> [] | Inr l \<Rightarrow> map (\<lambda>(d, t). Inr (d, t)) (cbufs l))
      (comp_map (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] (\<lambda>x. case x of Inl _ \<Rightarrow> [] | Inr l \<Rightarrow> map (\<lambda>(d, t). Inr (d, t)) (cbufs l))
        (logic_map (1 :: 3) (label_propagation_op os_label_prop))
        (logic_map (2 :: 3) (increment_op (0 :: 2) 0 (MyPair 0 1) (os 2)))))))))
  \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms
proof (coinduction arbitrary: lxs os os_input os_label_prop cbufs chns sg T G V L S SO SP D
    rule: weakBisimWeakUptoBisimCong)
  case SIM1
  show ?case (is \<open>wsim ((~) OO \<U> ?R OO (\<approx>)) _ _\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    show ?thesis
      unfolding R_def[symmetric]
      unfolding wsim_def ooo_input_op_def label_propagation_op_def increment_op_def
      apply (intro allI impI)
      apply (elim step_dataflow_op_elim step_set_op_elim step_map_op_elim step_comp_op_elim
          step_loop_op_elim step_builder_op_elim conjE)
      apply (simp_all only: IO.simps)
(* ; simp only: IO.simps; hypsubst_thin?; clarsimp simp flip: cin.rep_eq split: option.splits; hypsubst_thin?) *)
      sorry
  qed
next
  case SIM2
  then show ?case sorry
  oops

end