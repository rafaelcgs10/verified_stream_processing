theory Batch_Op_Correctness_Mset

imports
  Batch_Op
  Dataplane_Core.Consumes
  Dataplane_Core.Progress
  Dataplane_Core.Produces
  Dataplane_Core.Outputs
  Dataplane_Core.Timely_Collections
  Dataplane_Core.OCapsReorder
  Dataplane_Core.Init
  Dataplane_Core.Mset_Op
  "../../Lib/SimulationProofMethods"
  "HOL-ex.Sketch_and_Explore"
begin
no_notation shiftr (infixl \<open>>>\<close> 55)

declare if_cong[cong]
declare filter_True[simp del] filter_False[simp del] list_emb_Nil2[simp del]
  BULK_BENQ_right_empty[simp del] BULK_BENQ_left_empty[simp del] in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

section \<open>Generalized Correctness\<close>

definition \<open>raw_summary = (\<lambda>l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
    then [0 :: _ :: {canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le, ccompare, bot}]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
    then [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
    then [0]
   else [])\<close>

subsection \<open>Topology Facts\<close>

text \<open>Simp rules about the concrete two-node summary topology.\<close>

lemma antichain_from_list_pair_set_singleton[simp]:
  "{(nid' :: 2, p' :: 1). antichain_from_list (if nid' = 0 then [0] else []) \<noteq> {}\<^sub>A} = {(0, 0)}"
  apply (auto 10 10 simp add: if_distrib antichain_from_list_singleton)
  apply presburger
  done


lemma weights_to_graph_fun_to_next[simp]:
  "weights_to_graph_fun
          (\<lambda>l1 l2.
              if 0 \<in>\<^sub>A antichain_from_list
                         (if 0 \<le> node l1 \<and> node l1 < 1 \<and> 0 \<le> node l2 \<and> node l2 < 1 then if node l1 = 0 \<and> node l2 = 0 \<and> Locations.is_Trg (port l1) \<and> is_Src (port l2) then [0] else []
                          else if 1 \<le> node l1 \<and> 1 \<le> node l2 then if node l1 = 1 \<and> node l2 = 1 \<and> Locations.is_Trg (port l1) \<and> is_Src (port l2) then [0] else []
                               else if 0 \<le> node l1 \<and> node l1 < 1 \<and> 1 \<le> node l2 \<and> is_Src (port l1) \<and> Locations.is_Trg (port l2)
                                    then case if node l1 = 0 then Some (0, 1) else None of None \<Rightarrow> [] | Some (offset, q) \<Rightarrow> if node (l2 :: (2, 1) location) = 1 + offset \<and> q = idp (port l2) then [0] else [] else [])
              then antichain_from_list [0] else {}\<^sub>A) = 
   (\<lambda> l. 
     if l = Loc (0 :: 2) (Src (1 :: 1)) then [Loc 1 (Trg 1)] else
     if l = Loc 0 (Trg 0) then [Loc 0 (Src 0)] else
     if l = Loc 1 (Trg 0) then [Loc 1 (Src (0 :: 1))] else 
     [])"
  apply (rule ext)
  unfolding weights_to_graph_fun_def enum_location_def enum_num1_def Enum.enum_prod_def 
  subgoal for l
    using loc_2_1_cases[where l=l] apply -
    apply (elim disjE; hypsubst_thin)
    unfolding enum_location_def enum_port_def Numeral_Type.enum_num1_def comp_def Enum.enum_prod_def
    by (auto; code_simp?)+
  done

lemma bi_unique_op_conn_2_1[simp]:
  "bi_unique
        (op_conn
          (\<lambda>(x :: (2, 1) location) (xa :: (2, 1) location).
              antichain_from_list
               (if 0 \<le> node x \<and> node x < 1 \<and> 0 \<le> node xa \<and> node xa < 1 then if node x = 0 \<and> node xa = 0 \<and> Locations.is_Trg (port x) \<and> is_Src (port xa) then [0] else []
                else if 1 \<le> node x \<and> 1 \<le> node xa then if node x = 1 \<and> node xa = 1 \<and> Locations.is_Trg (port x) \<and> is_Src (port xa) then [0] else []
                     else if 0 \<le> node x \<and> node x < 1 \<and> 1 \<le> node xa \<and> is_Src (port x) \<and> Locations.is_Trg (port xa)
                          then case if node x = 0 then Some (0, 1) else None of None \<Rightarrow> [] | Some (offset, q) \<Rightarrow> if node xa = 1 + offset \<and> q = idp (port xa) then [0] else [] else [])))"
  unfolding bi_unique_def
  apply safe
  subgoal
    apply (simp only: if_distrib[of antichain_from_list] location.simps port.simps op_conn.simps image_iff split_beta split: prod.splits if_splits port.splits; simp?)
    by (auto simp add: if_distrib[of antichain_from_list] split: if_splits)
  subgoal
    by (simp only: if_distrib[of antichain_from_list] location.simps port.simps op_conn.simps image_iff split_beta split: prod.splits if_splits port.splits; simp?)
  subgoal
    by (simp only: if_distrib[of antichain_from_list] location.simps port.simps op_conn.simps image_iff split_beta split: prod.splits if_splits port.splits; simp?)
  subgoal
    by (simp only: if_distrib[of antichain_from_list] location.simps port.simps op_conn.simps image_iff split_beta split: prod.splits if_splits port.splits; simp?)
  done

lemma dataflow_tree_to_graph_to_raw_summary[simp]:
  "dataflow_tree_to_graph (Comp [(0, 1) \<mapsto> (0, 1)] (Logic op1 default_internal_summary) (Logic op2 default_internal_summary)) = raw_summary"
  unfolding dataflow_tree_to_graph_def Let_def default_internal_summary_def comp_def                                               
  apply (simp only: split: if_splits prod.splits)
  apply (intro allI impI conjI)
  subgoal for x su
    apply (rule ext)+
    apply simp
    apply (elim conjE)
    apply hypsubst_thin
    subgoal premises prems for l1 l2
      apply (cases l1; cases l2)
      apply simp
      subgoal for nid1 p1 nid2 p2
        apply (cases p1; cases p2; simp)
           apply (auto simp add: raw_summary_def split: if_splits)
          apply code_simp+
        done
      done
    done
  subgoal for x su
    apply simp
    apply (rule FalseE)
    apply (safe; hypsubst_thin?)
    subgoal
      apply (subst (asm) weights_to_graph_fun_to_next)
      apply simp
      apply code_simp
      apply eval
      done
    subgoal for l1 l2
      apply (cases l1; cases l2)
      apply simp
      subgoal for nid1 lp1 nid2 lp2
        by (cases lp1; cases lp2; simp add: incomparable_def if_distrib split: if_splits)
      done
    subgoal for nid
      by (clarsimp simp add: image_iff split_beta split: prod.splits if_splits port.splits)
    subgoal 
      by simp
    done
  done 

(* The same equation keyed on the notation wire, which also occurs in goals. *)
lemma dataflow_tree_to_graph_to_raw_summary_tscomp[simp]:
  "dataflow_tree_to_graph (Logic op1 default_internal_summary \<sqdot>\<^bsub>1\<^esub> Logic op2 default_internal_summary) = (raw_summary :: (2, 1) location \<Rightarrow> (2, 1) location \<Rightarrow> _ list)"
  unfolding tscomp_op_wire_eq by (rule dataflow_tree_to_graph_to_raw_summary)

lemma outputs_at_target_raw_summary[simp]:
  "outputs_at_target (antichain_from_list oo raw_summary) os = (\<lambda> p. if p = (1, 0) then outpu (os 0) 0 else [])"
  unfolding outputs_at_target_def raw_summary_def
  apply (rule ext)
  apply (auto simp add: antichain_from_list_singleton split: prod.splits if_splits)
  done

lemma dataflow_topology_raw_summary:
  \<open>dataflow_topology (antichain_from_list \<circ>\<circ> raw_summary) (-+-)\<close>
  using dataflow_topology_from_tree.dataflow_topology_axioms dataflow_tree_to_graph_to_raw_summary
  by metis

subsection \<open>Output Batches\<close>

text \<open>Collecting the outputs a batch function produces at a timestamp.\<close>

definition "output_batches f F batches = (let ts = outputs_ts F (map snd batches) in
                                          concat (map (\<lambda> t. map (\<lambda> d. (d, t)) (f (map fst (filter (\<lambda> (d, t'). t' = t) batches)))) ts))" 

lemma output_batchesI:
  "t \<in> snd ` set batches \<Longrightarrow>
   \<not> frontier_less_equal F t \<Longrightarrow>
   d \<in> set (f (map fst (filter (\<lambda> (d, t'). t' = t) batches))) \<Longrightarrow>
   (d, t) \<in> set (output_batches f F batches)"
  unfolding output_batches_def Let_def outputs_ts_def
  apply auto
  done

subsection \<open>The Generalized Correctness Lemma\<close>

text \<open>One large induction establishing correctness for the wired batch
  dataflow.\<close>

lemma dataplane_tracker_inv_clean2:
  "sg = sg' \<Longrightarrow>
   (\<forall> nid. intsum (os nid) = intsum (os' nid) \<and> ocaps (os nid) = ocaps (os' nid) \<and> 
   consu (os nid) = consu (os' nid) \<and> inter (os nid) = inter (os' nid) \<and>
   produ (os nid) = produ (os' nid) \<and> input (os nid) = input (os' nid) \<and>
   outpu (os nid) = outpu (os' nid) \<and> front (os nid) = front (os' nid)) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg'"
  apply hypsubst
  apply (rule dataplane_tracker_inv_clean)
  apply assumption
  done

abbreviation \<open>(comp_wire :: 2 + 2 \<times> 1 \<Rightarrow> (2 + 2 \<times> 1) option) \<equiv>
  case_sum (\<lambda>_. None) (\<lambda>(nid, p). case if nid = 0 then Some (0, 1) else None of
    None \<Rightarrow> None
  | Some (offset, q) \<Rightarrow> Some (Inr (1 + offset, q)))\<close>

lemma ran_comp_wire:
  \<open>ran comp_wire = {Inr (1, 1)}\<close>
proof -
  have \<open>comp_wire (Inr (0, 1)) = Some (Inr (1, 1))\<close> by simp
  moreover have \<open>comp_wire x = None\<close> if \<open>x \<noteq> Inr (0, 1)\<close> for x using that by (simp split: sum.splits)
  ultimately show ?thesis unfolding ran_def using Collect_cong Set.empty_def insert_Collect
      option.simps(1,2) by (smt (verit, del_insts))
qed

lemma batch_op_1_alt:
  \<open>batch_op [1 :: 1] f id os = builder_op True {|1|} {|1|} os
    (\<lambda>os. batch_op_logic [1] f id os
      (\<lambda>p. filter (\<lambda>t. \<not>frontier_less_equal (front os 1) t) (ocaps os 1)))\<close>
  unfolding batch_op_def notifier_op_def by simp

definition batch_op_batches where
  \<open>batch_op_batches f os caps p t =
  f (map (de1 os \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (caps p)) (input os p)))\<close>

definition batch_op_ts where
  \<open>batch_op_ts os caps p = remdups (map snd (filter (\<lambda>(d, t). t \<in> set (caps p)) (input os p)))\<close>

definition batch_op_outputs where
  \<open>batch_op_outputs ps batches batches_ts =
  concat (map (\<lambda>p. concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t p)) (batches p t)) (batches_ts p))) ps)\<close>

definition batch_op_drops where
  \<open>batch_op_drops ps caps = concat (map (\<lambda>p. map (\<lambda>t. Cap t p) (caps p)) ps)\<close>

lemma batch_op_logic_alt:
  \<open>batch_op_logic ps f g os caps =
  (let caps' = g caps in if \<exists>p. p \<in> set ps \<and> caps' p \<noteq> [] then
    let os' = os\<lparr>input := (\<lambda>p. filter (\<lambda>(d, t). t \<notin> set (caps' p)) (input os p))\<rparr>;
        outs = batch_op_outputs ps (batch_op_batches f os caps') (batch_op_ts os caps');
        drops = batch_op_drops ps caps'
    in {|trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops))
      (drop_caps (produces os' (map (\<lambda>(d, cap). (en2 os' d, cap)) outs)) drops)|}
  else trace (STR ''No capabilities'') {||})\<close>
  unfolding batch_op_logic_def batch_op_batches_def batch_op_ts_def batch_op_outputs_def
    batch_op_drops_def by metis

(* TODO: Move. *)
lemma frontier_less_equal_bots[simp]:
  \<open>frontier_less_equal (antichain (set bots)) t\<close>
  using frontier_less_equal_iff2 set_bots_bot_antichain by blast

(* TODO: Move. *)
lemma filter_const:
  \<open>filter (\<lambda>x. P) xs = (if P then xs else [])\<close>
  by (cases P; simp add: filter_True filter_False)

(* TODO: Move. *)
lemma dataplane_tracker_inv_produces_drops':
  assumes \<open>os' = os(nid := os nid\<lparr>outpu := noutput, ocaps := nocaps, input := ninput, produ := nprodu, inter := ninter\<rparr>)\<close>
    \<open>dataflow_topology (summ sg) (-+-)\<close>
    \<open>noutput = (\<lambda>p. outpu (os nid) p @ oputs p)\<close>
    \<open>nocaps = (\<lambda>p. list_diff (ocaps (os nid) p) (drops p))\<close>
    \<open>ninput = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drops p)) (input (os nid) p))\<close>
    \<open>nprodu = produ (os nid) @ produs\<close>
    \<open>ninter = operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum)\<close>
    \<open>\<forall>p. mset (drops p) \<subseteq># mset (ocaps (os nid) p)\<close>
    \<open>\<forall>(p, t, m) \<in> set produs. 0 < m \<and> t \<in> set (ocaps (os nid) p)\<close>
    \<open>\<forall>p. snd ` set (oputs p) \<subseteq> set (ocaps (os nid) p)\<close>
    \<open>\<forall>p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))\<close>
    \<open>graph_summar_nt (summ sg) (nxt sg) os\<close>
    \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    \<open>dataplane_tracker_inv os cbufs sg\<close>
  shows \<open>dataplane_tracker_inv os' cbufs sg\<close>
  unfolding assms(1) using dataplane_tracker_inv_produces_drops[OF assms(2-)] .

(* TODO: Move. *)
lemma cfilter_cfilter':
  \<open>cfilter P (cfilter Q X) = cfilter (\<lambda>x. P x \<and> Q x) X\<close>
  by force

(* TODO: Move. *)
lemma sum_eq_single: 
  assumes \<open>finite A\<close> \<open>a \<in> A\<close> \<open>f a = x\<close> \<open>\<And>a'. a' \<in> A \<Longrightarrow> a' \<noteq> a \<Longrightarrow> f a' = 0\<close>
  shows \<open>sum f A = x\<close>
proof -
  have \<open>sum f A = sum f {a}\<close> by (rule sum.mono_neutral_cong) (use assms in auto)
  then show ?thesis by (simp add: \<open>f a = x\<close>)
qed

lemma correctness_gen:
  fixes lxs :: \<open>('t :: {canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le, order_ccompare, bot}, 'd1) event llist\<close>
    and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
    and os_input :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
    and os_batch :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
    and os :: \<open>2 \<Rightarrow> (1, 'd1 + 'd2, 't) operator_state\<close>
    and chns :: \<open>2 \<times> 1 \<Rightarrow> (('d1 + 'd2) \<times> 't) list\<close>
    and sg :: \<open>(2, 1, 't) subgraph\<close>
  assumes
    \<open>summ sg = antichain_from_list oo raw_summary\<close>
    \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    \<open>os_input = operator_state.extend (os 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, es = (\<lambda>_. lxs)\<rparr>\<close>
    \<open>os_batch = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr\<rparr>\<close>
    \<open>ty1_check os_input (curry cbufs 0)\<close>
    \<open>ty2_check os_batch (curry cbufs 1)\<close>
    \<open>\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    \<open>input (os 0) = (\<lambda>_. [])\<close>
    \<open>initia (os 0)\<close>
    \<open>input_ocaps_inv (os 1)\<close>
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    \<open>cbufs (0, 0) = []\<close>
    \<open>dataplane_tracker_inv os cbufs sg\<close>
    \<open>SP = cmUnion (cmset_of_cset ((\<lambda>t. cmset_of_list (map (\<lambda>d. ((1, 1), (Inr d, t)))
      (f (coll ((map (\<lambda>(d, t'). Data t' (projl d)) (chns (1, 1))) @@- lxs) t))))
  |`| cUn (ts lxs) (snd |`| cset_from_list (chns (1, 1)))))\<close>
    \<open>SO = cmset_of_list (map (Pair (1, 1)) (outpu (os 1) 1))\<close>
    \<open>\<forall>t. in_cmset t (cmimage (snd \<circ> snd) (S + SO)) \<longrightarrow> \<not>frontier_less_equal (front (os 1) 1) t\<close>
    \<open>\<forall>t. in_cmset t (cmimage (snd \<circ> snd) (S + SO + SP)) \<longrightarrow>
  (\<exists>xs. cmimage (projr \<circ> fst \<circ> snd) (cmfilter (\<lambda>(_, (_, t')). t' = t) (S + SO + SP))
  = cmset_of_list (f xs))\<close>
    \<open>timely_input_stream lxs (mset (ocaps (os 0) 1))\<close>
  shows 
    \<open>mset_op S D (dataflow_op sg (G_op f os_input os_batch cbufs)) \<approx> mset_spec_op (S + SO + SP) D\<close>
  using assms unfolding tscomp_op_wire_eq
proof (coinduction arbitrary: os sg os_input os_batch chns cbufs lxs SP SO S D rule: weakBisimWeakUptoBisimCong)
  case SIM1
  note subgraph_inv = SIM1(1,2)
  note os_inv = SIM1(3-10)
  note bufs_inv = SIM1(11,12)
  note dataplane_inv = SIM1(13)
  note sets_inv = SIM1(14-17)
  note input_stream_inv = SIM1(18)
  show ?case (is \<open>wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    have "\<exists>op2'. step (Out (p, 1) (d, t)) (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S (cminsert ((p, 1), d, t) D) (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} os_input)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id os_batch)))))) op2'"
      if "in_cmset ((p, 1), d, t) (S - D)"
      for p :: 2
        and d :: "'d1 + 'd2"
        and t :: 't
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (BENQ (1, 1) (Inr (d, t)) (map Inr \<circ> cbufs))) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} (os_input \<lparr>outpu := (outpu os_input)(1 := xs)\<rparr>))) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id os_batch)))))) op2'"
      if "outpu os_input 1 = (d, t) # xs"
      for d :: "'d1 + 'd2"
        and t :: 't
        and xs :: "(('d1 + 'd2) \<times> 't) buf"
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (BTL (1, 1) (map Inr \<circ> cbufs))) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} os_input)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (consumes os_batch 1 t d))))))) op2'"
      if "cbufs (1, 1) \<noteq> []"
        and "(d, t) = BHD (1, 1) cbufs"
      for d :: "'d1 + 'd2"
        and t :: 't
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} (ip_state'\<lparr>front := front os_input, initia := True\<rparr>))) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id os_batch)))))) op2'"
      if "initia os_input"
        and "ip_state' |\<in>| ooo_input_op_logic {|1|} os_input"
      for ip_state' :: "(1, 'd1 + 'd2, 'd1, 't) input_state"
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} os_input)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (os_batch'\<lparr>front := front os_batch, initia := True\<rparr>))))))) op2'" (is \<open>\<exists>_. _ \<and> ((~) OO \<U> R OO (\<approx>)) ?op1' _\<close>)
      if "initia os_batch"
        and "os_batch' |\<in>| batch_op_logic [1] f id os_batch (\<lambda>_. filter (\<lambda>t. \<not>frontier_less_equal (front os_batch 1) t) (ocaps os_batch 1))"
    for os_batch' :: "(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2"
    proof -
      have dataflow_topo_sg: \<open>dataflow_topology (summ sg) (-+-)\<close>
        using dataflow_topology_raw_summary subgraph_inv(1) by simp
      have graph_summar_sg: \<open>graph_summar_nt (summ sg) (nxt sg) os\<close>
        using graph_summar_nt[OF _ _ _ subgraph_inv(2)] subgraph_inv(1) os_inv(5)
          dataflow_tree_to_graph_to_raw_summary by metis
      define caps where \<open>caps = (\<lambda>_ :: 1. filter (\<lambda>t. \<not>frontier_less_equal (front os_batch 1) t) (ocaps os_batch 1))\<close>
      define os_batch'' where \<open>os_batch'' = os_batch\<lparr>input := (\<lambda>_. filter (\<lambda>(_, t). t \<notin> set (caps 1)) (input os_batch 1))\<rparr>\<close>
      define outs where \<open>outs = batch_op_outputs [1] (batch_op_batches f os_batch caps) (batch_op_ts os_batch caps)\<close>
      have outs_not_frontier_less_equal: \<open>\<forall>t \<in> time ` snd ` set outs. \<not>frontier_less_equal (front (os 1) 1) t\<close>
        by (simp add: outs_def caps_def batch_op_outputs_def batch_op_ts_def os_inv(2,8) operator_state.defs)
      define drops where \<open>drops = batch_op_drops [1] caps\<close>
      have os_batch': \<open>os_batch' = drop_caps (produces os_batch'' (map (\<lambda>(d, cap). (en2 os_batch'' d, cap)) outs)) drops\<close>
        using that(2) by (simp add: batch_op_logic_alt caps_def os_batch''_def outs_def drops_def split: if_splits)
      define os' where \<open>os' = os(1 := operator_state.truncate os_batch')\<close>
      define chns' where \<open>chns' = outputs_at_target (summ sg) os' >> cbufs >> inputs_at_target os'\<close>
      have chns_1_1: \<open>chns (1, 1) = input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1\<close>
        by (simp add: subgraph_inv(1,2) bufs_inv(1) BULK_BENQ_def inputs_at_target_def)
      have chns'_1_1: \<open>chns' (1, 1) = input (os' 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1\<close>
        by (simp add: subgraph_inv(1,2) chns'_def BULK_BENQ_def inputs_at_target_def os'_def)
      define g where \<open>g = (\<lambda>t. cmset_of_list (map (\<lambda>d. ((1 :: 2, 1 :: 1), Inr d :: 'd1 + 'd2, t))
  (f (coll (map (\<lambda>(d, t'). Data t' (projl d)) (chns (1, 1)) @@- lxs) t))))\<close>
      define h where \<open>h = (\<lambda>t. cmset_of_list (map (\<lambda>d. ((1 :: 2, 1 :: 1), Inr d :: 'd1 + 'd2, t))
  (f (coll (map (\<lambda>(d, t'). Data t' (projl d)) (chns' (1, 1)) @@- lxs) t))))\<close>
      define SP' where \<open>SP' = cmUnion (cmset_of_cset (h |`| cUn (ts lxs) (snd |`| cset_from_list (chns' (1, 1)))))\<close>
      define SO' where \<open>SO' = cmset_of_list (map (Pair (1 :: 2, 1 :: 1)) (outpu (os' 1) 1))\<close>
      have SO'_alt: \<open>SO' = SO + cmset_of_list (map (\<lambda>(d, cap). ((1, 1), (Inr d, time cap))) outs)\<close>
        by (simp add: SO'_def sets_inv(2) os'_def os_inv(2) os_batch' os_batch''_def
            operator_state.defs filter_True comp_def split_beta' cmset_of_list_append)
      define P where \<open>P = (\<lambda>t. frontier_less_equal (front (os 1) 1) t \<or> t \<notin> set (ocaps (os 1) 1))\<close>
      have g_h_cong: \<open>g t = h t\<close> if \<open>P t\<close> for t
      proof -
        have \<open>coll (llist_of (map (\<lambda>(d, t'). Data t' (projl d)) (chns (1, 1)))) t
  = coll (llist_of (map (\<lambda>(d, t'). Data t' (projl d)) (chns' (1, 1)))) t\<close>
          by (simp add: chns_1_1 chns'_1_1 os_inv(2) os'_def os_batch' os_batch''_def
              operator_state.defs caps_def) (metis (mono_tags, lifting) that P_def prod.case_eq_if)
        then show ?thesis unfolding g_def h_def
          using coll_lshift[OF timely_input_stream_expires[OF input_stream_inv]] by force
      qed
      have SP_alt: \<open>SP = SP' + cmset_of_list (map (\<lambda>(d, cap). ((1, 1), (Inr d, time cap))) outs)\<close>
      proof (rule cmset_eqI)
        fix x :: \<open>(2 \<times> 1) \<times> ('d1 + 'd2) \<times> 't\<close>
        obtain nid p d t where x: \<open>x = ((nid, p), (d, t))\<close> using prod.exhaust by metis
        show \<open>cmcount SP x = cmcount (SP' + cmset_of_list (map (\<lambda>(d, cap). ((1, 1), (Inr d, time cap))) outs)) x\<close>
        proof (cases \<open>nid = 1\<close>)
          case True
          show ?thesis
          proof (cases \<open>t |\<in>| cUn (ts lxs) (snd |`| cset_from_list (chns (1, 1)))\<close>)
            case t_cin: True
            let ?ts = \<open>cUn (ts lxs) (snd |`| cset_from_list (chns (1, 1)))\<close>
            have Ball_P: \<open>\<forall>t \<in> rcset (ts lxs) \<union> snd ` set ((outputs_at_target (summ sg) os >> cbufs) (1, 1)). P t\<close> unfolding P_def
            proof (intro ballI disjI1, erule UnE)
              fix t'
              assume \<open>t' \<in> rcset (ts lxs)\<close>
              have \<open>front (os 1) 1 \<le> ifrontier (summ sg) (-+-) (pt_tr sg) (Loc 1 (Trg 1))\<close>
                using order.trans dataplane_inv unfolding dataplane_tracker_inv_def front_inv_def
                  imp_front_inv_def  by blast
              moreover have \<open>frontier_less_equal \<dots> t'\<close>
              proof -
                have \<open>frontier_less_equal (frontier (to_zmset (ocaps (os 0) 1))) t'\<close>
                  using \<open>t' \<in> rcset (ts lxs)\<close> cin.rep_eq ts_lsetE
                    timely_input_stream_frontier_less_equal[OF input_stream_inv] by auto
                moreover have \<open>to_zmset (ocaps (os 0) 1) = c_pts (change_multiplicities (summ sg)
    (extract_progress 0 (nxt sg) (snd (obtain_progress (os 0)))
      @ extract_progress 1 (nxt sg) (snd (obtain_progress (os 1)))) (pt_tr sg))
  (Loc 0 (Src 1))\<close> using dataplane_inv unfolding dataplane_tracker_inv_def Src_caps_inv_def
                  c_pts_inv_def by force
                ultimately have \<open>frontier_less_equal (frontier (c_pts (change_multiplicities (summ sg)
  (extract_progress 0 (nxt sg) (snd (obtain_progress (os 0)))) (pt_tr sg)) (Loc 0 (Src 1)))) t'\<close>
                  by (simp add: c_pts_change_multiplicities subgraph_inv(1,2) zmset_filter_extract_progress_Src_consumes_diff)
                moreover have \<open>0 \<in>\<^sub>A graph.path_weight (summ sg) (Loc 0 (Src 1)) (Loc 1 (Trg 1))\<close>
                proof (rule path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF dataflow_topo_sg]])
                  have \<open>nxt sg (0, 1) = Some (1, 1)\<close> by (auto simp add: subgraph_inv graph_to_nxt_def
                        raw_summary_def antichain_from_list_singleton is_empty_antichain_iff
                        split: if_splits intro: find_Some_singleton)
                  then show \<open>0 \<in>\<^sub>A summ sg (Loc 0 (Src 1)) (Loc 1 (Trg 1))\<close> using graph_summar_sg
                    unfolding graph_summar_nt_def by fast
                qed
                ultimately show ?thesis using dataflow_topology_from_tree.results_in_zero
                    frontier_less_equal_ifrontier_from_Src[OF dataflow_topo_sg] dataplane_inv
                  unfolding dataplane_tracker_inv_def by metis
              qed
              ultimately show \<open>frontier_less_equal (front (os 1) 1) t'\<close>
                using frontier_less_equal_le_trans by blast
            next
              fix t'
              assume \<open>t' \<in> snd ` set ((outputs_at_target (summ sg) os >> cbufs) (1, 1))\<close>
              then show \<open>frontier_less_equal (front (os 1) 1) t'\<close> using dataplane_inv
                  frontier_less_equal_le_trans unfolding dataplane_tracker_inv_def front_inv_def
                  imp_front_inv_def chnls_imp_front_inv_def by meson
            qed
            then have cfilter_P: \<open>cfilter P ?ts = cUn (ts lxs) (snd |`| cset_from_list (chns' (1, 1)))\<close>
              by (auto simp add: subgraph_inv(1,2) os_inv(2) bufs_inv(1) chns'_def os'_def os_batch'
                  os_batch''_def operator_state.defs inputs_at_target_def BULK_BENQ_def caps_def P_def)
            define ts_empty_batch where \<open>ts_empty_batch =
  cset_from_list (filter (\<lambda>t. \<not>P t \<and> batch_op_batches f os_batch caps 1 t = []) (map snd (input (os 1) 1)))\<close>
            have cfilter_not_P: \<open>cfilter (Not \<circ> P) ?ts = cUn ts_empty_batch (time \<circ> snd |`| cset_from_list outs)\<close>
            proof -
              have \<open>cfilter (Not \<circ> P) ?ts = cset_from_list (filter (Not \<circ> P) (map snd (input (os 1) 1)))\<close>
                using Ball_P unfolding bufs_inv(1) BULK_BENQ_def inputs_at_target_def by auto
              also have \<open>\<dots> = cUn (cfilter (\<lambda>t. \<not>P t \<and> batch_op_batches f os_batch caps 1 t = [])
    (cset_from_list (filter (Not \<circ> P) (map snd (input (os 1) 1)))))
  (cfilter (\<lambda>t. batch_op_batches f os_batch caps 1 t \<noteq> [])
    (cset_from_list (filter (Not \<circ> P) (map snd (input (os 1) 1)))))\<close>
                by (subst cset_cfilter_split) auto
              also have \<open>\<dots> = cUn ts_empty_batch (time \<circ> snd |`| cset_from_list outs)\<close>
                by (rule arg_cong2[where f=cUn]) (auto simp add: ts_empty_batch_def comp_def
                    cfilter_cfilter' outs_def batch_op_outputs_def image_Union batch_op_ts_def
                    caps_def batch_op_batches_def image_image os_inv(2) operator_state.defs
                    image_constant_conv P_def)
              finally show ?thesis .
            qed
            then have Ball_not_P: \<open>\<forall>t \<in> rcset ts_empty_batch \<union> time ` snd ` set outs. \<not>P t\<close>
              by auto
            have cmcount_SP: \<open>cmcount SP x = cmcount (g t) x\<close>
              apply (simp add: sets_inv(1) flip: g_def)
              apply (subst cmUnion_cmset_of_cset_single[of \<open>g t\<close>])
              using t_cin apply blast
              subgoal for M
                apply (rule ccontr)
                apply (subgoal_tac \<open>in_cmset x M \<and> (\<exists>t'. M = g t')\<close>)
                 apply (elim conjE exE)
                 apply (fastforce simp add: g_def x \<open>nid = 1\<close>)
                using cmset_alt apply fast
                done
              apply (rule refl)
              done
            show ?thesis
            proof (cases \<open>P t\<close>)
              case True
              have \<open>cmcount SP' x = cmcount (h t) x\<close>
                apply (simp add: SP'_def)
                apply (subst cmUnion_cmset_of_cset_single[of \<open>h t\<close>])
                using t_cin \<open>P t\<close> apply (fastforce simp add: bufs_inv(1) chns'_def BULK_BENQ_def subgraph_inv(1,2) os'_def inputs_at_target_def os_batch' os_batch''_def operator_state.defs os_inv(2) caps_def P_def)
                subgoal for M
                  apply (rule ccontr)
                  apply (subgoal_tac \<open>in_cmset x M \<and> (\<exists>t'. M = h t')\<close>)
                   apply (elim conjE exE)
                   apply (fastforce simp add: h_def x \<open>nid = 1\<close>)
                  using cmset_alt apply fast
                  done
                 apply (rule refl)
                done
              moreover have \<open>cmcount (cmset_of_list (map (\<lambda>(d, cap). ((1, 1), (Inr d, time cap))) outs)) x = 0\<close>
                using \<open>P t\<close> Ball_not_P by (auto simp add: zero_enat_def count_list_0_iff x \<open>nid = 1\<close>)
              ultimately show ?thesis unfolding cmcount_plus cmcount_SP g_h_cong[OF \<open>P t\<close>] by fastforce
            next
              case False
              then have coll_t: \<open>coll (map (\<lambda>(d, t'). Data t' (projl d)) (chns (1, 1)) @@- lxs) t
  = map (projl \<circ> fst) (filter (\<lambda>(_, t'). t' = t) (input (os 1) 1))\<close>
                using Ball_P
                apply (simp add: bufs_inv(1) BULK_BENQ_def inputs_at_target_def)
                apply (subst coll_lshift[OF timely_input_stream_expires[OF input_stream_inv]])
                apply simp
                apply (intro conjI)
                  apply (smt (verit, ccfv_threshold) List.empty_filter_conv UnCI case_prodE rev_image_eqI snd_eqD)
                  apply (smt (verit, ccfv_threshold) List.empty_filter_conv UnCI case_prodE rev_image_eqI snd_eqD)
                apply (simp add: coll_def)
                apply (subgoal_tac \<open>lfilter (\<lambda>e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) lxs = LNil\<close>)
                 apply simp
                apply (rule lfilter_False)
                apply (force split: event.splits)
                done
              have \<open>cmcount SP' x = 0\<close> using \<open>\<not>P t\<close> Ball_P
                apply (simp add: SP'_def chns'_def BULK_BENQ_def subgraph_inv(1,2) os'_def inputs_at_target_def os_batch' os_batch''_def operator_state.defs caps_def os_inv(2) x \<open>nid = 1\<close> cmcount_cmUnion isum_eq_0_iff)
                apply (auto simp add: h_def zero_enat_def count_list_0_iff P_def)
                done
              moreover have \<open>cmcount (cmset_of_list (map (\<lambda>(d, cap). ((1, 1), (Inr d, time cap))) outs)) x = cmcount (g t) x\<close>
                apply (simp add: outs_def batch_op_outputs_def batch_op_ts_def batch_op_batches_def os_inv(2) operator_state.defs x \<open>nid = 1\<close> g_def coll_t map_concat comp_def count_list_concat split_beta flip: sum_code)
                apply (subst sum_eq_single[OF _ _ refl, where a=t])
                   apply simp
                using t_cin Ball_P \<open>\<not>P t\<close> apply (simp add: caps_def os_inv(2) operator_state.defs bufs_inv(1) BULK_BENQ_def inputs_at_target_def P_def)
                apply blast
                 apply (force simp add: count_list_0_iff)
                using False
                 apply (simp add: caps_def os_inv(2) operator_state.defs P_def)
                done
              ultimately show ?thesis unfolding cmcount_plus cmcount_SP by simp
            qed
          next
            case t_not_cin: False
            then have \<open>cmcount SP x = 0\<close> by (simp add: sets_inv(1) x cmcount_cmUnion isum_eq_0_iff)
                (auto simp add: zero_enat_def cmcount_cmset_of_cset)
            moreover have \<open>cmcount SP' x = 0\<close> using t_not_cin
              by (simp add: SP'_def h_def chns'_def bufs_inv(1) x cmcount_cmUnion isum_eq_0_iff)
                (auto simp add: zero_enat_def cmcount_cmset_of_cset BULK_BENQ_def subgraph_inv(1,2)
                  os'_def os_inv(2) os_batch' os_batch''_def operator_state.defs
                  inputs_at_target_def)
            ultimately show ?thesis using t_not_cin
              by (auto simp add: x zero_enat_def cmcount_plus count_list_0_iff BULK_BENQ_def
                  bufs_inv(1) inputs_at_target_def os_inv(2) operator_state.defs outs_def
                  batch_op_outputs_def batch_op_ts_def)
          qed
        next
          case False
          then have \<open>nid = 0\<close> using num2_neq(2) by fast
          then have \<open>cmcount SP x = 0\<close> \<open>cmcount SP' x = 0\<close>
            by (simp_all add: sets_inv(1) SP'_def h_def x cmcount_cmUnion isum_eq_0_iff cmset.set_map)
              (auto simp add: zero_enat_def count_list_0_iff)
          then show ?thesis
            by (clarsimp simp add: \<open>nid = 0\<close> x zero_enat_def count_list_0_iff cmcount_plus)
        qed
      qed
      have \<open>SO' + SP' = SO + SP\<close> by (simp add: SO'_alt SP_alt ac_simps)
      have \<open>R ?op1' (mset_spec_op (S + SO + SP) D)\<close>
      proof -
        have "mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} os_input)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (os_batch' \<lparr>front := front os_batch, initia := True\<rparr>)))))) = mset_op S D (dataflow_op sg (dataflow_tree_to_operator cbufs (Comp [(0, 1) \<mapsto> (0, 1)] (input_dt os_input) (batch_dt os_batch' f))))"
          by (simp add: dataflow_tree_to_operator_def os_batch' os_batch''_def that(1) comp_def)
        moreover have "(mset_spec_op (S + SO + SP) D::(2 \<times> 1, 2 \<times> 1, ('d1 + 'd2) \<times> 't) op) = mset_spec_op (S + SO' + SP') D"
          by (simp add: \<open>SO' + SP' = SO + SP\<close> add.assoc)
        moreover have "summ sg = antichain_from_list \<circ>\<circ> raw_summary"
          by (simp add: subgraph_inv(1))
        moreover have "nxt sg = graph_to_nxt (summ sg)"
          by (simp add: subgraph_inv(2))
        moreover have "os_input = operator_state.extend (os' 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, es = (\<lambda>_. lxs)\<rparr>"
          by (simp add: os_inv(1) os'_def)
        moreover have "os_batch' = operator_state.extend (os' 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr\<rparr>"
          by (simp add: os_inv(2) os'_def os_batch' os_batch''_def operator_state.defs)
        moreover have "ty1_check os_input (curry cbufs 0)"
          by (simp add: os_inv(3))
        moreover have "ty2_check os_batch' (curry cbufs 1)" using os_inv(2-4)
          by (force simp add: ty2_check_def os'_def os_batch' os_batch''_def operator_state.defs)
        moreover have "\<forall>n. intsum (os' n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))"
          by (simp add: os_inv(2,5) os'_def os_batch' os_batch''_def operator_state.defs)
        moreover have "input (os' 0) = (\<lambda>_. [])"
          by (simp add: os_inv(6) os'_def)
        moreover have "initia (os' 0)"
          by (simp add: os_inv(7) os'_def)
        moreover have "input_ocaps_inv (os' 1)"
        proof -
          have \<open>filter (\<lambda>t. \<not>frontier_less_equal (front (os 1) 1) t) (ocaps (os 1) 1) \<noteq> []\<close>
            using that(2) by (simp add: os_inv(2) operator_state.defs batch_op_logic_alt split: if_splits)
          then show ?thesis using os_inv(8) by (clarsimp simp add: input_ocaps_inv_def os'_def
                os_inv(2,5) os_batch' os_batch''_def operator_state.defs drop_caps_def drops_def
                batch_op_drops_def) (fastforce simp add: raw_summary_def)
        qed
        moreover have "chns' = outputs_at_target (summ sg) os' >> cbufs >> inputs_at_target os'"
          by (simp add: chns'_def)
        moreover have "cbufs (0, 0) = []"
          by (simp flip: bufs_inv(2))
        moreover have "dataplane_tracker_inv os' cbufs sg"
          by (rule dataplane_tracker_inv_produces_drops'[OF _ dataflow_topo_sg refl refl refl refl refl _ _ _ _ graph_summar_sg subgraph_inv(2) dataplane_inv,
                where nid=1 and oputs=\<open>\<lambda>_ :: 1. map (\<lambda>(d, cap). (Inr d, time cap)) outs\<close>
                  and drops=\<open>\<lambda>_. map time drops\<close> and produs=\<open>map (\<lambda>(_, cap). (1, time cap, 1)) outs\<close>])
              (auto simp add: fun_eq_iff os'_def os_batch' os_batch''_def drop_caps_def produces_def
                operator_state.defs os_inv(2) filter_True comp_def split_beta enum_num1_def
                drops_def batch_op_drops_def image_image caps_def outs_def batch_op_outputs_def
                batch_op_ts_def batch_op_batches_def)
        moreover have "SP' = cmUnion (cmset_of_cset (h |`| cUn (ts lxs) (snd |`| cset_from_list (chns' (1, 1)))))"
          by (simp add: SP'_def)
        moreover have "SO' = cmset_of_list (map (Pair (1, 1)) (outpu (os' 1) 1))"
          by (simp add: SO'_def)
        moreover have "\<forall>t. in_cmset t (cmimage (snd \<circ> snd) (S + SO')) \<longrightarrow> \<not>frontier_less_equal (front (os' 1) 1) t"
          by (simp add: sets_inv(3) SO'_alt os_inv(2) os'_def os_batch' os_batch''_def operator_state.defs cmimage_plus cmset_plus cmimage_cmset_of_list split_beta outs_not_frontier_less_equal image_image)
        moreover have "\<forall>t. in_cmset t (cmimage (snd \<circ> snd) (S + SO' + SP')) \<longrightarrow> (\<exists>xs. cmimage (projr \<circ> fst \<circ> snd) (cmfilter (\<lambda>(_, (_, t')). t' = t) (S + SO' + SP')) = cmset_of_list (f xs))"
          using sets_inv(4) by (simp add: \<open>SO' + SP' = SO + SP\<close> add.assoc)
        moreover have "timely_input_stream lxs (mset (ocaps (os' 0) 1))"
          by (simp add: input_stream_inv os'_def)
        ultimately show ?thesis unfolding R_def h_def by blast
      qed
      then show ?thesis using bisim_refl wbisim_refl wb_upto_b_base by blast
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op (sg\<lparr>pt_tr := change_multiplicities (summ sg) (extract_progress 1 (nxt sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} os_input)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id os_batch')))))) op2'"
      if "(os_batch', st) = obtain_progress os_batch"
      for st :: "(1, 't) shared_state"
        and os_batch' :: "(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2"
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op (sg\<lparr>pt_tr := change_multiplicities (summ sg) (extract_progress 0 (nxt sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state')) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id os_batch)))))) op2'"
      if "(ip_state', st) = obtain_progress os_input"
      for st :: "(1, 't) shared_state"
        and ip_state' :: "(1, 'd1 + 'd2, 'd1, 't) input_state"
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr>pt_tr := conf'\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} os_input)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (os_batch \<lparr>front := frontier \<circ> (\<lambda>p. c_imp (pt_tr (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr>pt_tr := conf'\<rparr>)) (Loc 1 (Trg 1))), initia := True\<rparr>))))))) op2'"
      sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op (cminsert ((1, 1), d, t) S) D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} os_input)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (os_batch \<lparr>outpu := (outpu os_batch)(1 := xs)\<rparr>))))))) op2'"
      if "outpu os_batch 1 = (d, t) # xs"
      for d :: "'d1 + 'd2"
        and t :: 't
        and xs :: "(('d1 + 'd2) \<times> 't) buf"
      using that sorry
    note * = calculation this
    show ?thesis unfolding R_def[symmetric] wsim_def by (intro allI impI,
          sim_cases intros: *[unfolded comp_def]
          defs: dataflow_tree_to_operator_def batch_op_1_alt ooo_input_op_def
          elims: step_mset_op_elim step_dataflow_op_elim step_map_op_elim
          step_comp_op_elim step_builder_op_elim
          simps: ran_comp_wire comp_def)
  qed
next
  case SIM2
  then show ?case (is "wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2")
  proof -
    define R where \<open>R = ?R\<close>
    show ?thesis sorry
  qed
qed

section \<open>Correctness\<close>

abbreviation "init_sg \<equiv> init_subgraph (antichain_from_list oo raw_summary)"

(* TODO: Move. *)
lemma cfilter_cimage:
  \<open>cfilter P (f |`| X) = (f |`| cfilter (P \<circ> f) X)\<close>
  by auto

lemma correctness_aux:
  fixes lxs :: \<open>('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bots}, 'd1) event llist\<close>
  assumes \<open>timely_input_stream lxs (mset bots)\<close>
  shows \<open>mset_op cmempty cmempty (dataflow_op init_sg (G_op f
  (init_input_state default_internal_summary (\<lambda>_. lxs))
  (init_operator_state_ty2 default_internal_summary) (\<lambda>_. [])))
  \<approx> mset_spec_op (cmempty + cmempty + cmUnion (cmset_of_cset ((\<lambda>t. cmset_of_list (map (\<lambda>d :: 'd2. ((1, 1), (Inr d, t)))
    (f (coll ((map (\<lambda>(d :: 'd1 + 'd2, t). Data t (projl d)) (inputs_at_target init_op_states (1, 1))) @@- lxs) t))))
  |`| (cUn (ts lxs) (cset_from_list (map snd (inputs_at_target init_op_states (1, 1)))))))) cmempty\<close>
  using [[goals_limit=17]]
proof (rule correctness_gen)
  show \<open>\<forall>n. intsum (init_op_states n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    using loc_2_1_cases by (auto simp add: default_internal_summary_def raw_summary_def)
next
  have \<open>\<forall>loc. (antichain_from_list \<circ>\<circ> raw_summary) loc loc = {}\<^sub>A\<close> by (auto simp add: raw_summary_def)
  moreover have \<open>reachable_locations (antichain_from_list \<circ>\<circ> raw_summary) = UNIV\<close>
    using loc_2_1_cases is_empty_antichain_not_empty_list
    by (fastforce simp add: reachable_locations_def raw_summary_def)
  ultimately show \<open>dataplane_tracker_inv (init_op_states :: 2 \<Rightarrow> (1, 'd1 + 'd2, 't) operator_state) (\<lambda>_. []) init_sg\<close>
    unfolding init_subgraph_def using dataplane_tracker_inv_init_op_state[OF dataflow_topology_raw_summary]
    by fast
next
  define M :: \<open>((2 \<times> 1) \<times> ('d1 + 'd2) \<times> 't) cmset\<close> where \<open>M = cmempty + cmempty
  + cmUnion (cmset_of_cset ((\<lambda>t. cmset_of_list (map (\<lambda>d. ((1, 1), (Inr d, t)))
    (f (coll ((map (\<lambda>(d :: 'd1 + 'd2, t). Data t (projl d)) (inputs_at_target init_op_states (1, 1))) @@- lxs) t))))
  |`| (cUn (ts lxs) (cset_from_list (map snd (inputs_at_target init_op_states (1, 1)))))))\<close>
  show \<open>\<forall>t. in_cmset t (cmimage (snd \<circ> snd) M) \<longrightarrow>
  (\<exists>xs. cmimage (projr \<circ> fst \<circ> snd) (cmfilter (\<lambda>(_, (_, t')). t' = t) M) = cmset_of_list (f xs))\<close>
    apply (simp add: inputs_at_target_def M_def)
    apply safe
    subgoal for t
      apply (rule exI[of _ \<open>coll lxs t\<close>])
      apply (subgoal_tac \<open>t |\<in>| ts lxs\<close>)
       apply (simp add: cmfilter_cmUnion cmimage_cmUnion cmset.map_comp comp_def)
       apply (unfold cmset_eq_iff)
       apply (rule allI)
      subgoal for d
        apply (subst cmUnion_cmimage_cmset_of_cset_single[where x=\<open>cmset_of_list (map (\<lambda>d. ((1, 1), (Inr d, t))) (f (coll lxs t)))\<close>])
          apply simp
        subgoal for M
          apply (subgoal_tac \<open>\<exists>t'. M = cmset_of_list (map (\<lambda>d. ((1, 1), (Inr d, t'))) (f (coll lxs t')))\<close>)
           apply (erule exE)
          subgoal for t'
            apply (rule ccontr)
            apply (subgoal_tac \<open>t' = t\<close>)
             apply fast
            apply (simp add: cmfilter_cmset_of_list filter_map comp_def filter_const isum_eq_0_iff split: if_splits)
            apply (simp add: zero_enat_def)
            done
          apply blast
          done
        apply (simp add: cmfilter_cmset_of_list filter_map comp_def filter_True cmimage_cmset_of_list)
        done
      apply (force simp add: cmset_cmUnion cmset.set_map)
      done
    done
qed (auto simp add: init_subgraph_def ty1_check_def ty2_check_def input_ocaps_inv_def inputs_at_target_def operator_state.defs assms)

lemma tscomp_op_wire_eq_num1:
  \<open>(\<lambda>(nid :: 2, _ :: 1). if nid = 0 then Some (0 :: 2, 1 :: 1) else None) = [(0, 1) \<mapsto> (0, 1)]\<close>
  by force

lemma dataflow_tree_to_graph_to_raw_summary_tscomp2[simp]:
  \<open>dataflow_tree_to_graph (Comp (\<lambda>(nid, _). if nid = 0 then Some (0, 1) else None)
  (Logic op1 default_internal_summary) (Logic op2 default_internal_summary)) = raw_summary\<close>
  unfolding tscomp_op_wire_eq_num1 by (rule dataflow_tree_to_graph_to_raw_summary)

lemma correctness:
  fixes lxs :: \<open>('t :: {canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le, order_ccompare, bots}, 'd1) event llist\<close>
  assumes \<open>timely_input_stream lxs (mset bots)\<close>
  shows \<open>mset_op cmempty cmempty (compiled_batch_op (\<lambda> _. lxs) f)
  \<approx> mset_spec_op (cmUnion (cmset_of_cset ((\<lambda>t. cmset_of_list (map (\<lambda>x. ((1, 1), Inr x, t)) (f (coll lxs t)))) |`| ts lxs))) cmempty\<close>
  using correctness_aux[OF assms] by (auto simp add: compile_dataflow_def inputs_at_target_def)

lemma soundness:
  fixes t :: \<open>'t :: {canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le, order_ccompare, bots}\<close>
  assumes \<open>timely_input_stream lxs (mset bots)\<close> \<open>VOut p (Inr d, t) \<in> lset vios\<close>
    \<open>wtraced (compiled_batch_op (\<lambda> _. lxs) f) vios\<close> \<open>\<forall>vio \<in> lset vios. \<not>is_VInp vio\<close>
  shows \<open>d \<in> set (f (coll lxs t))\<close>
  using mset_op_soundness[OF correctness[OF assms(1)] assms(2-)] by (auto simp add: cmset_cmUnion)

lemma completeness:
  fixes t :: \<open>'t :: {canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le, order_ccompare, bots}\<close>
  assumes \<open>timely_input_stream lxs (mset bots)\<close> \<open>t |\<in>| ts lxs\<close> \<open>d \<in> set (f (coll lxs t))\<close>
  shows \<open>\<exists>vios. VOut (1, 1) (Inr d, t) \<in> lset vios \<and> wtraced (compiled_batch_op (\<lambda> _. lxs) f) vios\<close>
  using mset_op_completeness[OF correctness[OF assms(1)], of \<open>(1, 1)\<close> \<open>(Inr d, t)\<close> f] assms(2-)
  by - (drule meta_spec, drule meta_mp, fastforce simp add: cmset_cmUnion, blast)

end
