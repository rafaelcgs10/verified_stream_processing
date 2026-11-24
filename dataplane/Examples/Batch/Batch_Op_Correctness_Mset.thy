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
no_notation shiftr  (infixl \<open>>>\<close> 55)

declare if_cong[cong]
declare filter_True[simp del] filter_False[simp del] list_emb_Nil2[simp del]
  BULK_BENQ_right_empty[simp del] BULK_BENQ_left_empty[simp del] in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]


section \<open>Generalized Correctness\<close>

definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then [0]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then [0 :: _ :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}]
   else [])"

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

lemma dataflow_tree_to_graph_to_my_summ[simp]:
  "dataflow_tree_to_graph (Comp [(0, 1) \<mapsto> (0, 1)] (Logic op1 default_internal_summary) (Logic op2 default_internal_summary)) = (my_summ :: (2, 1) location \<Rightarrow> (2, 1) location \<Rightarrow> _ list)"
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
           apply (auto simp add: my_summ_def split: if_splits)
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
lemma dataflow_tree_to_graph_to_my_summ_tscomp[simp]:
  "dataflow_tree_to_graph (Logic op1 default_internal_summary \<sqdot>\<^bsub>1\<^esub> Logic op2 default_internal_summary) = (my_summ :: (2, 1) location \<Rightarrow> (2, 1) location \<Rightarrow> _ list)"
  unfolding tscomp_op_wire_eq by (rule dataflow_tree_to_graph_to_my_summ)

lemma outputs_at_target_my_summ[simp]:
  "outputs_at_target (antichain_from_list oo my_summ) os = (\<lambda> p. if p = (1, 0) then outpu (os 0) 0 else [])"
  unfolding outputs_at_target_def my_summ_def
  apply (rule ext)
  apply (auto simp add: antichain_from_list_singleton split: prod.splits if_splits)
  done

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
  \<open>batch_op [1 :: 1] f id bt_state = builder_op True {|1|} {|1|} bt_state
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

lemma filter_const:
  \<open>filter (\<lambda>x. P) xs = (if P then xs else [])\<close>
  by (cases P; simp add: filter_True filter_False)

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

(* TODO: Move to Cmset_Utils.thy. *)

lemma cmcount_cmsingle:
  \<open>cmcount (cmsingle x) y = (if y = x then 1 else 0)\<close>
  unfolding cmcount_cminsert cmcount_cmempty one_eSuc ..

lemma cmimage_plus:
  \<open>cmimage f (M + N) = cmimage f M + cmimage f N\<close>
  unfolding cmset_eq_iff cmcount_cmimage cmcount_plus isum_plus by blast

lemma cmimage_cminsert:
  \<open>cmimage f (cminsert x M) = cminsert (f x) (cmimage f M)\<close> unfolding cmset_eq_iff
proof
  fix y
  have \<open>cmcount (cmimage f (cminsert x M)) y = cmcount (cmimage f (cmsingle x)) y 
  + cmcount (cmimage f M) y\<close> by (subst cminsert_is_plus) (simp add: cmimage_plus cmcount_plus)
  also have \<open>\<dots> = cmcount (cmsingle (f x)) y + cmcount (cmimage f M) y\<close>
    by (subst cmcount_cmimage) (simp add: cmcount_cmsingle isum_eq_singl isum_eq_0_iff)
  also have \<open>\<dots> = cmcount (cminsert (f x) (cmimage f M)) y\<close> by (subst (2) cminsert_is_plus)
      (simp add: cmcount_plus)
  finally show \<open>cmcount (cmimage f (cminsert x M)) y = cmcount (cminsert (f x) (cmimage f M)) y\<close> .
qed

lemma cmfilter_split:
  \<open>M = cmfilter P M + cmfilter (Not \<circ> P) M\<close>
  unfolding cmset_eq_iff cmcount_plus cmfilter.rep_eq by simp

lemma cmset_disjoint_iff:
  \<open>M \<sqinter> N = cmempty \<longleftrightarrow> cmset M \<inter> cmset N = {}\<close>
  using cmcount_cmempty cmcount_less_in_cmset_minus cmcount_minus cmset_cmempty cmset_eq_iff
    cmset_inf gr_zeroI idiff_0_right inf.commute inf_bot_left insert_disjoint(2) by metis

lemma cmfilter_split_disjoint:
  \<open>cmfilter P M \<sqinter> cmfilter (Not \<circ> P) M = cmempty\<close>
  unfolding cmset_disjoint_iff cmset_alt cmfilter.rep_eq by force

lemma cmUnion_plus:
  assumes \<open>M \<sqinter> N = cmempty\<close>
  shows \<open>cmUnion (M + N) = cmUnion M + cmUnion N\<close> unfolding cmset_eq_iff
proof
  fix x
  let ?f = \<open>\<lambda>N'. cmcount N' x * cmcount (M + N) N'\<close>
  let ?g = \<open>\<lambda>N'. cmcount N' x * cmcount M N'\<close>
  let ?h = \<open>\<lambda>N'. cmcount N' x * cmcount N N'\<close>
  have f_g: \<open>\<And>N'. in_cmset N' M \<Longrightarrow> ?f N' = ?g N'\<close> and f_h: \<open>\<And>N'. in_cmset N' N \<Longrightarrow> ?f N' = ?h N'\<close>
    using assms unfolding cmset_disjoint_iff cmcount_plus cmset_alt by force+
  have \<open>cmcount (cmUnion (M + N)) x = isum ?f (cmset M \<union> cmset N)\<close> unfolding cmcount_cmUnion
      cmset_plus ..
  also have \<open>\<dots> = isum ?f (cmset M) + isum ?f (cmset N)\<close> using assms unfolding cmset_disjoint_iff
    by simp
  also have \<open>\<dots> = isum ?g (cmset M) + isum ?h (cmset N)\<close> using isum_cong[OF _ f_g]
      isum_cong[OF _ f_h] by fastforce
  also have \<open>\<dots> = cmcount (cmUnion M + cmUnion N) x\<close> unfolding cmcount_cmUnion cmcount_plus ..
  finally show \<open>cmcount (cmUnion (M + N)) x = cmcount (cmUnion M + cmUnion N) x\<close> .
qed

lemma cmUnion_cmfilter_split:
  \<open>cmUnion M = cmUnion (cmimage (cmfilter P) M) + cmUnion (cmimage (cmfilter (Not \<circ> P)) M)\<close>
  by (subst cmfilter_split) (simp add: cmfilter_cmUnion)

lemma correctness_gen:
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
    and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
    and ip_state :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
    and bt_state :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
    and os :: \<open>2 \<Rightarrow> (1, 'd1 + 'd2, 't) operator_state\<close>
    and chns :: \<open>2 \<times> 1 \<Rightarrow> (('d1 + 'd2) \<times> 't) list\<close>
    and sg :: \<open>(2, 1, 't) subgraph\<close>
  assumes
    \<open>raw_s = dataflow_tree_to_graph (G_dt f ip_state bt_state)\<close>
    \<open>summ sg = antichain_from_list oo raw_s\<close>
    \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    \<open>ip_state = operator_state.extend (os 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, es = inps\<rparr>\<close>
    \<open>bt_state = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr\<rparr>\<close>
    \<open>ty1_check ip_state (curry cbufs 0)\<close>
    \<open>ty2_check bt_state (curry cbufs 1)\<close>
    \<open>\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_s (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    \<open>input (os 0) = (\<lambda>_. [])\<close>
    \<open>initia (os 0)\<close>
    \<open>input_ocaps_inv (os 1)\<close>
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    \<open>cbufs (0, 0) = []\<close>
    \<open>dataplane_tracker_inv os cbufs sg\<close>
    \<open>SP = cmUnion (cmset_of_cset ((\<lambda>t. cmset_of_list (map (\<lambda>d. ((1, 1), (Inr d, t)))
      (f (coll ((map (\<lambda>(d, t'). Data t' (projl d)) (chns (1, 1))) @@- inps 1) t))))
  |`| cUn (ts (inps 1)) (snd |`| cset_from_list (chns (1, 1)))))\<close>
    \<open>SO = cmset_of_list (map (Pair (1, 1)) (outpu (os 1) 1))\<close>
    \<open>\<forall>t. in_cmset t (cmimage (snd \<circ> snd) (S + SO)) \<longrightarrow> \<not>frontier_less_equal (front (os 1) 1) t\<close>
    \<open>\<forall>t. in_cmset t (cmimage (snd \<circ> snd) (S + SO + SP)) \<longrightarrow>
  (\<exists>xs. cmimage (projr \<circ> fst \<circ> snd) (cmfilter (\<lambda>(_, (_, t')). t' = t) (S + SO + SP))
  = cmset_of_list (f xs))\<close>
    \<open>timely_input_stream (inps 1) (mset (ocaps (os 0) 1))\<close>
  shows 
    \<open>mset_op S D (dataflow_op sg (G_op f ip_state bt_state cbufs)) \<approx> mset_spec_op (S + SO + SP) D\<close>
  using assms unfolding tscomp_op_wire_eq
proof (coinduction arbitrary: os sg ip_state bt_state chns cbufs inps SP SO S D raw_s rule: weakBisimWeakUptoBisimCong)
  case SIM1
  note subgraph_inv = SIM1(1-3)
  note os_inv = SIM1(4-11)
  note bufs_inv = SIM1(12,13)
  note dataplane_inv = SIM1(14)
  note sets_inv = SIM1(15-18)
  note input_stream_inv = SIM1(19)
  then show ?case (is "wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2")
  proof -
    define R where \<open>R = ?R\<close>
    have "\<exists>op2'. step (Out (p, 1) (d, t)) (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S (cminsert ((p, 1), d, t) D) (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id bt_state)))))) op2'"
      if "in_cmset ((p, 1), d, t) (S - D)"
      for p :: 2
        and d :: "'d1 + 'd2"
        and t :: 't
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (BENQ (1, 1) (Inr (d, t)) (map Inr \<circ> cbufs))) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} (ip_state \<lparr>outpu := (outpu ip_state)(1 := xs)\<rparr>))) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id bt_state)))))) op2'"
      if "outpu ip_state 1 = (d, t) # xs"
      for d :: "'d1 + 'd2"
        and t :: 't
        and xs :: "(('d1 + 'd2) \<times> 't) buf"
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (BTL (1, 1) (map Inr \<circ> cbufs))) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (consumes bt_state 1 t d))))))) op2'"
      if "cbufs (1, 1) \<noteq> []"
        and "(d, t) = BHD (1, 1) cbufs"
      for d :: "'d1 + 'd2"
        and t :: 't
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} (ip_state'\<lparr>front := front ip_state, initia := True\<rparr>))) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id bt_state)))))) op2'"
      if "initia ip_state"
        and "ip_state' |\<in>| ooo_input_op_logic {|1|} ip_state"
      for ip_state' :: "(1, 'd1 + 'd2, 'd1, 't) input_state"
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (bt_state'\<lparr>front := front bt_state, initia := True\<rparr>))))))) op2'" (is \<open>\<exists>_. _ \<and> ((~) OO \<U> R OO (\<approx>)) ?op1' _\<close>)
      if "initia bt_state"
        and "bt_state' |\<in>| batch_op_logic [1] f id bt_state (\<lambda>_. filter (\<lambda>t. \<not>frontier_less_equal (front bt_state 1) t) (ocaps bt_state 1))"
    for bt_state' :: "(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2"
    proof -
      have dataflow_topo_sg: \<open>dataflow_topology (summ sg) (-+-)\<close>
        using dataflow_topology_from_tree.dataflow_topology_axioms subgraph_inv(1,2) by metis
      have graph_summar_sg: \<open>graph_summar_nt (summ sg) (nxt sg) os\<close> using graph_summar_nt
          subgraph_inv os_inv(5) by blast
      define caps where \<open>caps = (\<lambda>_ :: 1. filter (\<lambda>t. \<not>frontier_less_equal (front bt_state 1) t) (ocaps bt_state 1))\<close>
      define bt_state'' where \<open>bt_state'' = bt_state\<lparr>input := (\<lambda>_. filter (\<lambda>(_, t). t \<notin> set (caps 1)) (input bt_state 1))\<rparr>\<close>
      define outs where \<open>outs = batch_op_outputs [1] (batch_op_batches f bt_state caps) (batch_op_ts bt_state caps)\<close>
      have outs_not_frontier_less_equal: \<open>\<forall>t \<in> time ` snd ` set outs. \<not>frontier_less_equal (front (os 1) 1) t\<close>
        by (simp add: outs_def caps_def batch_op_outputs_def batch_op_ts_def os_inv(2,8) operator_state.defs)
      define drops where \<open>drops = batch_op_drops [1] caps\<close>
      have bt_state': \<open>bt_state' = drop_caps (produces bt_state'' (map (\<lambda>(d, cap). (en2 bt_state'' d, cap)) outs)) drops\<close>
        using that(2) by (simp add: batch_op_logic_alt caps_def bt_state''_def outs_def drops_def split: if_splits)
      define os' where \<open>os' = os(1 := operator_state.truncate bt_state')\<close>
      define chns' where \<open>chns' = outputs_at_target (summ sg) os' >> cbufs >> inputs_at_target os'\<close>
      define g where \<open>g = (\<lambda>t. cmset_of_list (map (\<lambda>d. ((1 :: 2, 1 :: 1), Inr d :: 'd1 + 'd2, t))
  (f (coll (map (\<lambda>(d, t'). Data t' (projl d)) (chns (1, 1)) @@- inps 1) t))))\<close>
      define h where \<open>h = (\<lambda>t. cmset_of_list (map (\<lambda>d. ((1 :: 2, 1 :: 1), Inr d :: 'd1 + 'd2, t))
  (f (coll (map (\<lambda>(d, t'). Data t' (projl d)) (chns' (1, 1)) @@- inps 1) t))))\<close>
      define SP' where \<open>SP' = cmUnion (cmset_of_cset (h |`| cUn (ts (inps 1)) (snd |`| cset_from_list (chns' (1, 1)))))\<close>
      define SO' where \<open>SO' = cmset_of_list (map (Pair (1 :: 2, 1 :: 1)) (outpu (os' 1) 1))\<close>
      have SO'_alt: \<open>SO' = SO + cmset_of_list (map (\<lambda>(d, cap). ((1, 1), (Inr d, time cap))) outs)\<close>
        by (simp add: SO'_def sets_inv(2) os'_def os_inv(2) bt_state' bt_state''_def
            operator_state.defs filter_True comp_def split_beta' cmset_of_list_append)
      have SP_alt: \<open>SP = SP' + cmset_of_list (map (\<lambda>(d, cap). ((1, 1), (Inr d, time cap))) outs)\<close> unfolding cmset_eq_iff
      proof
        fix x :: \<open>(2 \<times> 1) \<times> ('d1 + 'd2) \<times> 't\<close>
        obtain nid p d t where x: \<open>x = ((nid, p), (d, t))\<close> using prod.exhaust by metis
        show \<open>cmcount SP x = cmcount (SP' + cmset_of_list (map (\<lambda>(d, cap). ((1, 1), (Inr d, time cap))) outs)) x\<close>
        proof (cases \<open>nid = 1\<close>)
          case True
          show ?thesis
          proof (cases \<open>t |\<in>| cUn (ts (inps 1)) (snd |`| cset_from_list (chns (1, 1)))\<close>)
            case t_cin: True
            let ?ts = \<open>cUn (ts (inps 1)) (snd |`| cset_from_list (chns (1, 1)))\<close>
            let ?P = \<open>\<lambda>t. t \<notin> set (ocaps (os 1) 1) \<or> frontier_less_equal (front (os 1) 1) t\<close>
            have Ball_P: \<open>\<forall>t \<in> rcset (ts (inps 1)) \<union> snd ` set ((outputs_at_target (summ sg) os >> cbufs) (1, 1)). ?P t\<close>
            proof (intro ballI disjI2, erule UnE)
              fix t'
              assume \<open>t' \<in> rcset (ts (inps 1))\<close>
              have \<open>front (os 1) 1 \<le> ifrontier (summ sg) (-+-) (pt_tr sg) (Loc 1 (Trg 1))\<close>
                using order.trans dataplane_inv unfolding dataplane_tracker_inv_def front_inv_def
                  imp_front_inv_def  by blast
              moreover have \<open>frontier_less_equal \<dots> t'\<close>
              proof -
                have \<open>frontier_less_equal (frontier (to_zmset (ocaps (os 0) 1))) t'\<close>
                  using \<open>t' \<in> rcset (ts (inps 1))\<close> cin.rep_eq ts_lsetE
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
                        my_summ_def antichain_from_list_singleton is_empty_antichain_iff
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
            then have \<open>cfilter ?P ?ts = cUn (ts (inps 1)) (snd |`| cset_from_list (chns' (1, 1)))\<close>
              by (auto simp add: subgraph_inv(1,2) os_inv(2) bufs_inv(1) chns'_def os'_def bt_state'
                  bt_state''_def operator_state.defs inputs_at_target_def BULK_BENQ_def caps_def)
            let ?g = \<open>\<lambda>t. cmset_of_list (map (\<lambda>d. ((1, 1), (Inr d, t)))
  (f (coll ((map (\<lambda>(d, t'). Data t' (projl d)) (chns (1, 1))) @@- inps 1) t)))\<close>
            let ?h = \<open>\<lambda>t. cmset_of_list (map (\<lambda>d. ((1, 1), (Inr d, t)))
  (f (coll ((map (\<lambda>(d, t'). Data t' (projl d)) (chns' (1, 1))) @@- inps 1) t)))\<close>
            show ?thesis
            proof (cases \<open>?P t\<close>)
              case True
              then show ?thesis sorry
            next
              case False
              then have t_input: \<open>t \<in> snd ` set (input (os 1) 1)\<close> using t_cin Ball_P
                by (auto simp add: bufs_inv(1) BULK_BENQ_def inputs_at_target_def)
              then show ?thesis sorry
            qed
          next
            case False
            then have \<open>cmcount SP x = 0\<close> by (simp add: sets_inv(1) x cmcount_cmUnion isum_eq_0_iff)
                (auto simp add: zero_enat_def cmcount_cmset_of_cset)
            moreover have \<open>cmcount SP' x = 0\<close> using False
              by (simp add: SP'_def h_def chns'_def bufs_inv(1) x cmcount_cmUnion isum_eq_0_iff)
                (auto simp add: zero_enat_def cmcount_cmset_of_cset BULK_BENQ_def subgraph_inv(1,2)
                  os'_def os_inv(2) bt_state' bt_state''_def operator_state.defs
                  inputs_at_target_def)
            ultimately show ?thesis using False
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
        have "mset_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (bt_state' \<lparr>front := front bt_state, initia := True\<rparr>)))))) = mset_op S D (dataflow_op sg (dataflow_tree_to_operator cbufs (Comp [(0, 1) \<mapsto> (0, 1)] (input_dt ip_state) (batch_dt bt_state' f))))"
          by (simp add: dataflow_tree_to_operator_def bt_state' bt_state''_def that(1) comp_def)
        moreover have "(mset_spec_op (S + SO + SP) D::(2 \<times> 1, 2 \<times> 1, ('d1 + 'd2) \<times> 't) op) = mset_spec_op (S + SO' + SP') D"
          by (simp add: \<open>SO' + SP' = SO + SP\<close> add.assoc)
        moreover have "raw_s = dataflow_tree_to_graph (Comp [(0, 1) \<mapsto> (0, 1)] (input_dt ip_state) (batch_dt bt_state' f))"
          by (simp add: subgraph_inv(1))
        moreover have "summ sg = antichain_from_list \<circ>\<circ> raw_s"
          by (simp add: subgraph_inv(2))
        moreover have "nxt sg = graph_to_nxt (summ sg)"
          by (simp add: subgraph_inv(3))
        moreover have "ip_state = operator_state.extend (os' 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, es = inps\<rparr>"
          by (simp add: os_inv(1) os'_def)
        moreover have "bt_state' = operator_state.extend (os' 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr\<rparr>"
          by (simp add: os_inv(2) os'_def bt_state' bt_state''_def operator_state.defs)
        moreover have "ty1_check ip_state (curry cbufs 0)"
          by (simp add: os_inv(3))
        moreover have "ty2_check bt_state' (curry cbufs 1)" using os_inv(2-4)
          by (force simp add: ty2_check_def os'_def bt_state' bt_state''_def operator_state.defs)
        moreover have "\<forall>n. intsum (os' n) = (\<lambda>p1 p2. raw_s (Loc n (Trg p1)) (Loc n (Src p2)))"
          by (simp add: os_inv(2,5) os'_def bt_state' bt_state''_def operator_state.defs)
        moreover have "input (os' 0) = (\<lambda>_. [])"
          by (simp add: os_inv(6) os'_def)
        moreover have "initia (os' 0)"
          by (simp add: os_inv(7) os'_def)
        moreover have "input_ocaps_inv (os' 1)"
        proof -
          have \<open>filter (\<lambda>t. \<not>frontier_less_equal (front (os 1) 1) t) (ocaps (os 1) 1) \<noteq> []\<close>
            using that(2) by (simp add: os_inv(2) operator_state.defs batch_op_logic_alt split: if_splits)
          then show ?thesis using os_inv(8) by (clarsimp simp add: input_ocaps_inv_def os'_def
                os_inv(2,5) bt_state' bt_state''_def operator_state.defs drop_caps_def drops_def
                batch_op_drops_def ) (fastforce simp add: subgraph_inv(1) my_summ_def)
        qed
        moreover have "chns' = outputs_at_target (summ sg) os' >> cbufs >> inputs_at_target os'"
          by (simp add: chns'_def)
        moreover have "cbufs (0, 0) = []"
          by (simp flip: bufs_inv(2))
        moreover have "dataplane_tracker_inv os' cbufs sg"
          by (rule dataplane_tracker_inv_produces_drops'[OF _ dataflow_topo_sg refl refl refl refl refl _ _ _ _ graph_summar_sg subgraph_inv(3) dataplane_inv,
                where nid=1 and oputs=\<open>\<lambda>_ :: 1. map (\<lambda>(d, cap). (Inr d, time cap)) outs\<close>
                  and drops=\<open>\<lambda>_. map time drops\<close> and produs=\<open>map (\<lambda>(_, cap). (1, time cap, 1)) outs\<close>])
              (auto simp add: fun_eq_iff os'_def bt_state' bt_state''_def drop_caps_def produces_def
                operator_state.defs os_inv(2) filter_True comp_def split_beta enum_num1_def
                drops_def batch_op_drops_def image_image caps_def outs_def batch_op_outputs_def
                batch_op_ts_def batch_op_batches_def)
        moreover have "SP' = cmUnion (cmset_of_cset (h |`| cUn (ts (inps 1)) (snd |`| cset_from_list (chns' (1, 1)))))"
          by (simp add: SP'_def)
        moreover have "SO' = cmset_of_list (map (Pair (1, 1)) (outpu (os' 1) 1))"
          by (simp add: SO'_def)
        moreover have "\<forall>t. in_cmset t (cmimage (snd \<circ> snd) (S + SO')) \<longrightarrow> \<not>frontier_less_equal (front (os' 1) 1) t"
          by (simp add: sets_inv(3) SO'_alt os_inv(2) os'_def bt_state' bt_state''_def operator_state.defs cmimage_plus cmset_plus cmimage_cmset_of_list split_beta outs_not_frontier_less_equal image_image)
        moreover have "\<forall>t. in_cmset t (cmimage (snd \<circ> snd) (S + SO' + SP')) \<longrightarrow> (\<exists>xs. cmimage (projr \<circ> fst \<circ> snd) (cmfilter (\<lambda>(_, (_, t')). t' = t) (S + SO' + SP')) = cmset_of_list (f xs))"
          using sets_inv(4) by (simp add: \<open>SO' + SP' = SO + SP\<close> add.assoc)
        moreover have "timely_input_stream (inps 1) (mset (ocaps (os' 0) 1))"
          by (simp add: input_stream_inv os'_def)
        ultimately show ?thesis unfolding R_def h_def by blast
      qed
      then show ?thesis using bisim_refl wbisim_refl wb_upto_b_base by blast
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op (sg\<lparr>pt_tr := change_multiplicities (summ sg) (extract_progress 1 (nxt sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id bt_state')))))) op2'"
      if "(bt_state', st) = obtain_progress bt_state"
      for st :: "(1, 't) shared_state"
        and bt_state' :: "(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2"
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op (sg\<lparr>pt_tr := change_multiplicities (summ sg) (extract_progress 0 (nxt sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state')) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id bt_state)))))) op2'"
      if "(ip_state', st) = obtain_progress ip_state"
      for st :: "(1, 't) shared_state"
        and ip_state' :: "(1, 'd1 + 'd2, 'd1, 't) input_state"
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op S D (dataflow_op (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr>pt_tr := conf'\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (bt_state \<lparr>front := frontier \<circ> (\<lambda>p. c_imp (pt_tr (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr>pt_tr := conf'\<rparr>)) (Loc 1 (Trg 1))), initia := True\<rparr>))))))) op2'"
      sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (mset_spec_op (S + SO + SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (mset_op (cminsert ((1, 1), d, t) S) D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op comp_wire (case_sum (\<lambda>_. []) (map Inr \<circ> cbufs)) (map_op (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (case_option (Inl 0) (\<lambda>_. Inr (0, 1))) (ooo_input_op {|1|} ip_state)) (map_op (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (case_option (Inl 1) (\<lambda>_. Inr (1, 1))) (batch_op [1] f id (bt_state \<lparr>outpu := (outpu bt_state)(1 := xs)\<rparr>))))))) op2'"
      if "outpu bt_state 1 = (d, t) # xs"
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

abbreviation "my_sg \<equiv> init_subgraph (antichain_from_list oo my_summ)"

lemma correctness_aux:
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bots}, 'd1) event llist\<close>
  assumes T: \<open>timely_input_stream (inps 1) (mset bots)\<close>
  shows \<open>mset_op cmempty cmempty (dataflow_op my_sg (G_op f
  (init_input_state default_internal_summary inps)
  (init_operator_state_ty2 default_internal_summary) (\<lambda>_. [])))
  \<approx> mset_spec_op (cmempty + cmempty + cmUnion (cmimage (\<lambda>t. cmset_of_list (map (\<lambda>x. ((1, 1), (Inr x, t)))
    (f (coll ((map (\<lambda>(x, t). Data t (projl x)) (inputs_at_target init_op_states (1, 1))) @@- inps 1) t))))
  (cmset_of_cset (ts (inps 1)) + cmset_of_list (map snd (inputs_at_target init_op_states (1, 1)))))) cmempty\<close>
  apply (rule correctness_gen[where S="cmempty" and os=init_op_states and SO="cmempty" and D="cmempty" and sg=my_sg and inps=inps and cbufs="\<lambda> _. []" and ip_state="(init_input_state default_internal_summary inps)" and bt_state="init_operator_state_ty2 default_internal_summary"])
  (* Before any simp runs: simp would otherwise collapse the singleton-port
     conjunct in the wire, leaving a form no my_summ rule matches. *)
  unfolding tscomp_op_wire_eq
                  apply (simp_all add: input_ocaps_inv_def operator_state.defs ty2_check_def ty1_check_def init_subgraph_def)
  subgoal
    using loc_2_1_cases  by (auto del: ext intro!: ext simp add: default_internal_summary_def my_summ_def)
  subgoal
    apply (rule dataplane_tracker_inv_init_op_state[where isu=default_internal_summary and su="antichain_from_list \<circ>\<circ> my_summ" and i="\<lambda> (nid :: 2). nid = 0", simplified])
    subgoal  
      unfolding comp_def
      using dataflow_topology_from_tree.dataflow_topology_axioms[unfolded comp_def, of "(Comp [((0 :: 2), (1 :: 1)) \<mapsto> (0, 1)] (Logic _ default_internal_summary) (Logic _ default_internal_summary))", simplified]
      by auto
    subgoal
      unfolding my_summ_def
      by auto
    subgoal
      unfolding reachable_locations_def
      apply (auto simp add: image_iff split_beta )
      using loc_2_1_cases apply blast
      using loc_2_1_cases apply blast
       apply (smt (verit, del_insts) is_empty_antichain_not_empty_list loc_2_1_cases my_summ_def zero_one)+
      done
    done
  subgoal
    by (simp add: inputs_at_target_def)
  subgoal
    apply (simp add: inputs_at_target_def)
    apply safe
    subgoal for t
      apply (rule exI[of _ \<open>coll (inps 1) t\<close>])
      apply (simp add: cmfilter_cmUnion cmimage_cmUnion cmset.map_comp comp_def
          cmfilter_cmset_of_list filter_map filter_const if_distrib cmimage_cmset_of_list cmset_cmUnion map_replicate_const cmset.set_map)
      apply (elim exE conjE)
      subgoal for e
        apply (subgoal_tac \<open>t |\<in>| ts (inps 1)\<close>)
         apply (simp add: cmset_eq_iff cmcount_cmUnion)
         apply (rule allI)
         apply (subst isum_eq_singl[OF refl, where a=\<open>cmset_of_list (f (coll (inps 1) t))\<close>])
           apply (intro allI impI)
        subgoal for x M
          apply (cases \<open>cmcount M x = 0\<close>; auto simp add: isum_eq_0_iff cmset_eq_iff)
          done
        subgoal
          by (simp add: cmset.set_map)
        subgoal for x
          apply (cases \<open>enat (count_list (f (coll (inps 1) t)) x) = 0\<close>; simp)
          apply (subgoal_tac \<open>{t'. t' \<noteq> t \<longrightarrow> (\<forall>x. enat (count_list (f (coll (inps 1) t)) x) = 0)} = {t}\<close>)
           apply (auto simp add: cmcount_cmset_of_cset)
          done
        apply simp
        done
      done
    done
  subgoal
    using T by auto
  done

(* Third wire shape: at port type 1 simp collapses the port conjunct. *)
lemma tscomp_op_wire_eq_num1:
  "(\<lambda> (nid :: 2, p' :: 1). if nid = 0 then Some (0 :: 2, 1 :: 1) else None) = [(0, 1) \<mapsto> (0, 1)]"
  by (rule ext) (auto split: prod.splits)

lemma dataflow_tree_to_graph_to_my_summ_tscomp2[simp]:
  "dataflow_tree_to_graph (Comp (\<lambda> (nid, p'). if nid = 0 then Some (0, 1) else None) (Logic op1 default_internal_summary) (Logic op2 default_internal_summary)) = (my_summ :: (2, 1) location \<Rightarrow> (2, 1) location \<Rightarrow> _ list)"
  unfolding tscomp_op_wire_eq_num1 by (rule dataflow_tree_to_graph_to_my_summ)

lemma correctness:
  fixes inps :: \<open>('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bots}, 'd1) event llist\<close>
  assumes T: "timely_input_stream inps (mset bots)"
  shows "mset_op cmempty cmempty (compiled_batch_op (\<lambda> _. inps) f) \<approx>
         mset_spec_op (cmUnion (cmimage (\<lambda>t. cmset_of_list (map (\<lambda>x. ((1, 1), Inr x, t)) (f (coll inps t)))) (cmset_of_cset (ts inps)))) cmempty"
  using T apply -
  apply (drule correctness_aux[unfolded BULK_BENQ_def outputs_at_target_def inputs_at_target_def, simplified, where f=f])
  unfolding compile_dataflow_def
  apply simp
  done

lemma soundness:
  fixes inps :: \<open>('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bots}, 'd1) event llist\<close>
    and ios :: "(2 \<times> 1, 2 \<times> 1, ('d1 + 'b) \<times> 't) VIO llist"
  assumes T: "timely_input_stream inps (mset bots)"
  shows 
    "wtraced (compiled_batch_op (\<lambda> _. inps) f) ios \<Longrightarrow>
   \<forall>vio\<in>lset ios. \<not> is_VInp vio \<Longrightarrow>
   VOut p (Inr r, t) \<in> lset ios \<Longrightarrow> 
   r \<in> set (f (coll inps t))"
  apply (drule mset_op_soundness[OF correctness, of inps p \<open>(Inr r, t)\<close> ios f, OF T])
    apply assumption+
  apply (clarsimp simp add: cmset_cmUnion cmset.set_map)
  done

lemma completeness:
  fixes inps :: \<open>('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bots}, 'd1) event llist\<close>
    and ios :: "(2 \<times> 1, 2 \<times> 1, ('d1 + 'b) \<times> 't) VIO llist"
  assumes T: "timely_input_stream inps (mset bots)"
  shows 
    "Data t d \<in> lset inps \<Longrightarrow> r \<in> set (f (coll inps t)) \<Longrightarrow>
   \<exists>ios. wtraced (compiled_batch_op (\<lambda> _. inps) f) ios \<and> VOut (1, 1) (Inr r, t) \<in> lset ios"
  using mset_op_completeness[OF correctness, of inps "(1, 1)" \<open>(Inr r, t)\<close> f, simplified, unfolded image_iff, simplified, OF T] apply -
  apply (drule meta_spec)+
  apply (drule meta_mp)
   apply (force simp add: cmset_cmUnion cmset.set_map)+
  done

end
