theory Dataplane_Inv

imports
  Loop
  Input0
begin

lemma label_prop_input0_step_batch_caps:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes IOC: \<open>input_ocaps_inv os\<close>
    and zero: \<open>0 \<in> set (intsum os (0 :: 2) (1 :: 2))\<close>
    and input: \<open>(d, t) \<in> set (input os (0 :: 2))\<close>
    and member: \<open>(x, cap) \<in> set (label_prop_input0_step_batch os d t)\<close>
  shows \<open>\<exists>t'\<in>set (ocaps os (out cap)). t' \<le> capability.time cap\<close>
proof -
  have t_ocaps: \<open>t \<in> set (ocaps os (1 :: 2))\<close>
    using IOC[unfolded input_ocaps_inv_def, rule_format, where p=0 and p'=1] zero input
    by force
  have shape: \<open>out cap = 1 \<and> myfst t \<le> myfst (capability.time cap) \<and> mysnd (capability.time cap) = mysnd t\<close>
    using member
    unfolding label_prop_input0_step_batch_def label_prop_edge_batch_def Let_def
    by (auto split: if_splits)
  then show ?thesis
    using t_ocaps by (intro bexI[where x=t]) (auto simp add: less_eq_myprod_def)
qed


lemma input_ocaps_inv_label_prop_input0_step_stateI:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (label_prop_input0_step_state os d t)\<close>
  unfolding label_prop_input0_step_state_def Let_def
  apply (rule input_ocaps_inv_release_capsI)
  apply (rule input_ocaps_inv_drop_produces_add_capsI)
  using assms
  by (auto dest: in_set_tlD simp add: input_ocaps_inv_def input_tl_def label_prop_edge_record_update_def)






lemma dataplane_tracker_inv_label_prop_input0_step_state:
  fixes ls :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>'nid :: {enum, linorder} \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg\<close>
    and G: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and IOC: \<open>input_ocaps_inv ls\<close>
    and zero: \<open>0 \<in> set (intsum ls (0 :: 2) (1 :: 2))\<close>
    and input: \<open>input ls (0 :: 2) = (d, t) # xs\<close>
  shows \<open>dataplane_tracker_inv (os(nid := op_state_base (label_prop_input0_step_state ls d t))) cbufs sg\<close>
proof -
  let ?ls1 = \<open>input_tl ls (0 :: 2)\<close>
  let ?v1 = \<open>fst (de1 ls d)\<close>
  let ?v2 = \<open>snd (de1 ls d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l1 = \<open>min_label ls ?t1 ?v1\<close>
  let ?l2 = \<open>min_label ls ?t1 ?v2\<close>
  let ?v = \<open>if ?l1 > ?l2 then ?v1 else ?v2\<close>
  let ?l = \<open>if ?l1 > ?l2 then ?l2 else ?l1\<close>
  let ?ls2 = \<open>label_prop_edge_record_update ?ls1 ?t1 ?v1 ?v2 ?v ?l\<close>
  let ?batch = \<open>label_prop_input0_step_batch ls d t\<close>
  have inv_base2: \<open>dataplane_tracker_inv (os(nid := op_state_base ?ls2)) cbufs sg\<close>
  proof -
    have fields: \<open>\<forall>nid'. intsum ((os(nid := op_state_base ls)) nid') = intsum ((os(nid := op_state_base ?ls2)) nid') \<and>
      ocaps ((os(nid := op_state_base ls)) nid') = ocaps ((os(nid := op_state_base ?ls2)) nid') \<and>
      consu ((os(nid := op_state_base ls)) nid') = consu ((os(nid := op_state_base ?ls2)) nid') \<and>
      inter ((os(nid := op_state_base ls)) nid') = inter ((os(nid := op_state_base ?ls2)) nid') \<and>
      produ ((os(nid := op_state_base ls)) nid') = produ ((os(nid := op_state_base ?ls2)) nid') \<and>
      outpu ((os(nid := op_state_base ls)) nid') = outpu ((os(nid := op_state_base ?ls2)) nid') \<and>
      front ((os(nid := op_state_base ls)) nid') = front ((os(nid := op_state_base ?ls2)) nid')\<close>
      by (auto simp add: op_state_base_def input_tl_def label_prop_edge_record_update_def)
    show ?thesis
      using iffD1[OF dataplane_tracker_inv_clean_input[OF fields] Inv] .
  qed
  have G_base2: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2))\<close>
  proof -
    have geq: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2)) =
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
      by (rule graph_summar_nt_intsum_cong)
        (simp add: op_state_base_def input_tl_def label_prop_edge_record_update_def)
    show ?thesis
      using geq G by simp
  qed
  have input_member: \<open>(d, t) \<in> set (input ls (0 :: 2))\<close>
    using input by simp
  have batch_caps: \<open>\<And>x cap. (x, cap) \<in> set ?batch \<Longrightarrow>
    \<exists>t'\<in>set (ocaps (op_state_base ?ls2) (out cap)). t' \<le> capability.time cap\<close>
    using label_prop_input0_step_batch_caps[OF IOC zero input_member]
    by (simp add: op_state_base_def input_tl_def label_prop_edge_record_update_def)
  have inv_drop:
    \<open>dataplane_tracker_inv
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)))
      cbufs sg\<close>
    by (rule dataplane_tracker_inv_add_caps_produces_drop_caps_update[OF D inv_base2 G_base2 Nxt batch_caps])
  have G_drop:
    \<open>graph_summar_nt (summ sg) (nxt sg)
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)))\<close>
  proof -
    have geq: \<open>graph_summar_nt (summ sg) (nxt sg)
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch))) =
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2))\<close>
      by (rule graph_summar_nt_intsum_cong) (simp add: drop_caps_def produces_def add_caps_def)
    show ?thesis
      using geq G_base2 by simp
  qed
  have inv_release:
    \<open>dataplane_tracker_inv
      (os(nid := release_caps (drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)) 1))
      cbufs sg\<close>
    by (rule dataplane_tracker_inv_release_caps_update[OF D inv_drop G_drop Nxt])
  have step_base:
    \<open>op_state_base (label_prop_input0_step_state ls d t) =
      release_caps (drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)) 1\<close>
    unfolding label_prop_input0_step_state_def label_prop_input0_step_batch_def Let_def
    by simp
  show ?thesis
    using inv_release by (simp add: step_base)
qed


lemma dataplane_tracker_inv_label_prop_input0_batched:
  fixes ls :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>'nid :: {enum, linorder} \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg\<close>
    and G: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and IOC: \<open>input_ocaps_inv ls\<close>
    and zero: \<open>0 \<in> set (intsum ls (0 :: 2) (1 :: 2))\<close>
  shows \<open>dataplane_tracker_inv
    (os(nid := op_state_base (fst (label_prop_input0_batched ls (input ls (0 :: 2)))))) cbufs sg\<close>
proof -
  have aux:
    \<open>msgs = input ls (0 :: 2) \<Longrightarrow>
      dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg \<Longrightarrow>
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls)) \<Longrightarrow>
      input_ocaps_inv ls \<Longrightarrow>
      0 \<in> set (intsum ls (0 :: 2) (1 :: 2)) \<Longrightarrow>
      dataplane_tracker_inv
        (os(nid := op_state_base (fst (label_prop_input0_batched ls (input ls (0 :: 2)))))) cbufs sg\<close>
    for msgs ls
  proof (induct msgs arbitrary: ls)
    case Nil
    then show ?case by simp
  next
    case (Cons msg msgs)
    obtain d t where msg_eq: \<open>msg = (d, t)\<close>
      by (cases msg)
    have input_eq: \<open>input ls (0 :: 2) = (d, t) # msgs\<close>
      using Cons.prems(1) msg_eq by simp
    let ?ls' = \<open>label_prop_input0_step_state ls d t\<close>
    have inv_step: \<open>dataplane_tracker_inv (os(nid := op_state_base ?ls')) cbufs sg\<close>
      by (rule dataplane_tracker_inv_label_prop_input0_step_state[OF D Cons.prems(2) Cons.prems(3) Nxt Cons.prems(4) Cons.prems(5) input_eq])
    have G_step: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls'))\<close>
    proof -
      have geq: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls')) =
        graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
        by (rule graph_summar_nt_intsum_cong) (simp add: label_prop_input0_step_state_def Let_def op_state_base_def)
      show ?thesis
        using geq Cons.prems(3) by simp
    qed
    have IOC_step: \<open>input_ocaps_inv ?ls'\<close>
      by (rule input_ocaps_inv_label_prop_input0_step_stateI[OF Cons.prems(4)])
    have zero_step: \<open>0 \<in> set (intsum ?ls' (0 :: 2) (1 :: 2))\<close>
      using Cons.prems(5) by simp
    have input_step: \<open>msgs = input ?ls' (0 :: 2)\<close>
      using input_eq by simp
    have rec: \<open>dataplane_tracker_inv
      (os(nid := op_state_base (fst (label_prop_input0_batched ?ls' (input ?ls' (0 :: 2)))))) cbufs sg\<close>
      by (rule Cons.hyps[OF input_step inv_step G_step IOC_step zero_step])
    obtain ls_final batches where rec_eq:
      \<open>label_prop_input0_batched ?ls' msgs = (ls_final, batches)\<close>
      by (cases \<open>label_prop_input0_batched ?ls' msgs\<close>)
    show ?case
      using rec input_eq msg_eq rec_eq by (simp add: fun_upd_def)
  qed
  show ?thesis
    by (rule aux[OF refl Inv G IOC zero])
qed



subsection \<open>One-step dataplane preservation for input-1 loop update\<close>

lemma loop_updates_preserves_dataplane_tracker_inv:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step:
    \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(1 := op_state_base os_label_prop)) cbufs sg\<close>
    and label_prop_extension:
    \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    and Summ: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
    (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and IOC1: \<open>input_ocaps_inv os_label_prop\<close>
    and IOC2: \<open>input_ocaps_inv (os 2)\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  shows \<open>dataplane_tracker_inv (os'(1 := op_state_base os_label_prop')) cbufs' sg\<close>
  using step D GR Nxt Inv label_prop_extension Summ Intsum IOC1 IOC2 INV LABELS WF

proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' T G V L rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  note loop_step = "1.prems"(1)
  note D0 = "1.prems"(2)
  note GR0 = "1.prems"(3)
  note Nxt0 = "1.prems"(4)
  note Inv0 = "1.prems"(5)
  note Ext0 = "1.prems"(6)
  note Summ0 = "1.prems"(7)
  note Intsum0 = "1.prems"(8)
  note IOC10 = "1.prems"(9)
  note IOC20 = "1.prems"(10)
  note INV0 = "1.prems"(11)
  note LABELS0 = "1.prems"(12)
  note WF0 = "1.prems"(13)

  have good: \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    using INV0 LABELS0 WF0 by blast


  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto

  have Inv1: \<open>dataplane_tracker_inv (os1(1 := op_state_base os_label_prop1)) cbufs1 sg\<close>
    by (rule label_prop_input1_loop_updates_preserves_dataplane_tracker_inv_corrected
        [OF step1[symmetric] D0 GR0 Nxt0 Inv0 Ext0 Summ0 Intsum0 IOC10 IOC20])

  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      apply (subst loop_updates.simps)
      using good step1 True by simp
    show ?thesis
      using loop_step loop_eq Inv1 by (simp add: fun_upd_def)
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      apply (subst loop_updates.simps)
      using good step1 False by simp
    have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
      using loop_step loop_eq by simp
    have GR1: \<open>graph_summar_nt (summ sg) (nxt sg) (os1(1 := op_state_base os_label_prop1))\<close>
      by (rule graph_summar_nt_label_prop_input1_loop_updates_corrected[OF step1[symmetric] GR0])
    have Ext1:
      \<open>os_label_prop1 = operator_state.extend (op_state_base os_label_prop1)
        \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
          en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V,
          label = label os_label_prop1\<rparr>\<close>
      by (rule label_prop_input1_loop_updates_extension[OF step1[symmetric] Ext0])

    have Intsum1: \<open>\<forall>n. intsum ((os1(1 := op_state_base os_label_prop1)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
      using label_prop_input1_loop_updates_intsum_corrected[OF step1[symmetric]] Intsum0 by simp
    have IOC11: \<open>input_ocaps_inv os_label_prop1\<close>
      by (rule input_ocaps_inv_label_prop_input1_loop_updates_label[OF step1[symmetric] IOC10])
    have IOC21: \<open>input_ocaps_inv (os1 2)\<close>
      by (rule input_ocaps_inv_label_prop_input1_loop_updates_os2[OF step1[symmetric] IOC20 Intsum0])
    have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
      by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] INV0 WF0])
    have LABELS1: \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
      by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] INV0 WF0 LABELS0])
    have EN10: \<open>en1 os_label_prop = Inl\<close>
      using arg_cong[OF Ext0, of en1]
      by (simp add: operator_state.defs)
    have DE10: \<open>de1 os_label_prop = projl\<close>
      using arg_cong[OF Ext0, of de1]
      by (simp add: operator_state.defs)
    have INPUT11: \<open>input os_label_prop1 1 = []\<close>
      by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
    have WF_msgs1: \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      by (rule label_prop_input1_loop_updates_msgs_invI
          [OF step1[symmetric] EN10 DE10 INV0 LABELS0 WF0])
    have WF1: \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      using INPUT11 WF_msgs1 by simp

    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            step_rec D0 GR1 Nxt0 Inv1 Ext1 Summ0 Intsum1 IOC11 IOC21 INV1 LABELS1 WF1])

  qed
qed


subsection \<open>Progress comparison for loop_updates\<close>


lemma loop_updates_final_dataplane_tracker_inv_for_progress:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes label_prop_extension:
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and Summ: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
        (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and IOC1: \<open>input_ocaps_inv os_label_prop\<close>
    and IOC2: \<open>input_ocaps_inv (os 2)\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and DATAPLANE: \<open>dataplane_tracker_inv os cbufs sg\<close>
  shows \<open>dataplane_tracker_inv
    ((snd (snd (loop_updates cbufs os_label_prop os)))
      (1 := op_state_base (fst (snd (loop_updates cbufs os_label_prop os)))))
    (fst (loop_updates cbufs os_label_prop os)) sg\<close>
proof -
  let ?res = \<open>loop_updates cbufs os_label_prop os\<close>
  have step: \<open>(fst ?res, fst (snd ?res), snd (snd ?res)) = ?res\<close>
    by (cases ?res) simp
  have base_label_prop: \<open>op_state_base os_label_prop = os 1\<close>
    using label_prop_extension
    unfolding op_state_base_def
    by (simp add: operator_state.defs)
  have base_inv: \<open>dataplane_tracker_inv (os(1 := op_state_base os_label_prop)) cbufs sg\<close>
    using DATAPLANE by (simp add: base_label_prop)
  have ext_base:
    \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop)
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T,
        graph = G, vertices = V, label = L\<rparr>\<close>
    using label_prop_extension
    by (simp add: op_state_base_def operator_state.defs)
  show ?thesis
    by (rule loop_updates_preserves_dataplane_tracker_inv
        [OF step D GR Nxt base_inv ext_base Summ Intsum IOC1 IOC2 INV LABELS WF])

qed






lemma dataplane_tracker_inv_buffer_balance_aux:
  fixes os :: "3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state"
    and cbufs :: "3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf"
    and sg :: "(3, 2, (nat, nat) myprod) subgraph"
  assumes D: "dataplane_tracker_inv os cbufs sg"
    and conn_eq: "(outputs_at_target (summ sg) os >> cbufs) (2, 1)
                  = outpu (os 1) 1 @ cbufs (2, 1)"
  shows "to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))
       = c_pts (change_multiplicities (summ sg)
                  (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))"
proof -
  from D obtain caps where
    Trg: "Trg_caps_inv caps (outputs_at_target (summ sg) os >> cbufs)" and
    cp: "c_pts_inv (change_multiplicities (summ sg)
            (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) caps"
    unfolding dataplane_tracker_inv_def by blast
  have caps_eq:
    "caps (Loc 2 (Trg 1)) = to_zmset (map snd ((outputs_at_target (summ sg) os >> cbufs) (2, 1)))"
    using Trg unfolding Trg_caps_inv_def by blast
  have caps_simp:
    "caps (Loc 2 (Trg 1)) = to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))"
    using caps_eq conn_eq by (simp add: to_zmset_append)
  have c_pts_eq:
    "c_pts (change_multiplicities (summ sg)
              (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))
     = caps (Loc 2 (Trg 1))"
    using cp unfolding c_pts_inv_def by simp
  show ?thesis
    using caps_simp c_pts_eq by simp
qed


lemma extract_prog_at_loc_2_trg_1:
  fixes os :: "3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state"
  assumes nt_1_1: "nt (1::3, 1::2) = Some ((2::3), (1::2))"
    and nt_1_0: "nt ((1::3), (0::2)) = None"
    and nt_2_0: "nt ((2::3), (0::2)) = None"
    and nt_2_1: "nt ((2::3), (1::2)) = Some ((1::3), (1::2))"
    and nt_0_0: "nt ((0::3), (0::2)) = None"
    and nt_0_1: "nt ((0::3), (1::2)) = None"
  shows "zmset (map snd (filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
                  (extract_prog Enum.enum nt os)))
       = zmset (map (\<lambda>(p, t, m). (t, m))
                  (filter (\<lambda>(p, _, _). p = (1::2)) (produ (os 1))))
       - zmset (map (\<lambda>(p, t, m). (t, m))
                  (filter (\<lambda>(p, _, _). p = (1::2)) (consu (os 2))))"
proof -
  let ?F = "\<lambda>xs. filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l') xs"
  have nt_1_cases: "nt ((1::3), q) = (if q = (1::2) then Some (2, 1) else None)" for q
    using nt_1_0 nt_1_1 by (cases "q = 1") (auto, metis num2_neq(2))
  have nt_2_cases: "nt ((2::3), q) = (if q = (1::2) then Some (1, 1) else None)" for q
    using nt_2_0 nt_2_1 by (cases "q = 1") (auto, metis num2_neq(2))
  have nt_0_all: "nt ((0::3), q) = None" for q :: 2
    using nt_0_0 nt_0_1 by (cases "q = 1") (auto, metis num2_neq(2))
      (* unfold extract_prog *)
  have ep_unfold: "extract_prog Enum.enum nt os
    = extract_progress 0 nt (snd (obtain_progress (os 0)))
    @ extract_progress 1 nt (snd (obtain_progress (os 1)))
    @ extract_progress 2 nt (snd (obtain_progress (os 2)))"
    unfolding extract_prog_def by simp
      (* helper inductive facts *)
  have map_filter_None_const:
    "List.map_filter (\<lambda>(p, t, m). None) xs = []" for xs :: "('a \<times> 'b \<times> 'c) list"
    by (induct xs) (auto simp: List.map_filter_def split: prod.splits)
  have cons_empty_other_nid:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (map (\<lambda>(p, t, m). (Loc nid (Trg p), t, -m)) xs) = []"
    if "nid \<noteq> (2::3)" for nid xs
    by (induct xs) (use that in \<open>auto split: prod.splits\<close>)
  have inter_empty:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (map (\<lambda>(p, y). (Loc nid (Src p), y)) xs) = []" for nid xs
    by (induct xs) (auto split: prod.splits)
  have prod_empty_when_nt_None:
    "List.map_filter (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None
                              | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs = []"
    if "\<And>p. nt (nid, p) = None" for nid xs
    by (induct xs) (auto simp: List.map_filter_def that split: prod.splits)
  have prod_match_nt_1:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (List.map_filter (\<lambda>(p, t, m). case nt ((1::3), p) of None \<Rightarrow> None
                                       | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs)
     = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, m))
         (filter (\<lambda>(p, _, _). p = (1::2)) xs)" for xs
    by (induct xs)
      (auto simp: List.map_filter_def nt_1_cases split: prod.splits if_splits)
  have prod_empty_nt_2:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (List.map_filter (\<lambda>(p, t, m). case nt ((2::3), p) of None \<Rightarrow> None
                                       | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs) = []" for xs
    by (induct xs)
      (auto simp: List.map_filter_def nt_2_cases split: prod.splits if_splits)
  have cons_match_2:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (map (\<lambda>(p, t, m). (Loc (2::3) (Trg p), t, -m)) xs)
     = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, -m))
         (filter (\<lambda>(p, _, _). p = (1::2)) xs)" for xs
    by (induct xs) (auto split: prod.splits)
      (* assemble *)
  have nid0_empty: "?F (extract_progress 0 nt (snd (obtain_progress (os 0)))) = []"
    unfolding extract_progress_def obtain_progress_def
    by (simp add: split_beta cons_empty_other_nid inter_empty
        prod_empty_when_nt_None[OF nt_0_all])
  have nid1_routed:
    "?F (extract_progress 1 nt (snd (obtain_progress (os 1))))
    = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, m))
        (filter (\<lambda>(p, _, _). p = 1) (produ (os 1)))"
    unfolding extract_progress_def obtain_progress_def
    by (simp add: split_beta cons_empty_other_nid inter_empty prod_match_nt_1)
  have nid2_cons_only:
    "?F (extract_progress 2 nt (snd (obtain_progress (os 2))))
    = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, -m))
        (filter (\<lambda>(p, _, _). p = 1) (consu (os 2)))"
    unfolding extract_progress_def obtain_progress_def
    by (simp add: split_beta cons_match_2 inter_empty prod_empty_nt_2)
  have filtered_eq:
    "?F (extract_prog Enum.enum nt os)
    = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, m))
        (filter (\<lambda>(p, _, _). p = 1) (produ (os 1)))
    @ map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, -m))
        (filter (\<lambda>(p, _, _). p = 1) (consu (os 2)))"
    unfolding ep_unfold filter_append
    using nid0_empty nid1_routed nid2_cons_only by simp
      (* final zmset arithmetic *)
  have map_snd_drop_loc_pos:
    "map snd (map (\<lambda>(p, t, m). (Loc (2::3) (Trg (1::2)), t, m)) xs) 
     = map (\<lambda>(p, t, m). (t, m)) xs" for xs :: "(2 \<times> (nat, nat) myprod \<times> int) list"
    by (induct xs) (auto split: prod.splits)
  have map_snd_drop_loc_neg:
    "map snd (map (\<lambda>(p, t, m). (Loc (2::3) (Trg (1::2)), t, -m)) xs) 
     = map (\<lambda>(p, t, m). (t, -m)) xs" for xs :: "(2 \<times> (nat, nat) myprod \<times> int) list"
    by (induct xs) (auto split: prod.splits)
  have zmset_neg_3:
    "zmset (map (\<lambda>(p, t, m). (t, -m)) xs) = - zmset (map (\<lambda>(p, t, m). (t, m)) xs)"
    for xs :: "(2 \<times> (nat, nat) myprod \<times> int) list"
    by (simp add: case_prod_unfold)
  show ?thesis
    unfolding filtered_eq
    by (simp add: case_prod_beta' comp_def split_beta map_append zmset_append map_snd_drop_loc_pos map_snd_drop_loc_neg zmset_neg_3)
qed


lemma dataplane_buffer_consu_produ_balance:
  fixes os :: "3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state"
    and cbufs :: "3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf"
    and sg :: "(3, 2, (nat, nat) myprod) subgraph"
  assumes D: "dataplane_tracker_inv os cbufs sg"
    and Nxt: "nxt sg = nt"
    and conn_eq: "(outputs_at_target (summ sg) os >> cbufs) (2, 1)
                  = outpu (os 1) 1 @ cbufs (2, 1)"
    and nt_1_1: "nt (1::3, 1::2) = Some ((2::3), (1::2))"
    and nt_1_0: "nt ((1::3), (0::2)) = None"
    and nt_2_0: "nt ((2::3), (0::2)) = None"
    and nt_2_1: "nt ((2::3), (1::2)) = Some ((1::3), (1::2))"
    and nt_0_0: "nt ((0::3), (0::2)) = None"
    and nt_0_1: "nt ((0::3), (1::2)) = None"
  shows "to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))
       + zmset (map (\<lambda>(p, t, m). (t, m))
                  (filter (\<lambda>(p, _, _). p = (1::2)) (consu (os 2))))
       = c_pts (pt_tr sg) (Loc (2::3) (Trg (1::2)))
       + zmset (map (\<lambda>(p, t, m). (t, m))
                  (filter (\<lambda>(p, _, _). p = (1::2)) (produ (os 1))))"
proof -
  have buffer_balance:
    "to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))
     = c_pts (change_multiplicities (summ sg)
                (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))"
    using D conn_eq by (rule dataplane_tracker_inv_buffer_balance_aux)
  also have "c_pts (change_multiplicities (summ sg)
                (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))
           = c_pts (pt_tr sg) (Loc 2 (Trg 1))
           + zmset (map snd (filter (\<lambda>(l', _, _). Loc 2 (Trg 1) = l')
                  (extract_prog Enum.enum (nxt sg) os)))"
    by (simp add: c_pts_change_multiplicities)
  also have "zmset (map snd (filter (\<lambda>(l', _, _). Loc 2 (Trg 1) = l')
                  (extract_prog Enum.enum (nxt sg) os)))
           = zmset (map (\<lambda>(p, t, m). (t, m))
                      (filter (\<lambda>(p, _, _). p = 1) (produ (os 1))))
           - zmset (map (\<lambda>(p, t, m). (t, m))
                      (filter (\<lambda>(p, _, _). p = 1) (consu (os 2))))"
    using nt_1_1 nt_1_0 nt_2_0 nt_2_1 nt_0_0 nt_0_1
    unfolding Nxt[symmetric]
    by (rule extract_prog_at_loc_2_trg_1)
  finally show ?thesis by simp
qed


lemma dataplane_tracker_inv_buffer_balance:
  fixes os :: "3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state"
    and cbufs :: "3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf"
    and sg :: "(3, 2, (nat, nat) myprod) subgraph"
  assumes D: "dataplane_tracker_inv os cbufs sg"
    and conn_eq: "(outputs_at_target (summ sg) os >> cbufs) (2, 1)
                  = outpu (os 1) 1 @ cbufs (2, 1)"
  shows "to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))
       = c_pts (change_multiplicities (summ sg) 
                  (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))"
proof -
  from D obtain caps where
    Trg: "Trg_caps_inv caps (outputs_at_target (summ sg) os >> cbufs)" and
    cp: "c_pts_inv (change_multiplicities (summ sg)
            (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) caps"
    unfolding dataplane_tracker_inv_def by blast
  have caps_eq:
    "caps (Loc 2 (Trg 1)) = to_zmset (map snd ((outputs_at_target (summ sg) os >> cbufs) (2, 1)))"
    using Trg unfolding Trg_caps_inv_def by blast
  have caps_simp:
    "caps (Loc 2 (Trg 1)) = to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))"
    using caps_eq conn_eq by (simp add: to_zmset_append)
  have c_pts_eq:
    "c_pts (change_multiplicities (summ sg)
              (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))
     = caps (Loc 2 (Trg 1))"
    using cp unfolding c_pts_inv_def by simp
  show ?thesis
    using caps_simp c_pts_eq by simp
qed



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

(* TODO: Move. *)



end
