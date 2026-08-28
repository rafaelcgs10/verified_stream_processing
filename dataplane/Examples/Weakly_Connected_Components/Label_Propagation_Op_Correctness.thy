theory Label_Propagation_Op_Correctness

imports
  Dataplane_Inv
  Labels
begin

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del] 
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]
declare if_cong[cong]
declare list_emb_Nil2[simp del] BULK_BENQ_right_empty[simp del] BULK_BENQ_left_empty[simp del]
  filter_True[simp del] filter_False[simp del]
declare cin.rep_eq[simp del]
declare cin.rep_eq[symmetric, simp]

lemma produces_singleton:
  \<open>produces os [(x, cap)] = os\<lparr>outpu := (outpu os)(out cap := outpu os (out cap) @ [(x, capability.time cap)]),
    produ := produ os @ [(out cap, capability.time cap, 1)]\<rparr>\<close>
  by (auto simp: produces_def fun_eq_iff)
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
    \<open>\<forall>(d, _) \<in> set (outpu (os 2) 1 @ input (os 2) 1 @ cbufs (2, 1)). is_en1 os_label_prop d\<close>
    and buffers_inv:
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    \<open>cbufs (0, 0) = []\<close>
    and dataplane_inv:
    \<open>dataplane_tracker_inv os cbufs sg\<close>
    and csets_inv:
    \<open>SP = cimage
      (\<lambda>t. ((1, 0), (Inr (ccs
        (set (icoll (map (\<lambda>(x, t'). Data t' (projl x)) (chns (1, 0)) @@- lxs) t)
        \<union> all_edges os_label_prop (myfst t))), t)))
      (cUn (cUn (ts lxs) (cset_from_list (map snd (chns (1, 0))))) ((\<lambda> t. MyPair t 0) |`| (cfilter (\<lambda> t. t \<in> myfst ` set (ocaps (os 1) 0)) (cset_from_list (timestamps os_label_prop)))))\<close>
    \<open>SO = cset_from_list (map (\<lambda>x. ((1, 0), x)) (outpu (os 1) 0))\<close>
    and input_stream_inv:
    \<open>timely_input_stream lxs (mset (ocaps (os 0) 0))\<close>
    and label_prop_inv:
    \<open>(\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t))\<close>
    \<open>(\<forall> t \<in> set (timestamps os_label_prop). \<not> frontier_less_equal (exit_scope myfst (front (os 1) 0 + front (os 1) 1)) t \<longrightarrow> labels_stable (all_edges os_label_prop t) (min_label os_label_prop t))\<close>
    \<open>\<forall> t \<in> myfst ` snd ` set (input (os 1) 0) \<union> myfst ` snd ` set (input (os 1) 1). frontier_less_equal (exit_scope myfst (front (os 1) 1)) t\<close>
    \<open>\<forall>t \<in> event.time ` lset lxs \<union> snd ` set (chns (1, 0)) \<union> set (ocaps (os 1) 0). mysnd t = 0\<close>
    \<open>label_prop_upd_inv os_label_prop\<close>
    \<open>input_ocaps_inv (os 1)\<close>
    \<open>wf_label_prop_updates os_label_prop (set (chns (1, 1) @ map (\<lambda>(d, t). (d, t + MyPair 0 1)) (chns (2, 1))))\<close>
    \<open>label_prop_covered_inv os_label_prop (set (chns (1, 1) @ chns (2, 1)))\<close>
  shows \<open>set_op S D (dataflow_op sg (G_op os_input os_label_prop (os 2) cbufs))
         \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms
proof (coinduction arbitrary: S SO SP D lxs os os_input os_label_prop cbufs chns sg T G V L
    rule: weakBisimWeakUptoBisimCong)
  case SIM1
  note subgraph_inv = SIM1(1,2)
    and os_inv = SIM1(3-12)
    and buffers_inv = SIM1(13,14)
    and dataplane_inv = SIM1(15)
    and csets_inv = SIM1(16,17)
    and input_stream_inv = SIM1(18)
    and label_prop_inv = SIM1(19-)

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
        using os_inv(4,10) apply (simp add: BENQ_def operator_state.defs(3))
        using buffers_inv(2) apply (simp add: BENQ_def)
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
        using label_prop_inv(7) apply (simp add: os_inv(4,7) buffers_inv BULK_BENQ_def BENQ_def outputs_at_target_raw_summary subgraph_inv(1) image_Un operator_state.defs(3) Un_assoc)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3))
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply blast
          done
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
        using os_inv(4,10) apply (simp add: BTL_def operator_state.defs(3))
        using buffers_inv(2) apply (simp add: BTL_def)
        apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (1, p))\<close>])

        apply (simp add: BHD_def)
        subgoal
          apply (subgoal_tac "MyPair (myfst t) 0 \<in> snd ` set (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0))")
          subgoal
            apply (simp add: csets_inv(1) buffers_inv os_inv(4,7) operator_state.defs(3) consumes_def)
            apply (subgoal_tac "raw_summary (Loc (1 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Src (0 :: 2))) = [0]")
            subgoal
              apply simp
              apply (rule cimage_cong)
              subgoal
                by auto
              subgoal
                by auto
              done
            subgoal
              unfolding raw_summary_def
                zero_myprod_def by force
            done
          subgoal
            using label_prop_inv(4)[unfolded buffers_inv] apply -
            unfolding BULK_BENQ_def inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary BHD_def
            apply clarsimp
            apply (metis (no_types, lifting) Un_iff hd_in_set img_snd myprod.exhaust_sel)
            done
          done
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
        using label_prop_inv(7) apply (simp add: os_inv(4,7) operator_state.defs(3) buffers_inv)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def BENQ_def BTL_def BHD_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3) consumes_def add_caps_def)
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply blast
          done
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
          using os_inv(4,10) apply (simp add: operator_state.defs(3))
          using buffers_inv(1) apply fast
          using buffers_inv(2) apply simp
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
          using label_prop_inv(7) apply (simp add: os_inv(4) buffers_inv)
          subgoal
            using label_prop_inv(8)
            apply (simp only: fun_upd_triv)
            by (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3))
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
          apply (rule exI[of _ \<open>os(0 := produces (os 0) [(en1 os_input (v, w), Cap t 0)])\<close>])
          apply (rule exI[of _ os_input'])
          apply (rule exI)
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ \<open>BENQ (1, 0) (en1 os_input (v, w), t) chns\<close>])
          apply (intro exI conjI)
          defer
          apply (rule refl)
          apply (rule subgraph_inv(1))
          apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: produces_singleton operator_state.defs(3))
          using os_inv(2) apply (simp add: produces_singleton)
          using os_inv(3) apply (simp add: produces_singleton)
          using os_inv(4) apply simp
          using os_inv(1,5) apply (simp add: produces_singleton ty1_check_def operator_state.defs(3))
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: produces_singleton)

          using os_inv(8) apply simp
          using os_inv(9) apply simp
          using os_inv(4,10) apply (simp add: operator_state.defs(3))                    apply (simp add: buffers_inv BENQ_def BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def fun_eq_iff produces_singleton)
          using buffers_inv(2) apply simp
          apply (rule dataplane_tracker_inv_produce_singleton[OF D G subgraph_inv(2) dataplane_inv, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: timely_input_stream_def os_inv(1) operator_state.defs(3))
          apply (rule refl)
          apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3))
          apply (simp add: csets_inv(2))
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) produces_singleton)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BENQ_def)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          using label_prop_inv(7) apply (simp add: os_inv(4) BENQ_def)
          subgoal
            using label_prop_inv(8)
            by (simp add: BENQ_def os_inv(4))
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
          apply (rule exI[of _ \<open>os(0 := drop_caps (os 0) [Cap t 0])\<close>])
          apply (rule exI[of _ os_input'])
          apply (intro exI conjI)
          defer
          apply (rule refl)
          apply (rule subgraph_inv(1))
          apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: drop_caps_singleton operator_state.defs(3))
          using os_inv(2) apply (simp add: drop_caps_singleton)
          using os_inv(3) apply (simp add: drop_caps_singleton)
          using os_inv(4) apply simp
          using os_inv(5) apply (simp add: drop_caps_singleton ty1_check_def)
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: drop_caps_singleton)
          using os_inv(8) apply simp
          using os_inv(9) apply simp
          using os_inv(4,10) apply simp                    apply (simp add: buffers_inv)
          using buffers_inv(2) apply simp
          apply (rule dataplane_tracker_inv_drop_cap[OF D G subgraph_inv(2) dataplane_inv, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: timely_input_stream_def os_inv(1) operator_state.defs(3))
          apply (rule refl)
          apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
          apply (subst (1 2) icoll_lshift)
          using timely_input_stream_expires_le input_stream_inv apply blast
          using timely_input_stream_expires_le input_stream_inv apply blast
          apply simp
          apply (simp add: csets_inv(2))
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) drop_caps_singleton)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          using label_prop_inv(7) apply (simp add: os_inv(4) buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def)
          subgoal
            using label_prop_inv(8)
            by (simp add: BENQ_def os_inv(4) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
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
          apply (rule exI[of _ \<open>os(0 := add_caps (os 0) [Cap t 0])\<close>])
          apply (rule exI[of _ os_input'])
          apply (intro exI conjI)
          defer
          apply (rule refl)
          apply (rule subgraph_inv(1))
          apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: add_caps_singleton operator_state.defs(3))
          using os_inv(2) apply (simp add: add_caps_singleton)
          using os_inv(3) apply (simp add: add_caps_singleton)
          using os_inv(4) apply simp
          using os_inv(5) apply (simp add: add_caps_singleton ty1_check_def)
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: add_caps_singleton)
          using os_inv(8) apply simp
          using os_inv(9) apply simp
          using os_inv(4,10) apply simp                    apply (simp add: buffers_inv)
          using buffers_inv(2) apply simp
          apply (rule dataplane_tracker_inv_add_cap[OF D dataplane_inv G, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) timely_input_stream_def)
          apply (rule refl)
          apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
          apply (subst (1 2) icoll_lshift)
          using timely_input_stream_expires_le input_stream_inv apply blast
          using timely_input_stream_expires_le input_stream_inv apply blast
          apply (simp add: add_caps_singleton)
          apply (simp add: csets_inv(2))
          using input_stream_inv apply (force simp add: os_inv(1) operator_state.defs(3) add_caps_singleton)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def add_caps_singleton)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          using label_prop_inv(7) apply (simp add: os_inv(4) buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def)
          subgoal
            using label_prop_inv(8)
            by (simp add: BENQ_def os_inv(4) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
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
        using os_inv(6,10) apply (simp add: label_prob_ty2_check_def)
        using buffers_inv(2) apply (simp add: BENQ_def)
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
        apply (subst wf_label_prop_updates_cong[where os'=os_label_prop
              and S'=\<open>set (chns (1, 1) @ map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))\<close>])
        using label_prop_inv(7) apply (auto simp add: os_inv(4) operator_state.defs(3) buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def BENQ_def inputs_at_target_def image_Un)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3))
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply blast
          done
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
        using os_inv(10) apply (simp add: BHD_def BTL_def split_beta )
        apply (metis Un_iff in_hd_or_tl_conv)
        using buffers_inv(2) apply (simp add: BTL_def)
        apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (2, 1))\<close>])
        apply (simp add: BHD_def)
        using input_stream_inv apply simp
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) apply (simp add: os_inv(4,7) operator_state.defs(3) consumes_def)
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def)
        apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7)
        apply (subst wf_label_prop_updates_cong[OF refl refl refl refl _])
        defer
        apply assumption
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def BHD_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3))
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply (metis list.collapse set_ConsD)
          done
        apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def BHD_def image_set map_consI(2) flip: set_append)
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
                      apply (subgoal_tac "ocaps os_label_prop 0 = ocaps (os 1) 0")
                      subgoal
                        apply (cases "frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)")
                        subgoal
                          apply (clarsimp del: disjCI simp add: cimage_iff inputs_at_target_def cUn_assoc cimage_cUn)
                          apply (elim disjE; (clarsimp del: disjCI)?; (elim disjE)?; (clarsimp del: disjCI)?; hypsubst_thin?)
                          subgoal for t'
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule cBexI[of _ "myfst  t'"])
                            apply (simp_all add: image_iff)
                            apply (rule bexI[of _ " t'"])
                            apply (simp_all add: filter_True comp_def drop_caps_def image_iff)
                            done
                          done
                        subgoal
                          apply (clarsimp del: disjCI simp add: cimage_iff inputs_at_target_def cUn_assoc cimage_cUn)
                          apply (elim disjE; (clarsimp del: disjCI)?; (elim disjE)?; (clarsimp del: disjCI)?; hypsubst_thin?)
                          subgoal for  t'
                            apply (rule disjI2)
                            apply (rule disjI1)
                            apply (rule cBexI[of _ "(_, Cap (MyPair (myfst  t') 0) 0)"])
                            apply simp_all
                            unfolding label_prop_output_batch_def
                            apply (simp add: image_iff)
                            apply (rule exI[of _  t'])
                            apply (simp add: operator_state.defs os_inv(4))
                            apply (subgoal_tac "icoll (llist_of (map (\<lambda>(x, t'). Data t' (projl x)) (input (os 1) 0) @ map (\<lambda>(x, t'). Data t' (projl x)) (cbufs (1, 0)) @ map (\<lambda>(x, t'). Data t' (projl x)) (outpu (os 0) 0))) (MyPair (myfst  t') 0) = []")
                            subgoal
                              apply (subgoal_tac "icoll lxs (MyPair (myfst  t') 0) = []")
                              subgoal
                                apply simp
                                apply (rule sym)
                                apply (rule components_from_labels_correct)
                                subgoal
                                  using label_prop_inv(1)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of "myfst  t'"]
                                  by auto
                                subgoal
                                  using label_prop_inv(2)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of "myfst  t'"] 
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
                          done
                        done
                      subgoal
                        by (simp add: operator_state.defs os_inv(4))
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
                        apply simp
                        apply force
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
                    subgoal  for t'
                      unfolding drop_caps_def
                      apply (clarsimp del: disjCI simp add: filter_True comp_def)
                      apply force
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
          using os_inv(10) apply simp
          using buffers_inv(2) apply simp
          subgoal premises aux
            apply (rule iffD1[OF dataplane_tracker_inv_clean, rotated 1])
            apply (rule dataplane_tracker_inv_produces_drops[OF D, where nid=1 and os=os 
                  and drops = "\<lambda> p. if p = 1
                         then []
                         else filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)"
                  and produs="map (\<lambda> t . (0, MyPair t 0, 1)) (remdups (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))"
                  and oputs="(\<lambda> p. if p = 1 then [] else map (\<lambda>t. (en2 os_label_prop (components_from_labels (all_edges os_label_prop t) (min_label os_label_prop t)), (MyPair t 0)))
                          (remdups (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)))))"])
            apply (rule refl)+
            prefer 8
            subgoal
              apply (intro allI impI conjI)
              apply simp
              subgoal
                apply (rule ext)+
                unfolding produces_def drop_caps_def
                apply auto
                subgoal for x
                  apply (subgoal_tac "x = 0")
                  subgoal
                    apply clarsimp
                    apply (subst (2) filter_True)
                    apply (simp_all add: comp_def)
                    done
                  subgoal
                    by (metis num2_neq(2))
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
          subgoal
            apply (subst wf_label_prop_updates_cong)
            using label_prop_inv(7)
            by (auto simp add: produces_def buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def label_prop_output_batch_def)
          subgoal
            using label_prop_inv(8)
            apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3) produces_def drop_caps_def label_prop_output_batch_def)
            apply (erule label_prop_covered_inv_transportI)
            apply simp_all
            apply blast
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
                  apply (simp  del: filter.simps add:  label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
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
                        apply (subgoal_tac \<open>myfst t \<in> myfst ` set (ocaps (os 1) (0 :: 2))\<close>)
                        prefer 2
                        subgoal
                          apply (subgoal_tac \<open>t \<in> set (ocaps (os 1) (0 :: 2))\<close>)
                          apply force
                          apply (insert label_prop_inv(6) aux(2) os_inv(7))
                          unfolding input_ocaps_inv_def
                          apply (drule spec[where x=\<open>0 :: 2\<close>])
                          apply (drule spec[where x=\<open>0 :: 2\<close>])
                          apply (drule bspec[where x=t])
                          apply (simp add: os_inv(4) operator_state.defs)
                          apply (drule bspec[where x=\<open>MyPair 0 0\<close>])
                          apply (simp add: raw_summary_def)
                          apply (simp add: MyPair_zero_zero_sum2)
                          done
                        apply (simp only: cfilter_cinsert)
                        apply (simp add: release_caps_def drop_caps_def add_caps_def trace_simp
                            list_diff_append_cancel_right)

                        apply (subst (1) all_edges_eq[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                        subgoal 
                          using label_prop_inv(5)[unfolded os_inv(4) operator_state.defs]
                          by (simp add: label_prop_upd_inv_def)
                        subgoal by simp
                        subgoal
                          apply simp
                          apply (rule arg_cong2[where f=cinsert])
                          subgoal
                            apply (simp add: insert_commute ccs_insert_symmetric)
                            apply (subst ccs_insert_swap)
                            by (rule refl)
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
                                apply (subst (2) cfilter_False)
                                subgoal
                                  by (auto simp add: label_prop_edge_batch_def Let_def)
                                subgoal
                                  apply simp
                                  apply (rule cimage_cong)
                                  subgoal
                                    by simp
                                  subgoal for t''
                                    apply (cases "t \<le> t''")
                                    subgoal
                                      apply (subst all_edges_eq_le[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                                      subgoal using label_prop_inv(5)[unfolded os_inv(4) operator_state.defs] by simp                                      subgoal
                                        by (rule myfst_mono, assumption)
                                      subgoal by simp
                                      subgoal
                                        apply (subst insert_commute)
                                        apply (simp add: ccs_insert_symmetric)
                                        done
                                      done
                                    subgoal
                                      apply (subst all_edges_eq_not_le[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                                      subgoal
                                        by (cases t'') (auto simp add: less_eq_myprod_def)
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
                  apply simp
                  apply (rule label_prob_ty2_check_producesI)
                  subgoal
                    using os_inv(4,6) by auto
                  subgoal
                    using os_inv(4,6) aux(1,2,3) apply -
                    unfolding label_prob_ty2_check_def add_caps_def input_tl_def label_prop_edge_batch_def label_prop_edge_record_update_def label_prop_neighbor_batch_def
                    by (auto 0 0 simp add: os_inv(1,4) image_iff operator_state.defs produces_def release_caps_def drop_caps_def)
                  subgoal
                    using os_inv(4,6) aux(1,2,3) apply -
                    unfolding label_prob_ty2_check_def add_caps_def input_tl_def label_prop_edge_batch_def label_prop_edge_record_update_def label_prop_neighbor_batch_def
                    by (auto 0 0 simp add: os_inv(1,4) image_iff operator_state.defs produces_def release_caps_def drop_caps_def)
                  done
                subgoal premises aux
                  unfolding add_caps_def
                  using os_inv(7) by auto
                using os_inv(8) apply simp
                using os_inv(9) apply simp
                using os_inv(10) apply simp
                using buffers_inv(2) apply simp
                subgoal premises aux
                  apply (rule dataplane_tracker_inv_release_caps_update[OF D])
                  apply (rule dataplane_tracker_inv_add_produce_drop_caps[OF D])
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
                    by (smt (verit) Operator_State.intsum_add_caps array_rules(3,4) graph_summar_nt_intsum_cong intsum_drop_caps intsum_input_tl
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
                  using label_prop_inv(7)
                  by (auto intro: wf_label_prop_updates_subset simp add: buffers_inv BULK_BENQ_def inputs_at_target_def operator_state.defs os_inv(4) input_tl_def release_caps_def drop_caps_def produces_def)
                subgoal premises aux
                  apply simp
                  apply (rule input_ocaps_inv_release_capsI)
                  apply (rule input_ocaps_inv_drop_produces_add_capsI)
                  using label_prop_inv(6) input_ocaps_inv_input_tlI apply fast
                  done
                subgoal
                  apply (subst wf_label_prop_updates_Un[where S=\<open>set (chns (1, 1) @ map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))\<close>
                        and S'=\<open>set (map (\<lambda>(d, cap :: (2, (nat, nat) myprod) capability). (d, capability.time cap + MyPair 0 1)) (label_prop_edge_batch os_label_prop
             (label_prop_edge_record_update (os_label_prop\<lparr>input := (input os_label_prop)(0 := xs)\<rparr>) (myfst t) v1 v2 l1 l2) (myfst t) l1 l2 t))\<close>])
                  apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def input_tl_def image_Un flip: set_filter)
                  apply (subst filter_True)
                  apply (simp add: label_prop_edge_batch_def label_prop_neighbor_batch_def)
                  apply fastforce
                  apply fast
                  apply (rule conjI)
                  apply (rule wf_label_prop_updates_os_mono[OF label_prop_inv(7) _ _ _ refl])
                  apply simp
                  apply (clarsimp simp add: label_prop_edge_record_update_def)
                  apply (intro allI conjI)
                  apply (clarsimp simp add: label_prop_edge_record_update_def)
                  apply (force simp add: produces_def label_prop_edge_record_update_def)
                  apply simp
                  apply (clarsimp del: disjCI simp add: wf_label_prop_updates_def)
                  subgoal for d' cap
                    apply (intro conjI allI)
                    apply (clarsimp del: disjCI simp add: image_iff set_neighbors label_prop_neighbor_batch_def label_prop_edge_batch_def add_caps_def label_prop_edge_record_update_def)
                    apply fastforce
                    apply (rule label_prop_edge_batch_all_vertices[OF _ refl _ _ _ _ refl refl, of _ os_label_prop \<open>myfst t\<close> _ _ l1 l2 d' cap])
                    apply (simp add: input_tl_def label_prop_edge_record_update_def)
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    subgoal
                      apply (rule label_prop_upd_inv_input0_preserved)
                      apply (rule label_prop_inv(5))
                      apply (simp_all add: operator_state.defs os_inv(4))
                      unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                      using label_prop_inv(7)
                      by (auto intro: wf_label_prop_updates_subset simp add: buffers_inv BULK_BENQ_def inputs_at_target_def operator_state.defs os_inv(4) input_tl_def release_caps_def drop_caps_def produces_def)
                    apply (simp add: input_tl_def)
                    apply (force split: if_split_asm)
                    apply (rule impI)
                    apply (rule label_prop_edge_batch_cc_of_all_edges[OF refl refl])
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    subgoal
                      apply (rule label_prop_upd_inv_input0_preserved)
                      apply (rule label_prop_inv(5))
                      apply (simp_all add: operator_state.defs os_inv(4))
                      unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                      using label_prop_inv(7)
                      by (auto intro: wf_label_prop_updates_subset simp add: buffers_inv BULK_BENQ_def inputs_at_target_def operator_state.defs os_inv(4) input_tl_def release_caps_def drop_caps_def produces_def)
                    apply (simp add: input_tl_def)
                    apply assumption
                    apply simp
                    apply (erule sym)
                    apply (rule label_prop_inv(1))
                    apply (rule label_prop_inv(5))
                    done
                  done
                subgoal
                  apply (simp only: label_prop_covered_inv_release_caps label_prop_covered_inv_drop_caps
                      label_prop_covered_inv_produces label_prop_covered_inv_add_caps)
                  apply (rule label_prop_covered_inv_edge_batch_updateI[where et=t])
                  apply (rule label_prop_inv(8))
                  apply (simp add: label_prop_edge_record_update_def input_tl_def)
                  apply (simp add: label_prop_edge_record_update_def input_tl_def)
                  apply (simp add: label_prop_edge_record_update_def input_tl_def)
                  apply (simp add: label_prop_edge_record_update_def input_tl_def)
                  apply (rule label_prop_inv(5))
                  apply (simp add: os_inv(4) operator_state.defs)
                  apply (erule sym)
                  apply (rule refl)
                  subgoal for y
                    by (force simp add: buffers_inv BULK_BENQ_def inputs_at_target_def outputs_at_target_raw_summary subgraph_inv(1) image_iff split_beta os_inv(4) operator_state.defs input_tl_def produces_def add_caps_def drop_caps_def release_caps_def Let_def)
                  subgoal for d' tm
                    by (force simp add: buffers_inv BULK_BENQ_def inputs_at_target_def outputs_at_target_raw_summary subgraph_inv(1) image_iff split_beta os_inv(4) operator_state.defs input_tl_def produces_def add_caps_def drop_caps_def release_caps_def Let_def)
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
                               (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t)))
                           (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t))
                         (map snd (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t)))
                       1)"])
                apply (rule exI[of _ "release_caps
                       (drop_caps
                         (produces
                           (add_caps (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l))
                             (map snd
                               (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t)))
                           (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t))
                         (map snd (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t)))
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
                        apply (subst (2) cfilter_False)
                        subgoal
                          unfolding label_prop_label_batch_def label_prop_neighbor_batch_def
                          by auto
                        subgoal
                          apply simp
                          apply (rule cimage_cong)
                          subgoal
                            unfolding input_tl_def
                            by (simp add: release_caps_def drop_caps_def produces_def add_caps_def)
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
                using os_inv(10) apply simp
                using buffers_inv(2) apply simp
                subgoal
                  apply (rule dataplane_tracker_inv_release_caps_update[OF D])
                  apply (rule dataplane_tracker_inv_add_produce_drop_caps[OF D])
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
                    by (smt (verit, best) Operator_State.intsum_add_caps fun_upd_other fun_upd_same graph_summar_nt_intsum_cong intsum_drop_caps intsum_input_tl intsum_produces)
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
                    apply (rule wf_label_prop_updates_subset[OF label_prop_inv(7)])
                    apply (fastforce simp add: buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs(3))
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
                  using label_prop_inv(7) apply (auto intro: wf_label_prop_updates_subset simp add:  buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs(3))
                  done
                subgoal
                  apply simp
                  apply (rule input_ocaps_inv_release_capsI)
                  apply (rule input_ocaps_inv_drop_produces_add_capsI)
                  apply (rule input_ocaps_inv_input_tlI)
                  using label_prop_inv(6) apply -
                  apply (simp add: os_inv(4) operator_state.defs)
                  done
                subgoal
                  apply (subst wf_label_prop_updates_Un[where S=\<open>set (tl (input (os 1) 1)) \<union> set (cbufs (1, 1)) \<union> set (outpu (os 2) 1) \<union> set (map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))\<close>
                        and S'=\<open>set (map (\<lambda>(d, cap :: (2, (nat, nat) myprod) capability). (d, capability.time cap + MyPair 0 1)) (label_prop_label_batch os_label_prop
                     (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t))\<close>])
                  apply (simp add: os_inv(4) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def input_tl_def image_Un flip: set_filter)
                  apply (subst filter_True)
                  apply (simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
                  apply (simp add: image_image split_beta Un_assoc)
                  apply (rule conjI)
                  apply (rule wf_label_prop_updates_subset[where S=\<open>set (chns (1, 1) @ map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))\<close>])
                  apply (rule wf_label_prop_updates_os_mono[OF label_prop_inv(7) _ _ _ refl])
                  apply simp
                  apply simp
                  apply (intro allI conjI)
                  apply simp
                  apply (simp add: produces_def)
                  apply (simp add: os_inv(4) operator_state.defs(3) buffers_inv BULK_BENQ_def inputs_at_target_def outputs_at_target_raw_summary subgraph_inv(1))
                  apply blast
                  apply (clarsimp simp add: wf_label_prop_updates_def)
                  subgoal for d' cap
                    apply (intro conjI allI)
                    apply (rule label_prop_label_batch_in_timestamps[of d' cap os_label_prop _ \<open>myfst t\<close> v \<open>(min (min_label os_label_prop (myfst t) v) l)\<close> t])
                    apply blast
                    apply (rule label_prop_label_batch_all_vertices[OF refl refl, of \<open>input_tl os_label_prop 1\<close> d' cap \<open>myfst t\<close> v _ \<open>(min (min_label os_label_prop (myfst t) v) l)\<close> t])
                    apply (simp add: os_inv(4) operator_state.defs(3))
                    apply (simp add: os_inv(4) operator_state.defs(3))
                    using label_prop_inv(5) apply (simp add: input_tl_def label_prop_upd_inv_def)
                    apply (simp add: label_prop_label_batch_def label_prop_neighbor_batch_def input_tl_def neighbors_def)
                    apply (rule refl)
                    apply simp
                    apply (rule impI)
                    apply (rule label_prop_label_batch_cc_of_all_edges[OF refl refl])
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    apply (rule label_prop_inv(5))
                    apply blast
                    apply assumption
                    apply simp
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
                        apply (rule wf_label_prop_updates_subset[OF label_prop_inv(7)])
                        apply (fastforce simp add: buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs(3))
                        done
                      done
                    apply (rule refl)
                    apply simp
                    apply (insert label_prop_inv(7))
                    apply (drule wf_label_prop_updates_subset[where S'=\<open>set (input os_label_prop 1)\<close>])
                    apply (force simp add: buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs(3))
                    apply (unfold wf_label_prop_updates_def)
                    apply (drule bspec[of _ _ \<open>(d, t)\<close>])
                    apply simp
                    apply (simp add: edge_vertices_all_edges[OF label_prop_inv(5)])
                    done
                  done
                subgoal
                  apply (subgoal_tac "d = Inl (v, l)")
                  prefer 2
                  subgoal
                    apply (rule isl_projl_eq)
                    using os_inv(6)[unfolded label_prob_ty2_check_def, THEN conjunct1, rule_format, of _ 1] apply (fastforce simp add: os_inv(4) operator_state.defs)
                    apply (simp add: os_inv(4) operator_state.defs)
                    done
                  apply (simp only: label_prop_covered_inv_release_caps label_prop_covered_inv_drop_caps
                      label_prop_covered_inv_produces label_prop_covered_inv_add_caps)
                  apply (rule label_prop_covered_inv_label_batch_updateI[where et=t and lh=l])
                  apply (rule label_prop_inv(8))
                  apply (simp add: input_tl_def)
                  apply (simp add: input_tl_def)
                  apply (simp add: input_tl_def)
                  apply (simp add: input_tl_def)
                  apply (rule label_prop_inv(5))
                  apply (simp add: os_inv(4) operator_state.defs)
                  apply (rule refl)
                  apply (rule refl)
                  subgoal for x
                    by (force simp add: buffers_inv BULK_BENQ_def inputs_at_target_def outputs_at_target_raw_summary subgraph_inv(1) image_iff split_beta os_inv(4) operator_state.defs input_tl_def produces_def add_caps_def drop_caps_def release_caps_def Let_def)
                  subgoal for x tm
                    by (force simp add: buffers_inv BULK_BENQ_def inputs_at_target_def outputs_at_target_raw_summary subgraph_inv(1) image_iff split_beta os_inv(4) operator_state.defs input_tl_def produces_def add_caps_def drop_caps_def release_caps_def Let_def)
                  subgoal
                    using label_prop_inv(7)[unfolded wf_label_prop_updates_def]
                    by (fastforce simp add: buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs)                  done
                done
              done
            done
          done
        subgoal
          apply (clarsimp split: list.splits)
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
          apply (rule exI[of _ \<open>os(1 := release_caps (os 1) 1)\<close>])
          apply (rule exI[of _ \<open>release_caps os_label_prop 1\<close>])
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ sg])
          apply (intro conjI)
          apply (simp add: dataflow_tree_to_operator_def os_inv(1))
          apply (simp add: csets_inv buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def release_caps_def drop_caps_def cimage_cUn)
          apply (rule subgraph_inv(1))
          apply (rule subgraph_inv(2))
          using os_inv(2) apply simp
          using os_inv(3) apply simp
          using os_inv(4) apply (simp add: release_caps_def drop_caps_def operator_state.defs)
          using os_inv(1,5) apply (simp add: release_caps_def drop_caps_def)
          using os_inv(6) apply simp
          using os_inv(7) apply (simp add: release_caps_def drop_caps_def)

          using os_inv(8) apply (simp add: input_ocaps_inv_def release_caps_def drop_caps_def)
          using os_inv(9) apply simp
          using os_inv(10) apply force
          using buffers_inv(2) apply simp
          subgoal
            apply (rule dataplane_tracker_inv_release_caps_update[where nid=1 and os'=\<open>os 1\<close> and p=1, OF D])
            using dataplane_inv apply simp
            using G subgraph_inv(2) apply simp
            apply (rule subgraph_inv(2))
            done


          using input_stream_inv apply simp
          using label_prop_inv(1) apply simp
          using label_prop_inv(2) apply (simp add: release_caps_def drop_caps_def)
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def release_caps_def drop_caps_def)
          using label_prop_inv(5) apply simp
          apply simp
          apply (rule input_ocaps_inv_release_capsI)
          using label_prop_inv(6) os_inv(4) apply (simp add: operator_state.defs)
          using label_prop_inv(7) apply (simp add: buffers_inv image_Un Un_assoc BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def release_caps_def drop_caps_def)
          subgoal
            using label_prop_inv(8)
            apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3) release_caps_def drop_caps_def Let_def)
            apply (erule label_prop_covered_inv_transportI)
            apply simp_all
            apply blast
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
        using os_inv(10) apply force
        using buffers_inv(2) apply simp
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
          apply (intro impI conjI; clarsimp?)
          subgoal 
            by (clarsimp dest!: num2_neq(2) simp add: filter_True filter_False comp_def)
          subgoal
            by (clarsimp simp add: filter_True filter_False)
          done
        using input_stream_inv apply simp
        apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
        apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv image_Un Un_assoc BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def filter_True split_beta)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3) produces_def drop_caps_def image_Un split_beta)
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply (elim disjE)
          apply blast
          apply blast
          apply blast
          apply (force simp add: image_iff)
          apply blast
          apply blast
          done
        done
      subgoal for _ d t
        apply (simp add: ran_loop_wire cUNIV_def cin_def)
        apply hypsubst_thin
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
        apply (rule exI[of _ \<open>os(1 := consumes (os 1) 1 t d)\<close>])
        apply (rule exI[of _ \<open>consumes os_label_prop 1 t d\<close>])
        apply (rule exI[of _ \<open>BTL (1, 1) cbufs\<close>])
        apply (rule exI[of _ sg])
        apply (intro conjI)
        apply (clarsimp simp add: dataflow_tree_to_operator_def
            intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>]
            arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule comp_op_buf_cong[OF refl])
        using os_inv(1) apply simp
        apply (rule loop_op_buf_cong[OF refl])
        apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule comp_op_buf_cong[OF refl refl refl])
        apply (simp add: ran_comp_wire BTL_def)
        apply (simp add: ran_loop_wire BTL_def map_tl)
        apply (simp add: BTL_def ran_def split: sum.splits)
        apply (metis prod.exhaust sum.exhaust)
        apply (simp add: csets_inv buffers_inv BULK_BENQ_def BENQ_def BTL_def)
        apply (subgoal_tac \<open>timestamps (consumes os_label_prop 1 t d) = timestamps os_label_prop\<close>)
        apply (simp add: cimage_cUn)
        apply (simp add: consumes_def add_caps_def os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
        apply simp
        apply (rule subgraph_inv(1))
        apply (rule subgraph_inv(2))
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply (simp add: consumes_def add_caps_def operator_state.defs(3))
        using os_inv(1,5) apply (simp add: ty1_check_def BTL_def)
        using os_inv(1,4-6)
        apply (simp add: ty1_check_def label_prob_ty2_check_def operator_state.defs(3) BTL_def BHD_def)
        apply (erule conjE)
        apply (rotate_tac 5)
        apply (drule spec[of _ 1])
        apply (simp add: Ball_def)
        apply (meson img_fst in_fst_imageE in_set_tlD)
        using os_inv(7) apply simp
        using os_inv(8) apply simp
        using os_inv(9) apply simp
        using os_inv(10) apply (simp add: BTL_def)
        using buffers_inv(2) apply (simp add: BTL_def)
        apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (1, 1))\<close>])
        apply (simp add: BHD_def)
        using input_stream_inv apply simp
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) unfolding min_label_def apply (simp add: consumes_def all_edges_def all_vertices_def neighbors_def)
        subgoal
          using dataplane_inv unfolding dataplane_tracker_inv_def
          apply (simp add: label_prop_inv(3))
          apply (elim exE conjE)
          subgoal premises prems for caps
            using prems(1,6-8) prems(2)[symmetric] unfolding front_inv_def imp_front_inv_def chnls_imp_front_inv_def
            apply simp
            apply (rule contrapos_pp[OF _ frontier_less_equal_exit_scope, rotated, where t1=t])
            apply simp
            apply (drule spec2[of _ 1 1])
            apply (drule spec[of _ \<open>Loc 1 (Trg 1)\<close>])
            apply (drule spec2[of _ 1 1])
            apply (drule bspec[of _ _ \<open>(d, t)\<close>])
            apply (simp add: BULK_BENQ_def BHD_def)
            apply (rule disjI1)
            apply (metis list.set_sel(1))
            apply (rule frontier_less_equal_le_trans[rotated])
            apply (rule order.trans)
            apply assumption
            apply assumption
            apply simp
            done
          done
        using os_inv(7) label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def BENQ_def BTL_def raw_summary_def)
        subgoal
          apply (insert label_prop_inv(1,5))
          apply (unfold label_prop_upd_inv_def)
          apply (elim conjE)
          apply (intro conjI)
          apply (simp add: consumes_def)
          apply (simp add: consumes_def)
          apply (simp add: consumes_def)
          apply (simp add: consumes_def all_vertices_def)
          apply (simp add: consumes_def)
          apply (simp add: consumes_def)          done
        using inputs_ocaps_inv_consumes[OF label_prop_inv(6)] apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv flip: BULK_BENQ_assoc)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def BHD_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3) consumes_def add_caps_def)
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply (metis list.collapse set_ConsD)
          done
        done
      subgoal for d t xs
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
        apply (rule exI[of _ \<open>os(2 := (os 2)\<lparr>outpu := (outpu (os 2))(1 := xs)\<rparr>)\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ \<open>BENQ (1, 1) (d, t) cbufs\<close>])
        apply (rule exI[of _ sg])
        apply (intro conjI)
        apply (clarsimp simp add: dataflow_tree_to_operator_def
            intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>]
            arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule comp_op_buf_cong[OF refl])
        apply (simp add: os_inv(1))
        apply (rule loop_op_buf_cong[OF refl])
        apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule comp_op_buf_cong[OF refl refl refl])
        apply (simp add: ran_comp_wire BENQ_def)
        apply (simp add: ran_loop_wire)
        apply (clarsimp simp add: BENQ_def ran_def split: sum.splits)
        apply (metis obj_sumE prod.exhaust)
        apply (simp add: csets_inv buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) BENQ_def cimage_cUn)
        apply (rule subgraph_inv(1))
        apply (rule subgraph_inv(2))
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply force
        using os_inv(5) apply (simp add: os_inv(1) ty1_check_def BENQ_def)
        using os_inv(6,10) apply (simp add: label_prob_ty2_check_def BENQ_def)
        using os_inv(7) apply simp
        using os_inv(8) apply (simp add: input_ocaps_inv_def)
        using os_inv(9) apply simp
        using os_inv(6,10) apply (simp add: label_prob_ty2_check_def BENQ_def)
        using buffers_inv(2) apply (simp add: BENQ_def)
        apply (rule dataplane_tracker_inv_update_outputs[OF dataplane_inv _ _ _ _ G, where nid=2 and xs=\<open>[(d, t)]\<close> and ys=xs and p=1])
        apply simp
        apply (simp add: fun_eq_iff)
        apply (simp add: BENQ_def)
        apply (simp add: subgraph_inv(1) raw_summary_def antichain_from_list_singleton)
        using input_stream_inv apply simp
        apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
        apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv BULK_BENQ_def BENQ_def outputs_at_target_raw_summary subgraph_inv(1) image_Un Un_assoc)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def BHD_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3) consumes_def add_caps_def)
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply (metis list.collapse set_ConsD)
          done
        done
      subgoal for _ os_incr'
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
        apply (intro exI conjI)
        apply (simp add: dataflow_tree_to_operator_def os_inv(1))
        apply (simp add: csets_inv BULK_BENQ_def buffers_inv outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def cimage_cUn)
        using subgraph_inv(1) apply simp
        using subgraph_inv(2) apply simp
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply simp
        using os_inv(1,5) apply simp
        apply (rule os_inv(6))
        using os_inv(7) apply (simp add: obtain_progress_def)
        using os_inv(8) apply (simp add: obtain_progress_def input_ocaps_inv_def)
        using os_inv(9) apply (simp add: obtain_progress_def)
        using os_inv(10) apply (simp add: obtain_progress_def)
        using buffers_inv(2) apply simp
        apply (subst dataplane_tracker_inv_clean)
        prefer 2
        apply (rule dataplane_tracker_inv_progress[OF dataplane_inv D G, where nid=2])
        apply (simp add: obtain_progress_def)
        apply (simp add: obtain_progress_def)
        using input_stream_inv apply simp
        apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
        apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def obtain_progress_def image_Un Un_assoc)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3) obtain_progress_def)
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply blast
          done
        done
      subgoal for _ os_label_prop'
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
        apply (rule exI[of _ \<open>os(1 := fst (obtain_progress (os 1)))\<close>])
        apply (rule exI[of _ os_label_prop'])
        apply (rule exI[of _ cbufs])
        apply (intro exI conjI)
        apply (simp add: dataflow_tree_to_operator_def os_inv(1))
        apply (simp add: csets_inv buffers_inv obtain_progress_def BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def cimage_cUn)
        using subgraph_inv(1) apply simp
        using subgraph_inv(2) apply simp
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply (simp add: obtain_progress_def operator_state.defs(3))
        using os_inv(1,5) apply simp
        using os_inv(6) apply (simp add: obtain_progress_def label_prob_ty2_check_def)
        using os_inv(7) apply (simp add: obtain_progress_def)
        using os_inv(8) apply simp
        using os_inv(9) apply simp
        using os_inv(10) apply (simp add: obtain_progress_def)
        using buffers_inv(2) apply simp
        apply (subst dataplane_tracker_inv_clean)
        prefer 2
        apply (rule dataplane_tracker_inv_progress[OF dataplane_inv D G, where nid=1])
        apply (simp add: obtain_progress_def os_inv(4) operator_state.defs(3))
        apply (simp add: obtain_progress_def os_inv(4) operator_state.defs(3))
        using input_stream_inv apply simp
        using label_prop_inv(1) apply (simp add: obtain_progress_def)
        using label_prop_inv(2) apply (simp add: obtain_progress_def)
        using label_prop_inv(3) apply (simp add: obtain_progress_def)
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def obtain_progress_def)
        using label_prop_inv(5) apply (simp add: obtain_progress_def)
        using label_prop_inv(6) apply (simp add: obtain_progress_def input_ocaps_inv_def)
        using label_prop_inv(7) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def obtain_progress_def image_Un Un_assoc)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3) obtain_progress_def)
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply blast
          done
        done
      subgoal
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
        apply (rule exI[of _ \<open>os(0 := fst (obtain_progress (os 0)))\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ cbufs])
        apply (intro exI conjI)
        apply (simp add: dataflow_tree_to_operator_def os_inv(1) operator_state.defs(3) obtain_progress_def)
        apply (simp add: csets_inv buffers_inv)
        using subgraph_inv(1) apply simp
        using subgraph_inv(2) apply simp
        using os_inv(2) apply (simp add: obtain_progress_def)
        using os_inv(3) apply (simp add: obtain_progress_def)
        using os_inv(4) apply simp
        using os_inv(1,5) apply (simp add: obtain_progress_def ty1_check_def operator_state.defs(3))
        apply (rule os_inv(6))
        using os_inv(7) apply (simp add: obtain_progress_def)
        using os_inv(8) apply simp
        using os_inv(9) apply simp
        using os_inv(10) apply simp
        using buffers_inv(2) apply simp
        apply (subst dataplane_tracker_inv_clean)
        prefer 2
        apply (rule dataplane_tracker_inv_progress[OF dataplane_inv D G, where nid=0])
        apply (simp add: obtain_progress_def)
        apply simp
        using input_stream_inv apply (simp add: obtain_progress_def)
        apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv)
        apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3))
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply blast
          done
        done
      subgoal
        apply (insert dataplane_inv subgraph_inv(1))
        apply (unfold dataplane_tracker_inv_def propagation_inv_def)
        apply (elim exE conjE; hypsubst_thin)
        apply (rule FalseE)
        apply (rule propagate_all_terminates[OF D, unfolded not_def, rule_format])
        by (auto simp add: raw_summary_def)
      subgoal for c
        apply (erule thin_rl)
        apply (erule thin_rl)
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
        apply (rule exI[of _ \<open>os(1 := (os 1)\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg p))), initia := True\<rparr>)\<close>])
        apply (rule exI[of _ \<open>os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg p))), initia := True\<rparr>\<close>])
        apply (rule exI[of _ cbufs])
        apply (rule exI[of _ \<open>sg\<lparr>pt_tr := c\<rparr>\<close>])
        apply (intro conjI)
        apply (simp add: dataflow_tree_to_operator_def os_inv(1))
        apply (simp add: csets_inv buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def cimage_cUn)
        using subgraph_inv(1) apply simp
        using subgraph_inv(2) apply simp
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply (simp add: operator_state.defs(3))
        using os_inv(1,5) apply simp
        using os_inv(6) apply (simp add: label_prob_ty2_check_def)
        using os_inv(7) apply simp
        using os_inv(8) apply simp
        using os_inv(9) apply simp
        using os_inv(10) apply simp
        using buffers_inv(2) apply simp
        apply (subst dataplane_tracker_inv_clean[where os'=\<open>os(1 := (os 1)\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg p)))\<rparr>)\<close>])
        apply simp
        apply (rule dataplane_tracker_inv_front_update[OF D _ _ G dataplane_inv])
        apply (simp add: subgraph_inv(1))
        apply assumption
        using input_stream_inv apply simp
        using label_prop_inv(1) apply simp
        subgoal
          apply (intro ballI impI)
          subgoal for t
            apply simp
            apply (rule ccontr)
            using label_prop_inv(8) apply -
            apply (subgoal_tac "\<not> frontier_less_equal (exit_scope myfst (frontier (c_imp c (Loc 1 (Trg 1))))) t")
            prefer 2
            subgoal
              by (metis exit_scope_plus_distrib frontier_less_equal_antichain_plusI2)
            apply (erule not_labels_stable_covered_witnessE)
            apply assumption
            apply assumption
            subgoal for a s t' l'
              apply (subgoal_tac "(Inl (a, l'), MyPair s t') \<in> set ((outputs_at_target (summ sg) os >> cbufs) (1, 1)) \<union> set (input (os 1) 1) \<union> set ((outputs_at_target (summ sg) os >> cbufs) (2, 1)) \<union> set (input (os 2) 1)")
              prefer 2
              subgoal using buffers_inv by (auto simp add: BULK_BENQ_def inputs_at_target_def)
              apply (thin_tac "(Inl (a, l'), MyPair s t') \<in> set (chns (1, 1) @ chns (2, 1))")
              apply (elim UnE)
              subgoal
                apply (drule imageI[where f=snd])
                apply (drule dataplane_tracker_inv_c_imp_frontier_le_chan[OF D _ _ dataplane_inv, rotated 2, where s="0 :: (nat, nat) myprod" and L="Loc (1::3) (Trg (1::2))"])
                apply (rule graph.path_weight_refl)
                apply (rule dataflow_topology.axioms(1)[OF D])
                apply (simp add: subgraph_inv(1))
                apply assumption
                apply (drule frontier_less_equal_exit_scope_myfst_le[where t=t])
                apply simp
                apply blast
                done
              subgoal
                apply (subgoal_tac "MyPair s t' -+- MyPair 0 0 \<in> set (ocaps (os 1) 1)")
                prefer 2
                subgoal using label_prop_inv(6)[unfolded input_ocaps_inv_def] os_inv(7) by (fastforce simp add: raw_summary_def)
                apply (drule dataplane_tracker_inv_c_imp_frontier_le_ocaps[OF D _ _ dataplane_inv, rotated 2, where s="MyPair 0 1" and L="Loc (1::3) (Trg (1::2))"])
                apply (simp add: subgraph_inv(1) in_antichain_singleton)
                apply (simp add: subgraph_inv(1))
                apply assumption
                apply (drule frontier_less_equal_exit_scope_myfst_le[where t=t])
                apply simp
                apply blast
                done
              subgoal
                apply (drule imageI[where f=snd])
                apply (drule dataplane_tracker_inv_c_imp_frontier_le_chan[OF D _ _ dataplane_inv, rotated 2, where s="MyPair 0 1" and L="Loc (1::3) (Trg (1::2))"])
                apply (simp add: subgraph_inv(1) in_antichain_singleton)
                apply (simp add: subgraph_inv(1))
                apply assumption
                apply (drule frontier_less_equal_exit_scope_myfst_le[where t=t])
                apply simp
                apply blast
                done
              subgoal
                apply (subgoal_tac "MyPair s t' -+- MyPair 0 1 \<in> set (ocaps (os 2) 1)")
                prefer 2
                subgoal using os_inv(8)[unfolded input_ocaps_inv_def] os_inv(7) by (fastforce simp add: raw_summary_def)
                apply (drule dataplane_tracker_inv_c_imp_frontier_le_ocaps[OF D _ _ dataplane_inv, rotated 2, where s="0 :: (nat, nat) myprod" and L="Loc (1::3) (Trg (1::2))"])
                apply (simp add: subgraph_inv(1) in_antichain_singleton)
                apply (simp add: subgraph_inv(1))
                apply assumption
                apply (drule frontier_less_equal_exit_scope_myfst_le[where t=t])
                apply simp
                apply blast
                done
              done
            done
          done
        subgoal
          apply (intro ballI)
          apply simp
          apply (elim disjE)
          apply (clarsimp simp add: image_iff)
          subgoal for a b
            apply (drule imageI[where f=snd])
            apply (drule label_prop_inv(6)[unfolded input_ocaps_inv_def, rule_format, where p'=1 and s="MyPair 0 0"])
            apply (simp add: os_inv(7) raw_summary_def)
            apply (drule dataplane_tracker_inv_c_imp_frontier_le_ocaps[OF D _ _ dataplane_inv, rotated 2, where s="MyPair 0 1" and L="Loc (1::3) (Trg (1::2))"])
            apply (simp add: subgraph_inv(1) in_antichain_singleton)
            apply (simp add: subgraph_inv(1))
            apply assumption
            apply (rule frontier_less_equal_exit_scope_myfst_le)
            apply assumption
            apply simp
            done
          apply (clarsimp simp add: image_iff)
          subgoal for a b
            apply (drule imageI[where f=snd])
            apply (drule label_prop_inv(6)[unfolded input_ocaps_inv_def, rule_format, where p'=1 and s="MyPair 0 0"])
            apply (simp add: os_inv(7) raw_summary_def)
            apply (drule dataplane_tracker_inv_c_imp_frontier_le_ocaps[OF D _ _ dataplane_inv, rotated 2, where s="MyPair 0 1" and L="Loc (1::3) (Trg (1::2))"])
            apply (simp add: subgraph_inv(1) in_antichain_singleton)
            apply (simp add: subgraph_inv(1))
            apply assumption
            apply (rule frontier_less_equal_exit_scope_myfst_le)
            apply assumption
            apply simp
            done
          done
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
        using label_prop_inv(5) apply simp
        using label_prop_inv(6) apply (simp add: input_ocaps_inv_def)
        using label_prop_inv(7) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def image_Un Un_assoc)
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3))
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply blast
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
        using os_inv(10) apply simp
        using buffers_inv(2) apply simp
        apply (rule dataplane_tracker_inv_update_outputs_outside[OF dataplane_inv _ _ G])
        apply (simp add: fun_upd_def)
        apply (simp add: subgraph_inv(1) raw_summary_def)
        apply (subgoal_tac \<open>outputs_at_target (summ sg) (os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(0 := xs)\<rparr>)) (1, 0) = outputs_at_target (summ sg) os (1, 0)\<close>)
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
        subgoal
          apply (subst wf_label_prop_updates_cong[where os'=os_label_prop])
          using label_prop_inv(7)
          by (simp_all add: buffers_inv image_Un Un_assoc BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
        subgoal
          using label_prop_inv(8)
          apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3))
          apply (erule label_prop_covered_inv_transportI)
          apply simp_all
          apply blast
          done
        done
      done
  qed
next
  case SIM2
  note subgraph_inv = SIM2(1,2)
    and os_inv = SIM2(3-12)
    and buffers_inv = SIM2(13,14)
    and dataplane_inv = SIM2(15)
    and csets_inv = SIM2(16,17)
    and input_stream_inv = SIM2(18)
    and label_prop_inv = SIM2(19-)

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
  obtain cap where dt_inv:
    \<open>Src_caps_inv cap os\<close>
    \<open>Trg_caps_inv cap (outputs_at_target (summ sg) os >> cbufs)\<close>
    \<open>c_pts_inv
      (change_multiplicities (summ sg)
        (extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress (os 0))) @
         extract_progress 1 (subgraph.nxt sg) (snd (obtain_progress (os 1))) @
         extract_progress 2 (subgraph.nxt sg) (snd (obtain_progress (os 2))))
        (pt_tr sg)) cap\<close>
    \<open>front_inv os (pt_tr sg)\<close>
    \<open>imp_front_inv (summ sg) (pt_tr sg)\<close>
    \<open>chnls_imp_front_inv (summ sg) (pt_tr sg) (outputs_at_target (summ sg) os >> cbufs)\<close>
    \<open>change_deltas_inv os\<close>
    \<open>propagation_inv (summ sg) (pt_tr sg)\<close>
    \<open>extract_prog_changes_above_impl_inv (summ sg) (subgraph.nxt sg) (pt_tr sg) os\<close>
    \<open>produ_consu_inter_supported (subgraph.nxt sg) os (pt_tr sg)\<close>
    using dataplane_inv[unfolded dataplane_tracker_inv_def, simplified]
    by clarsimp
  obtain c' where first_propa:
    \<open>propagate_all (antichain_from_list \<circ>\<circ> raw_summary)
      (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary)
        (extract_progress 0 (graph_to_nxt (antichain_from_list \<circ>\<circ> raw_summary))
          (snd (obtain_progress os_input)))
        (pt_tr sg)) = Some c'\<close>
    \<open>\<forall>loc. frontier (c_imp c' loc) =
      ifrontier (antichain_from_list \<circ>\<circ> raw_summary) (-+-)
        (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary)
          (extract_progress 0 (graph_to_nxt (antichain_from_list \<circ>\<circ> raw_summary))
            (snd (obtain_progress os_input)))
          (pt_tr sg)) loc\<close>
    \<open>dataflow_topology_from_tree.inv_implications_nonneg c'\<close>
    \<open>dataflow_topology_from_tree.inv_imp_plus_work_nonneg c'\<close>
    \<open>dataflow_topology.inv_imps_work_sum (antichain_from_list \<circ>\<circ> raw_summary) (-+-) c'\<close>
    using change_multiplicities_and_propagate_all_correctness
      [OF D, of \<open>pt_tr sg\<close>
        \<open>extract_progress 0 (graph_to_nxt (antichain_from_list \<circ>\<circ> raw_summary))
          (snd (obtain_progress os_input))\<close>,
        unfolded subgraph_inv(1), simplified]
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
      apply (clarsimp simp add: obtain_progress_def subgraph_inv(1,2) set_map_filter
          split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
      subgoal for l t
        using loc_3_2_cases[of l]
        using dt_inv(7)[unfolded change_deltas_inv_def]
        by (fastforce del: disjCI split: option.splits)
      done
    apply (drule meta_mp)
    subgoal
      apply clarsimp
      subgoal for l t m
        apply (subst frontier_less_equal_iff[symmetric])
        apply (rule frontier_less_equal_le_trans[rotated])
        apply (rule dt_inv(5)[unfolded imp_front_inv_def, rule_format, of l])
        apply (rule dt_inv(9)[unfolded extract_prog_changes_above_impl_inv_def
              changes_above_impl_inv_def, simplified, rule_format,
              where xs=Nil and x=\<open>(l, t, m)\<close> and nid=0, simplified])
        apply (clarsimp simp add: obtain_progress_def subgraph_inv(1,2) set_map_filter
            split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
        done
      done
    apply (drule meta_mp)
    subgoal
      using raw_summary_no_self_loop by auto
    by clarsimp

(* ----------------------------- *)
(* STEPS 1: op 0 reports progress *)
  define os_progress where \<open>os_progress = os(0 := op_state_base (fst (obtain_progress os_input)))\<close>

  define sg_progress where \<open>sg_progress = sg\<lparr>
    pt_tr := change_multiplicities (summ sg)
      (extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress os_input)))
      (pt_tr sg)\<rparr>\<close>

  have dataplane_after_input_progress:
    \<open>dataplane_tracker_inv os_progress cbufs sg_progress\<close>
  proof -
    have base_progress:
      \<open>op_state_base (fst (obtain_progress os_input)) = fst (obtain_progress (os 0))\<close>
      using os_inv(1)
      by (simp add: obtain_progress_def op_state_base_def operator_state.defs)
    have progress_st:
      \<open>snd (obtain_progress os_input) = snd (obtain_progress (os 0))\<close>
      using os_inv(1)
      by (simp add: obtain_progress_def operator_state.defs)
    show ?thesis
      unfolding sg_progress_def
      using dataplane_tracker_inv_progress[OF dataplane_inv D G refl]
      by (simp add: os_progress_def base_progress progress_st)
  qed

  define sg_first_propa where \<open>sg_first_propa = sg_progress\<lparr>pt_tr := c'\<rparr>\<close>

  define label_front_after_first_propa where
    \<open>label_front_after_first_propa = frontier \<circ> (\<lambda>p. c_imp (pt_tr sg_first_propa) (Loc (1 :: 3) (Trg p)))\<close>

  define os_first_propa where
    \<open>os_first_propa = os_progress(1 := op_state_base
      (os_label_prop\<lparr>front := label_front_after_first_propa, initia := True\<rparr>))\<close>

  have dataplane_after_first_propa:
    \<open>dataplane_tracker_inv os_first_propa cbufs sg_first_propa\<close>
  proof -
    have base_progress:
      \<open>op_state_base (fst (obtain_progress os_input)) = fst (obtain_progress (os 0))\<close>
      using os_inv(1)
      by (simp add: obtain_progress_def op_state_base_def operator_state.defs)
    have progress_st:
      \<open>snd (obtain_progress os_input) = snd (obtain_progress (os 0))\<close>
      using os_inv(1)
      by (simp add: obtain_progress_def operator_state.defs)
    have G_progress:
      \<open>graph_summar_nt (summ sg_progress) (nxt sg_progress) os_progress\<close>
    proof -
      have \<open>graph_summar_nt (summ sg) (nxt sg) os_progress =
        graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_progress_def os_inv(1) obtain_progress_def op_state_base_def operator_state.defs)
      then show ?thesis
        using G by (simp add: sg_progress_def)
    qed
    have D_progress: \<open>dataflow_topology (summ sg_progress) (-+-)\<close>
      using D by (simp add: sg_progress_def)
    have reachable_progress: \<open>reachable_locations (summ sg_progress) = UNIV\<close>
      using subgraph_inv(1) by (simp add: sg_progress_def)
    have propagate_progress: \<open>propagate_all (summ sg_progress) (pt_tr sg_progress) = Some c'\<close>
      using first_propa(1) subgraph_inv by (simp add: sg_progress_def)
    define front_c where \<open>front_c = frontier \<circ> (\<lambda>p. c_imp c' (Loc (1 :: 3) (Trg p)))\<close>

    have inv_front_no_upfro:
      \<open>dataplane_tracker_inv os_first_propa cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>)\<close>
    proof -
      define os_front where \<open>os_front = map_entry (1 :: 3) (front_update (\<lambda>_. front_c)) os_progress\<close>

      have inv_map:
        \<open>dataplane_tracker_inv os_front cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>)\<close>
        unfolding os_front_def front_c_def
        by (rule dataplane_tracker_inv_front_update
            [OF D_progress reachable_progress propagate_progress G_progress dataplane_after_input_progress,
              where nid = \<open>1 :: 3\<close>, simplified])

      have clean_initia:
        \<open>dataplane_tracker_inv os_first_propa cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>) \<longleftrightarrow>
          dataplane_tracker_inv os_front cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>)\<close>
        by (rule dataplane_tracker_inv_clean)
          (simp_all add: os_first_propa_def os_front_def os_progress_def
            label_front_after_first_propa_def sg_first_propa_def front_c_def
            os_inv(4) op_state_base_def operator_state.defs)
      show ?thesis
        using clean_initia inv_map by simp
    qed
    show ?thesis
      using inv_front_no_upfro by (simp add: sg_first_propa_def)
  qed

(* ----------------------------- *)
(* STEPS 2: op 1 reads the initial frontier from propagation *)
  define os_label_after_first_propa where
    \<open>os_label_after_first_propa = os_label_prop\<lparr>front := label_front_after_first_propa, initia := True\<rparr>\<close>

  have labels_after_first_propa:
    \<open>\<forall>t. labels_inv (all_edges os_label_after_first_propa t) (min_label os_label_after_first_propa t)\<close>
    using label_prop_inv(1)
    by (simp add: os_label_after_first_propa_def all_edges_def all_vertices_def min_label_def)

  define input_events where \<open>input_events = (\<lambda>n. ltaken n lxs)\<close>

  define input_data where
    \<open>input_data = (\<lambda>n. map (\<lambda>ev. case ev of Data t d \<Rightarrow> (Inl d :: _ + nat set set, t))
      (filter is_Data (input_events n)))\<close>

  define os_input_after_stream where
    \<open>os_input_after_stream = (\<lambda>n. (fst (obtain_progress os_input))\<lparr>
      es := (es (fst (obtain_progress os_input)))(0 := ldropn n lxs),
      ocaps := (ocaps (fst (obtain_progress os_input)))(0 :=
        ocaps_updates (ocaps (fst (obtain_progress os_input)) 0) (input_events n)),
      inter := inter (fst (obtain_progress os_input)) @
        map (\<lambda>ev. case ev of Drop t \<Rightarrow> (0, t, -1) | Mint t \<Rightarrow> (0, t, 1))
          (filter (Not \<circ> is_Data) (input_events n)),
      produ := produ (fst (obtain_progress os_input)) @
        map (\<lambda>ev. case ev of Data t d \<Rightarrow> (0, t, 1))
          (filter is_Data (input_events n)),
      outpu := (outpu (fst (obtain_progress os_input)))(0 :=
        outpu (fst (obtain_progress os_input)) 0 @ input_data n)\<rparr>)\<close>

  define os_after_input_stream where
    \<open>os_after_input_stream = (\<lambda>n. os_first_propa(0 := op_state_base (os_input_after_stream n)))\<close>

  have dataplane_after_input_stream:
    \<open>dataplane_tracker_inv (os_after_input_stream n) cbufs sg_first_propa\<close>
    for n
  proof -
    have D_first: \<open>dataflow_topology (summ sg_first_propa) (-+-)\<close>
      using D by (simp add: sg_first_propa_def sg_progress_def)
    have Nxt_first: \<open>nxt sg_first_propa = graph_to_nxt (summ sg_first_propa)\<close>
      using subgraph_inv(2) by (simp add: sg_first_propa_def sg_progress_def)
    have G_first: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_first_propa\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_first_propa =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_first_propa_def os_progress_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs)
      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed

(* ----------------------------- *)
(* STEPS 3: op 0 produces n elements from the input stream *)  
    define xs where \<open>xs = ltaken n lxs\<close>

    define mint_times where \<open>mint_times = map event.time (filter is_Mint xs)\<close>

    define drop_times where \<open>drop_times = map event.time (filter is_Drop xs)\<close>

    define produs where \<open>produs = map (\<lambda>ev. ((0 :: 2), event.time ev, 1 :: int)) (filter is_Data xs)\<close>

    define oputs where \<open>oputs = (\<lambda>_. [])((0 :: 2) := input_data n)\<close>

    define base where \<open>base = os_first_propa 0\<close>

    define os_minted where
      \<open>os_minted = os_first_propa(0 := base\<lparr>
        ocaps := (ocaps base)((0 :: 2) := ocaps base 0 @ mint_times),
        inter := inter base @ map (\<lambda>t. ((0 :: 2), t, 1 :: int)) mint_times\<rparr>)\<close>

    have OSB1[simp]: \<open>\<And> F I. op_state_base (os_label_prop\<lparr>front := F, initia := I\<rparr>) = os 1\<lparr>front := F, initia := I\<rparr>\<close>
      by (simp add: op_state_base_def os_inv(4) operator_state.defs)
    have OSB0[simp]: \<open>op_state_base (fst (obtain_progress os_input)) = fst (obtain_progress (os 0))\<close>
      by (simp add: op_state_base_def obtain_progress_def os_inv(1) operator_state.defs)
    have inv_minted: \<open>dataplane_tracker_inv os_minted cbufs sg_first_propa\<close>
      unfolding os_minted_def base_def
      apply (rule dataplane_tracker_inv_mints_many[OF D_first, simplified,
            where nid=0 and p=0 and xs=mint_times])
      apply (rule dataplane_after_first_propa)
      apply (rule G_first)
      unfolding mint_times_def xs_def
      apply clarsimp
      subgoal for e
        apply (cases e; clarsimp)
        subgoal for t
          apply (drule setltakenD)
          apply (drule Mint_in_Stream_le_Mint_in_C[rotated])
          using input_stream_inv[unfolded timely_input_stream_def] apply blast
          using os_inv(1)
          by (auto simp add: os_first_propa_def os_progress_def
              obtain_progress_def op_state_base_def operator_state.defs)
        done
      done

    have G_minted: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_minted\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_minted =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_first_propa\<close>
        by (rule graph_summar_nt_intsum_cong) (simp add: os_minted_def base_def)
      then show ?thesis
        using G_first by simp
    qed

    define drops where \<open>drops = (\<lambda>_. [])((0 :: 2) := drop_times)\<close>

    define canon_ocaps_port0 where \<open>canon_ocaps_port0 = list_diff (ocaps base 0 @ mint_times) drop_times\<close>

    define canon_ocaps where \<open>canon_ocaps = (ocaps base)((0 :: 2) := canon_ocaps_port0)\<close>

    define canon_output where \<open>canon_output = (outpu base)((0 :: 2) := outpu base 0 @ input_data n)\<close>

    define canon_inter where
      \<open>canon_inter = inter base @ map (\<lambda>t. ((0 :: 2), t, 1 :: int)) mint_times @
        map (\<lambda>t. ((0 :: 2), t, -1 :: int)) drop_times\<close>

    define canon0 where
      \<open>canon0 = base\<lparr>outpu := canon_output, ocaps := canon_ocaps, input := input base,
        produ := produ base @ produs, inter := canon_inter\<rparr>\<close>

    define os_canon where \<open>os_canon = os_first_propa(0 := canon0)\<close>

    have concat_drops:
      \<open>concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int)) (drops p)) Enum.enum) =
        map (\<lambda>t. ((0 :: 2), t, - 1 :: int)) drop_times\<close>
      using concat_map_empty_except_1[OF Enum.enum_distinct Enum.in_enum,
          where x=\<open>0 :: 2\<close> and f=\<open>\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int)) (drops p)\<close>]
      by (auto simp: drops_def)
    have oputs_produs:
      \<open>\<forall>p. to_zmset (map snd (oputs p)) =
        zmset (map snd (filter (\<lambda>x. p = fst x) produs))\<close>
    proof
      fix p :: 2
      show \<open>to_zmset (map snd (oputs p)) =
        zmset (map snd (filter (\<lambda>x. p = fst x) produs))\<close>
      proof (cases \<open>p = 0\<close>)
        case True
        have data_time:
          \<open>map (\<lambda>x. snd (case x of Data t d \<Rightarrow> (Inl d, t))) (filter is_Data xs) =
            map event.time (filter is_Data xs)\<close>
          by (rule map_cong[OF refl]) (auto split: event.splits)
        have lhs_time:
          \<open>to_zmset (map snd (oputs (0 :: 2))) =
            to_zmset (map event.time (filter is_Data xs))\<close>
          apply (simp add: oputs_def input_data_def input_events_def xs_def[symmetric] comp_def)
          apply (rule arg_cong[where f=to_zmset])
          apply (rule data_time)
          done
        have rhs_time:
          \<open>zmset (map snd (filter (\<lambda>x. (0 :: 2) = fst x) produs)) =
            to_zmset (map event.time (filter is_Data xs))\<close>
          by (simp add: produs_def filter_True comp_def zmset_map_one)
        show ?thesis
          using True lhs_time rhs_time by simp
      next
        case False
        then show ?thesis
          by (simp add: oputs_def produs_def filter_False)
      qed
    qed

    have inv_canon_step:
      \<open>dataplane_tracker_inv
        (os_minted(0 := (os_minted 0)\<lparr>outpu := canon_output,
          ocaps := canon_ocaps, input := input base,
          produ := produ base @ produs, inter := canon_inter\<rparr>))
        cbufs sg_first_propa\<close>
      apply (rule dataplane_tracker_inv_produces_drops[OF D_first,
            where os = os_minted and nid = \<open>0 :: 3\<close>
              and oputs = oputs and produs = produs and drops = drops])
      apply (rule ext; simp add: canon_output_def oputs_def os_minted_def)
      apply (rule ext; simp add: canon_ocaps_def canon_ocaps_port0_def
          drops_def os_minted_def fun_upd_def)
      apply (rule ext; simp add: drops_def os_minted_def base_def
          os_first_propa_def os_progress_def
          os_inv(1,2) obtain_progress_def op_state_base_def operator_state.defs)
      apply (simp add: os_minted_def)
      apply (simp add: canon_inter_def os_minted_def drops_def concat_drops)
      using timely_input_stream_drops_subseteq_C_mints[OF input_stream_inv, of n] os_inv(1)
      apply (auto simp add: drops_def os_minted_def base_def
          os_first_propa_def os_progress_def drop_times_def mint_times_def xs_def
          obtain_progress_def op_state_base_def operator_state.defs split: if_splits)[1]
      apply (clarsimp del: disjCI simp add: produs_def os_minted_def base_def
          os_first_propa_def os_progress_def
          image_iff)
      subgoal for ev
        apply (cases ev; clarsimp del: disjCI simp add: image_iff)
        subgoal for t d
          using timely_input_stream_Data_in_C_in[OF _ input_stream_inv, of _ _ n] os_inv(1)
          by (force simp add: xs_def mint_times_def
              obtain_progress_def op_state_base_def operator_state.defs)
        done
      apply (clarsimp del: disjCI simp add: oputs_def os_minted_def base_def
          os_first_propa_def os_progress_def
          input_data_def input_events_def image_iff split: if_splits)
      subgoal for t d
        using timely_input_stream_Data_in_C_in[OF _ input_stream_inv, of _ _ n] os_inv(1)
        by (auto simp add: mint_times_def xs_def
            obtain_progress_def op_state_base_def operator_state.defs split: event.splits)
      apply (rule oputs_produs)
      apply (rule G_minted)
      apply (rule Nxt_first)
      apply (rule inv_minted)
      done
    have inv_canon: \<open>dataplane_tracker_inv os_canon cbufs sg_first_propa\<close>
      using inv_canon_step
      by (simp add: os_canon_def canon0_def os_minted_def base_def fun_upd_def)

    define target0_canon_ocaps where
      \<open>target0_canon_ocaps = (os_after_input_stream n 0)\<lparr>ocaps :=
        (ocaps (os_after_input_stream n 0))((0 :: 2) := canon_ocaps_port0)\<rparr>\<close>


    define os_target_canon_ocaps where \<open>os_target_canon_ocaps = (os_after_input_stream n)(0 := target0_canon_ocaps)\<close>

    have inter_events_mset:
      \<open>mset (map (\<lambda>t. ((0 :: 2), t, 1 :: int)) (map event.time (filter is_Mint xs))) +
        mset (map (\<lambda>t. ((0 :: 2), t, -1 :: int)) (map event.time (filter is_Drop xs))) =
        mset (map (\<lambda>ev. case ev of Drop t \<Rightarrow> ((0 :: 2), t, -1 :: int) | Mint t \<Rightarrow> ((0 :: 2), t, 1 :: int))
          (filter (Not \<circ> is_Data) xs))\<close> for xs
      by (induct xs) (auto split: event.splits)
    have inter_mset:
      \<open>mset canon_inter = mset (inter (target0_canon_ocaps))\<close>
      using inter_events_mset[of xs]
      by (simp add: canon_inter_def target0_canon_ocaps_def
          os_after_input_stream_def os_input_after_stream_def
          os_first_propa_def os_progress_def base_def
          mint_times_def drop_times_def
          input_events_def xs_def
          obtain_progress_def op_state_base_def operator_state.defs mset_append
          split: event.splits)

    have fields_inter:
      \<open>\<forall>nid. intsum (os_canon nid) = intsum (os_target_canon_ocaps nid) \<and>
        ocaps (os_canon nid) = ocaps (os_target_canon_ocaps nid) \<and>
        consu (os_canon nid) = consu (os_target_canon_ocaps nid) \<and>
        mset (inter (os_canon nid)) = mset (inter (os_target_canon_ocaps nid)) \<and>
        produ (os_canon nid) = produ (os_target_canon_ocaps nid) \<and>
        outpu (os_canon nid) = outpu (os_target_canon_ocaps nid) \<and>
        front (os_canon nid) = front (os_target_canon_ocaps nid)\<close>
      using inter_mset os_inv(1)
      by (auto simp add: os_canon_def canon0_def base_def
          os_target_canon_ocaps_def target0_canon_ocaps_def
          os_after_input_stream_def os_input_after_stream_def
          os_first_propa_def os_progress_def
          canon_ocaps_def canon_output_def produs_def xs_def input_events_def
          obtain_progress_def op_state_base_def operator_state.defs split: event.splits)
    have inv_target_canon_ocaps:
      \<open>dataplane_tracker_inv os_target_canon_ocaps cbufs sg_first_propa\<close>
      using iffD1[OF dataplane_tracker_inv_clean_reorder_inter[OF fields_inter, of cbufs sg_first_propa]]
        inv_canon
      by blast

    have ocaps_mset:
      \<open>mset (ocaps (os_after_input_stream n 0) (0 :: 2)) = mset canon_ocaps_port0\<close>
      using mset_ocaps_updates[of xs \<open>ldropn n lxs\<close> \<open>ocaps (fst (obtain_progress os_input)) (0 :: 2)\<close>]
        input_stream_inv os_inv(1)
      by (simp add: os_after_input_stream_def os_input_after_stream_def
          canon_ocaps_port0_def base_def os_first_propa_def os_progress_def
          mint_times_def drop_times_def xs_def input_events_def
          obtain_progress_def op_state_base_def operator_state.defs mset_list_diff)
    show ?thesis
      apply (rule dataplane_tracker_inv_replace_ocaps
          [where os' = os_target_canon_ocaps and nid = \<open>0 :: 3\<close> and p = \<open>0 :: 2\<close> and C = canon_ocaps_port0])
      apply (rule inv_target_canon_ocaps)
      apply (rule ocaps_mset)
      apply (simp add: os_target_canon_ocaps_def target0_canon_ocaps_def)
      done
  qed

(* ----------------------------- *)
(* STEPS 4: op 0 flushes the outpu buffer *)
  define input0_msgs where \<open>input0_msgs = (\<lambda>n. cbufs (1, 0) @ outpu (os 0) 0 @ input_data n)\<close>
  define cbufs_after_input_output where \<open>cbufs_after_input_output = (\<lambda>n. cbufs((1, 0) := input0_msgs n))\<close>
  define os_input_after_output where
    \<open>os_input_after_output = (\<lambda>n. (os_input_after_stream n)\<lparr>outpu :=
      (outpu (os_input_after_stream n))(0 := [])\<rparr>)\<close>

  define os_after_input_output where
    \<open>os_after_input_output = (\<lambda>n. (os_after_input_stream n)(0 := op_state_base (os_input_after_output n)))\<close>

  have dataplane_after_input_output:
    \<open>dataplane_tracker_inv
      (os_after_input_output n) (cbufs_after_input_output n) sg_first_propa\<close>
    for n
  proof -
    have G_after_input_stream:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_input_stream n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_input_stream n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_input_stream n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_input_stream_def os_input_after_stream_def
            os_first_propa_def os_progress_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs)

      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed

    have edge_input0_label0:
      \<open>summ sg_first_propa (Loc (0 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) \<noteq> {}\<^sub>A\<close>
      by (simp add: sg_first_propa_def sg_progress_def
          subgraph_inv(1) raw_summary_def antichain_from_list_singleton)
    show ?thesis
      apply (rule dataplane_tracker_inv_update_outputs
          [where os = \<open>os_after_input_stream n\<close> and cbufs = cbufs and sg = sg_first_propa
            and nid = \<open>0 :: 3\<close> and p = \<open>0 :: 2\<close>
            and xs = \<open>outpu (os_after_input_stream n 0) (0 :: 2)\<close> and ys = \<open>[]\<close>
            and os' = \<open>os_after_input_output n\<close> and cbufs' = \<open>cbufs_after_input_output n\<close>
            and nid' = \<open>1 :: 3\<close> and p' = \<open>0 :: 2\<close>])
      apply (rule dataplane_after_input_stream)
      apply simp
      apply (simp add: os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def
          fun_upd_def op_state_base_def operator_state.defs)
      apply (simp add: cbufs_after_input_output_def input0_msgs_def
          os_after_input_stream_def os_input_after_stream_def
          fun_upd_def os_inv(1) obtain_progress_def op_state_base_def operator_state.defs)
      apply (rule edge_input0_label0)
      apply (rule G_after_input_stream)
      done
  qed

(* ----------------------------- *)
(* STEPS 5: op 1 consumes all the data in the channel *)
  define os_label_after_read_input0 where
    \<open>os_label_after_read_input0 = (\<lambda>n. CONSUMES 0 (input0_msgs n) os_label_after_first_propa)\<close>

  define cbufs_after_label_read_input0 where
    \<open>cbufs_after_label_read_input0 = (\<lambda>n. (cbufs_after_input_output n)((1, 0) := []))\<close>

  define os_after_label_read_input0 where
    \<open>os_after_label_read_input0 = (\<lambda>n. (os_after_input_output n)(1 := op_state_base (os_label_after_read_input0 n)))\<close>

  have dataplane_after_label_read_input0:
    \<open>dataplane_tracker_inv
      (os_after_label_read_input0 n) (cbufs_after_label_read_input0 n) sg_first_propa\<close>
    for n
  proof -
    have G_after_input_output:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_input_output n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_input_output n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_input_output n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def
            os_first_propa_def os_progress_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs)

      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed

    show ?thesis
      apply (rule dataplane_tracker_inv_fold_consumes
          [where os = \<open>os_after_input_output n\<close> and cbufs = \<open>cbufs_after_input_output n\<close>
            and sg = sg_first_propa and nid = \<open>1 :: 3\<close> and p = \<open>0 :: 2\<close>
            and n = \<open>length (input0_msgs n)\<close>
            and buf' = \<open>cbufs_after_label_read_input0 n\<close>
            and os' = \<open>os_after_label_read_input0 n\<close>])
      apply (rule dataplane_after_input_output)
      apply (simp add: D sg_first_propa_def sg_progress_def)
      apply (rule G_after_input_output)
      apply (simp add: cbufs_after_input_output_def input0_msgs_def)
      apply (rule ext)
      apply (simp add: cbufs_after_label_read_input0_def cbufs_after_input_output_def
          input0_msgs_def split: prod.splits)
      apply (simp add: os_after_label_read_input0_def os_label_after_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_first_propa_def os_progress_def
          os_label_after_first_propa_def cbufs_after_input_output_def input0_msgs_def
          fun_upd_def op_state_base_CONSUMES)
      done
  qed

  have labels_after_label_read_input0:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_read_input0 n) t) (min_label (os_label_after_read_input0 n) t)\<close>
    for n
    using labels_after_first_propa
    by (simp add: os_label_after_read_input0_def input_CONSUMES all_vertices_def all_edges_def neighbors_def min_label_def)

(* ----------------------------- *)
(* STEPS 6: op 1 processes all the new edges in the input 0 *)
  define label_input0_msgs where \<open>label_input0_msgs = (\<lambda>n. input (os 1) 0 @ input0_msgs n)\<close>

  define os_label_after_input0 where
    \<open>os_label_after_input0 = (\<lambda>n. fst (label_prop_input0_batched
      (os_label_after_read_input0 n) (label_input0_msgs n)))\<close>

  define os_after_label_input0 where
    \<open>os_after_label_input0 = (\<lambda>n. (os_after_label_read_input0 n)(1 := op_state_base (os_label_after_input0 n)))\<close>

  have dataplane_after_label_input0:
    \<open>dataplane_tracker_inv
      (os_after_label_input0 n) (cbufs_after_label_read_input0 n) sg_first_propa\<close>
    for n
  proof -
    have G_after_label_read_input0:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_label_read_input0 n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_label_read_input0_def os_label_after_read_input0_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def
            os_first_propa_def os_progress_def os_label_after_first_propa_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs
            input_CONSUMES)

      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have IOC_label_read:
      \<open>input_ocaps_inv (os_label_after_read_input0 n)\<close>
      unfolding os_label_after_read_input0_def
      apply (rule input_ocaps_inv_CONSUMES)
      using label_prop_inv(6) os_inv(4)
      by (simp add: os_label_after_first_propa_def input_ocaps_inv_def operator_state.defs)
    have zero_label_read:
      \<open>0 \<in> set (intsum (os_label_after_read_input0 n) (0 :: 2) (1 :: 2))\<close>
      using os_inv(7) os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          intsum_consumes_fold raw_summary_def zero_myprod_def operator_state.defs)
    have inv_batch:
      \<open>dataplane_tracker_inv
        ((os_after_input_output n)(1 := op_state_base
          (fst (label_prop_input0_batched (os_label_after_read_input0 n)
            (input (os_label_after_read_input0 n) (0 :: 2))))))
        (cbufs_after_label_read_input0 n) sg_first_propa\<close>
      apply (rule dataplane_tracker_inv_label_prop_input0_batched
          [where os = \<open>os_after_input_output n\<close> and nid = \<open>1 :: 3\<close>
            and ls = \<open>os_label_after_read_input0 n\<close>])
      apply (simp add: D sg_first_propa_def sg_progress_def)
      using dataplane_after_label_read_input0[of n]
      apply (simp add: os_after_label_read_input0_def)
      using G_after_label_read_input0
      apply (simp add: os_after_label_read_input0_def)
      apply (simp add: sg_first_propa_def sg_progress_def subgraph_inv(2))
      apply (rule IOC_label_read)
      apply (rule zero_label_read)
      done
    show ?thesis
      using inv_batch input_label_read
      by (simp add: os_after_label_input0_def os_label_after_input0_def
          os_after_label_read_input0_def fun_upd_def)
  qed

  have labels_after_label_input0:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_input0 n) t) (min_label (os_label_after_input0 n) t)\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have WF_read:
      \<open>wf_label_prop_updates (os_label_after_read_input0 n)
        (set (input (os_label_after_read_input0 n) (1 :: 2)))\<close>
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    show ?thesis
      unfolding os_label_after_input0_def
      by (rule labels_inv_fst_label_prop_input0_batched_input_allI
          [OF input_label_read labels_after_label_read_input0 INV_read WF_read])
  qed

  have covered_after_label_input0:
    \<open>label_prop_covered_inv (os_label_after_input0 n)
      (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
       set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
            outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
            map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
              (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
               cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
               outpu (os_label_after_input0 n) (1 :: 2))))\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have WF_read:
      \<open>wf_label_prop_updates (os_label_after_read_input0 n)
        (set (input (os_label_after_read_input0 n) (1 :: 2)))\<close>
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have EN_read: \<open>en1 (os_label_after_read_input0 n) = Inl\<close>
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) input_CONSUMES operator_state.defs)
    have DE_read: \<open>de1 (os_label_after_read_input0 n) = projl\<close>
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) input_CONSUMES operator_state.defs)
    have COV_read: \<open>label_prop_covered_inv (os_label_after_read_input0 n)
        ((set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2))))))))
          \<union> set (outpu (os_label_after_read_input0 n) (1 :: 2)))\<close>
      apply (rule label_prop_covered_inv_transportI[OF label_prop_inv(8)])
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
      subgoal for a l' t t'
        using buffers_inv
        by (fastforce simp add: BULK_BENQ_def inputs_at_target_def
            outputs_at_target_raw_summary subgraph_inv(1) os_inv(4) operator_state.defs
            os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES
            image_Un image_iff split_beta)
      done
    have COV0raw: \<open>label_prop_covered_inv (os_label_after_input0 n)
        ((set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2))))))))
          \<union> set (outpu (os_label_after_input0 n) (1 :: 2)))\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_covered_inv_fst_label_prop_input0_batched_prefixI
          [where rest=\<open>[]\<close>, OF _ EN_read DE_read INV_read WF_read])
      apply (simp add: input_label_read)
      apply (rule COV_read)
      done
    have comp1: \<open>input (os_label_after_input0 n) (1 :: 2) = input os_label_prop (1 :: 2)\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def input_CONSUMES input_fst_label_prop_input0_batched)
    have comp2: \<open>outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) = outpu (os (2 :: 3)) (1 :: 2)\<close>
      and comp3: \<open>input (os_after_label_input0 n (2 :: 3)) (1 :: 2) = input (os (2 :: 3)) (1 :: 2)\<close>
      by (auto simp add: os_after_label_input0_def os_after_label_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
          os_inv(1) op_state_base_def obtain_progress_def operator_state.defs fun_upd_def)
    have comp4: \<open>cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) = cbufs ((1 :: 3), (1 :: 2))\<close>
      and comp5: \<open>cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) = cbufs ((2 :: 3), (1 :: 2))\<close>
      by (auto simp add: cbufs_after_label_read_input0_def cbufs_after_input_output_def
          input0_msgs_def fun_upd_def)
    show ?thesis
      apply (rule label_prop_covered_inv_transportI[OF COV0raw refl refl refl refl])
      subgoal for a l' t t'
        apply (elim UnE)
        subgoal by (fastforce simp add: comp1)
        subgoal by (fastforce simp add: comp4)
        subgoal by (fastforce simp add: comp2)
        subgoal by (rule exI[of _ t']) (simp add: comp3 image_Un)
        subgoal by (rule exI[of _ t']) (simp add: comp5 image_Un)
        subgoal
          apply (rule exI[of _ \<open>t' + Suc 0\<close>])
          apply (simp add: image_Un)
          apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2)
          apply (rule image_eqI[where x=\<open>(Inl (a, l'), MyPair t t')\<close>])
          apply (simp add: plus_myprod_def)
          apply simp
          done
        done
      done
  qed

(* ----------------------------- *)
(* STEPS 7: op 1 loops all the data, and processes everything until the labels converges *)
  define loop_res where
    \<open>loop_res = (\<lambda>n. loop_updates
      (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n))\<close>

  define cbufs_after_loop_updates where \<open>cbufs_after_loop_updates = (\<lambda>n. fst (loop_res n))\<close>

  define os_label_after_loop_updates where \<open>os_label_after_loop_updates = (\<lambda>n. fst (snd (loop_res n)))\<close>

  define os_after_loop_updates where \<open>os_after_loop_updates = (\<lambda>n. snd (snd (loop_res n)))\<close>

  have dataplane_after_loop_updates:
    \<open>dataplane_tracker_inv
      ((os_after_loop_updates n)(1 := op_state_base (os_label_after_loop_updates n)))
      (cbufs_after_loop_updates n) sg_first_propa\<close>
    for n
  proof -
    have step:
      \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n)
        = loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
      by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
          os_after_loop_updates_def loop_res_def prod_eq_iff)

    have D_sg: \<open>dataflow_topology (summ sg_first_propa) (-+-)\<close>
      using D by (simp add: sg_first_propa_def sg_progress_def)
    have Nxt_sg: \<open>nxt sg_first_propa = graph_to_nxt (summ sg_first_propa)\<close>
      using subgraph_inv(2) by (simp add: sg_first_propa_def sg_progress_def)
    have Summ_sg: \<open>summ sg_first_propa = antichain_from_list \<circ>\<circ> raw_summary\<close>
      using subgraph_inv(1) by (simp add: sg_first_propa_def sg_progress_def)
    have IOC2: \<open>input_ocaps_inv ((os_after_label_input0 n) 2)\<close>
      using os_inv(8)
      by (simp add: os_after_label_input0_def os_after_label_read_input0_def
          os_after_input_output_def os_after_input_stream_def
          os_first_propa_def os_progress_def)
    have Inv_step:
      \<open>dataplane_tracker_inv
        ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n)))
        (cbufs_after_label_read_input0 n) sg_first_propa\<close>
      using dataplane_after_label_input0[of n]
      by (simp add: os_after_label_input0_def fun_upd_def)
    have G_after_label_read_input0:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_label_read_input0 n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_label_read_input0_def os_label_after_read_input0_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def
            os_first_propa_def os_progress_def os_label_after_first_propa_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs
            input_CONSUMES)
      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed
    have GR: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
        ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n)))\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
          ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_label_input0_def os_after_label_read_input0_def
            os_label_after_input0_def intsum_fst_label_prop_input0_batched
            op_state_base_def operator_state.defs fun_upd_def)

      show ?thesis
        using eq G_after_label_read_input0 by simp
    qed
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have IOC_label_read:
      \<open>input_ocaps_inv (os_label_after_read_input0 n)\<close>
      unfolding os_label_after_read_input0_def
      apply (rule input_ocaps_inv_CONSUMES)
      using label_prop_inv(6) os_inv(4)
      by (simp add: os_label_after_first_propa_def input_ocaps_inv_def operator_state.defs)
    have lpe:
      \<open>os_label_after_input0 n = operator_state.extend (op_state_base (os_label_after_input0 n))
        \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr,
          timestamps = timestamps (os_label_after_input0 n),
          graph = graph (os_label_after_input0 n),
          vertices = vertices (os_label_after_input0 n),
          label = label (os_label_after_input0 n)\<rparr>\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def op_state_base_def operator_state.defs os_inv(4)
          input_CONSUMES en1_fst_label_prop_input0_batched de1_fst_label_prop_input0_batched
          is_en1_fst_label_prop_input0_batched en2_fst_label_prop_input0_batched
          de2_fst_label_prop_input0_batched is_en2_fst_label_prop_input0_batched)



    have Intsum:
      \<open>\<forall>m. intsum (((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
      using os_inv(7)
      by (simp add: os_after_label_input0_def os_label_after_input0_def
          os_after_label_read_input0_def os_label_after_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
          os_label_after_first_propa_def intsum_fst_label_prop_input0_batched intsum_consumes_fold
          op_state_base_def operator_state.defs os_inv(1) obtain_progress_def os_inv(4))

    have IOC1: \<open>input_ocaps_inv (os_label_after_input0 n)\<close>
    proof -
      have aux:
        \<open>msgs = input ls (0 :: 2) \<Longrightarrow> input_ocaps_inv ls \<Longrightarrow>
          input_ocaps_inv (fst (label_prop_input0_batched ls msgs))\<close>
        for ls :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close> and msgs
      proof (induct msgs arbitrary: ls)
        case Nil
        then show ?case by simp
      next
        case (Cons msg msgs)
        obtain d t where msg_eq: \<open>msg = (d, t)\<close>
          by (cases msg)
        have input_eq: \<open>input ls (0 :: 2) = (d, t) # msgs\<close>
          using Cons.prems(1) msg_eq by simp
        define ls' where \<open>ls' = label_prop_input0_step_state ls d t\<close>

        have step_inv: \<open>input_ocaps_inv ls'\<close>
          unfolding ls'_def
          by (rule input_ocaps_inv_label_prop_input0_step_stateI[OF Cons.prems(2)])
        have input_step: \<open>msgs = input ls' (0 :: 2)\<close>
          using input_eq
          by (simp add: ls'_def input_label_prop_input0_step_state)
        have rec: \<open>input_ocaps_inv (fst (label_prop_input0_batched ls' msgs))\<close>
          by (rule Cons.hyps[OF input_step step_inv])
        then show ?case
          using msg_eq
          by (cases \<open>label_prop_input0_batched ls' msgs\<close>) (simp add: ls'_def)

      qed
      show ?thesis
        unfolding os_label_after_input0_def
        by (rule aux[OF input_label_read[symmetric] IOC_label_read])

    qed
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)


    have INV: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)




    have LABELS:
      \<open>\<forall>t. labels_inv (all_edges (os_label_after_input0 n) t) (min_label (os_label_after_input0 n) t)\<close>
      unfolding os_label_after_input0_def
      apply (intro allI)
      apply (rule labels_inv_fst_label_prop_input0_batched_inputI[where msgs="label_input0_msgs n"])
      apply (rule input_label_read)
      using label_prop_inv(1)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          input_CONSUMES all_vertices_def all_edges_def neighbors_def min_label_def)
      apply (rule INV_read)
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)

    show ?thesis
      apply (rule loop_updates_preserves_dataplane_tracker_inv
          [where cbufs="cbufs_after_label_read_input0 n"
            and os_label_prop="os_label_after_input0 n"
            and os="os_after_label_input0 n"
            and sg="sg_first_propa"
            and T="timestamps (os_label_after_input0 n)"
            and G="graph (os_label_after_input0 n)"
            and V="vertices (os_label_after_input0 n)"
            and L="label (os_label_after_input0 n)"])
      apply (rule step)
      apply (rule D_sg)
      apply (rule GR)
      apply (rule Nxt_sg)
      apply (rule Inv_step)
      apply (rule lpe)
      apply (rule Summ_sg)
      apply (rule Intsum)
      apply (rule IOC1)
      apply (rule IOC2)
      apply (rule INV)
      apply (rule LABELS)
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
      apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
      apply (simp add: input_label_read)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (rule INV_read)
      subgoal
        using label_prop_inv(1)
        by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            input_CONSUMES all_vertices_def all_edges_def neighbors_def min_label_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done

  qed

  have input_0_after_loop_updates_empty:
    \<open>input (os_label_after_loop_updates n) (0 :: 2) = []\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have input0_after_input0:
      \<open>input (os_label_after_input0 n) (0 :: 2) = []\<close>
      unfolding os_label_after_input0_def
      by (rule input_0_fst_label_prop_input0_batched_empty[OF input_label_read[symmetric]])
    have loop_input0:
      \<open>input (fst (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) (0 :: 2) =
        input (os_label_after_input0 n) (0 :: 2)\<close>
      by (rule input_0_fst_snd_loop_updates)
    show ?thesis
      using input0_after_input0 loop_input0
      by (simp add: os_label_after_loop_updates_def loop_res_def)
  qed

  have input_1_after_loop_updates_empty:
    \<open>input (os_label_after_loop_updates n) (1 :: 2) = []\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
      apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
      apply (simp add: input_label_read)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    have loop_input1:
      \<open>input (fst (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) (1 :: 2) = []\<close>
      by (rule input_1_fst_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    show ?thesis
      using loop_input1
      by (simp add: os_label_after_loop_updates_def loop_res_def)
  qed

  have labels_after_loop_updates:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_loop_updates n) t) (min_label (os_label_after_loop_updates n) t)\<close>
    for n
  proof -
    have step:
      \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n) =
        loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
      by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
          os_after_loop_updates_def loop_res_def prod_eq_iff)
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
      apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
      apply (simp add: input_label_read)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    show ?thesis
      by (rule labels_inv_loop_updates_allI[OF step INV0 labels_after_label_input0 WF0 EN0 DE0])
  qed

  have covered_after_loop_updates:
    \<open>label_prop_covered_inv (os_label_after_loop_updates n)
      (set (cbufs_after_loop_updates n ((1 :: 3), (1 :: 2)) @
            outpu (os_after_loop_updates n (2 :: 3)) (1 :: 2) @
            map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
              (input (os_after_loop_updates n (2 :: 3)) (1 :: 2) @
               cbufs_after_loop_updates n ((2 :: 3), (1 :: 2)) @
               outpu (os_label_after_loop_updates n) (1 :: 2))))\<close>
    for n
  proof -
    have step:
      \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n) =
        loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
      by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
          os_after_loop_updates_def loop_res_def prod_eq_iff)
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
      apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
      apply (simp add: input_label_read)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    have EN_read: \<open>en1 (os_label_after_read_input0 n) = Inl\<close>
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) input_CONSUMES operator_state.defs)
    have outpu_read: \<open>outpu (os_label_after_read_input0 n) (1 :: 2) = outpu os_label_prop (1 :: 2)\<close>
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have isl_Inl: \<open>\<exists>v l. d = Inl (v, l)\<close> if \<open>is_en1 os_label_prop d\<close> for d
    proof -
      have \<open>isl d\<close>
        using that os_inv(4) by (simp add: operator_state.defs)
      then obtain y where \<open>d = Inl y\<close>
        by (cases d) auto
      then show ?thesis
        by (cases y) auto
    qed
    have base_is: \<open>\<forall>(d, u) \<in> set (input os_label_prop (1 :: 2)) \<union> set (cbufs ((1 :: 3), (1 :: 2))) \<union>
        set (outpu (os (2 :: 3)) (1 :: 2)) \<union> set (input (os (2 :: 3)) (1 :: 2)) \<union>
        set (cbufs ((2 :: 3), (1 :: 2))) \<union> set (outpu os_label_prop (1 :: 2)). \<exists>v l. d = Inl (v, l)\<close>
      apply (intro ballI)
      subgoal for x
        apply (cases x)
        apply (elim UnE)
        subgoal using os_inv(6)[unfolded label_prob_ty2_check_def] isl_Inl by fastforce
        subgoal using os_inv(6)[unfolded label_prob_ty2_check_def] isl_Inl
          by (fastforce simp add: curry_def)
        subgoal using os_inv(10) isl_Inl by fastforce
        subgoal using os_inv(10) isl_Inl by fastforce
        subgoal using os_inv(10) isl_Inl by fastforce
        subgoal using os_inv(6)[unfolded label_prob_ty2_check_def] isl_Inl by fastforce
        done
      done
    have Inl_out0: \<open>\<forall>(d, u) \<in> set (outpu (fst (label_prop_input0_batched os0 msgs)) (1 :: 2)). \<exists>v l. d = Inl (v, l)\<close>
      if en0: \<open>en1 os0 = Inl\<close> and out0: \<open>\<forall>(d, u) \<in> set (outpu os0 (1 :: 2)). \<exists>v l. d = Inl (v, l)\<close>
      for os0 :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close> and msgs
      using en0 out0
    proof (induct msgs arbitrary: os0)
      case Nil
      then show ?case by simp
    next
      case (Cons m msgs)
      obtain d t where m_eq: \<open>m = (d, t)\<close>
        by (cases m)
      have en_step: \<open>en1 (label_prop_input0_step_state os0 d t) = Inl\<close>
        using Cons.prems(1) by simp
      have out_step: \<open>\<forall>(d', u) \<in> set (outpu (label_prop_input0_step_state os0 d t) (1 :: 2)). \<exists>v l. d' = Inl (v, l)\<close>
        using Cons.prems
        by (fastforce simp add: label_prop_input0_step_batch_def label_prop_edge_batch_def Let_def
            split: prod.splits)
      have rec: \<open>\<forall>(d', u) \<in> set (outpu (fst (label_prop_input0_batched (label_prop_input0_step_state os0 d t) msgs)) (1 :: 2)). \<exists>v l. d' = Inl (v, l)\<close>
        by (rule Cons.hyps[OF en_step out_step])
      show ?case
        using rec unfolding m_eq
        by (cases \<open>label_prop_input0_batched (label_prop_input0_step_state os0 d t) msgs\<close>) simp
    qed
    have Inl_out_input0: \<open>\<forall>(d, u) \<in> set (outpu (os_label_after_input0 n) (1 :: 2)). \<exists>v l. d = Inl (v, l)\<close>
      unfolding os_label_after_input0_def
      apply (rule Inl_out0[OF EN_read])
      using base_is outpu_read by auto
    have comp1: \<open>input (os_label_after_input0 n) (1 :: 2) = input os_label_prop (1 :: 2)\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def input_CONSUMES input_fst_label_prop_input0_batched)
    have comp2: \<open>outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) = outpu (os (2 :: 3)) (1 :: 2)\<close>
      and comp3: \<open>input (os_after_label_input0 n (2 :: 3)) (1 :: 2) = input (os (2 :: 3)) (1 :: 2)\<close>
      by (auto simp add: os_after_label_input0_def os_after_label_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
          os_inv(1) op_state_base_def obtain_progress_def operator_state.defs fun_upd_def)
    have comp4: \<open>cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) = cbufs ((1 :: 3), (1 :: 2))\<close>
      and comp5: \<open>cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) = cbufs ((2 :: 3), (1 :: 2))\<close>
      by (auto simp add: cbufs_after_label_read_input0_def cbufs_after_input_output_def
          input0_msgs_def fun_upd_def)
    have base_isD: \<open>\<exists>v l. d = Inl (v, l)\<close>
      if mem: \<open>(d, u) \<in> set (input os_label_prop (1 :: 2)) \<or>
        (d, u) \<in> set (cbufs ((1 :: 3), (1 :: 2))) \<or>
        (d, u) \<in> set (outpu (os (2 :: 3)) (1 :: 2)) \<or>
        (d, u) \<in> set (input (os (2 :: 3)) (1 :: 2)) \<or>
        (d, u) \<in> set (cbufs ((2 :: 3), (1 :: 2))) \<or>
        (d, u) \<in> set (outpu os_label_prop (1 :: 2))\<close> for d u
      using bspec[OF base_is, of \<open>(d, u)\<close>] mem by auto
    have Inl_out_input0D: \<open>\<exists>v l. d = Inl (v, l)\<close>
      if mem: \<open>(d, u) \<in> set (outpu (os_label_after_input0 n) (1 :: 2))\<close> for d u
      using bspec[OF Inl_out_input0 mem] by simp
    have IS0: \<open>\<forall>(d, u) \<in> set (input (os_label_after_input0 n) (1 :: 2)) \<union>
        set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
             outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
             map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
               (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                outpu (os_label_after_input0 n) (1 :: 2))). \<exists>v l. d = Inl (v, l)\<close>
      apply (intro ballI)
      subgoal for x
        apply (cases x)
        apply (simp only: set_append set_map image_Un Un_iff prod.case)
        apply hypsubst_thin
        apply (elim disjE)
        subgoal by (rule base_isD) (fastforce simp add: comp1)
        subgoal by (rule base_isD) (fastforce simp add: comp4)
        subgoal by (rule base_isD) (fastforce simp add: comp2)
        subgoal
          apply (erule imageE)
          apply (clarsimp simp add: comp3 split_beta)
          apply (rule base_isD)
          apply blast
          done
        subgoal
          apply (erule imageE)
          apply (clarsimp simp add: comp5 split_beta)
          apply (rule base_isD)
          apply blast
          done
        subgoal
          apply (erule imageE)
          apply (clarsimp simp add: split_beta)
          apply (rule Inl_out_input0D)
          apply blast
          done
        done
      done
    show ?thesis
      by (rule label_prop_covered_inv_loop_updatesI
          [OF step INV0 labels_after_label_input0 WF0 EN0 DE0 IS0 covered_after_label_input0])
  qed

  have label_prop_upd_inv_after_loop_updates:
    \<open>label_prop_upd_inv (os_label_after_loop_updates n)\<close>
    for n
  proof -
    have step:
      \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n) =
        loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
      by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
          os_after_loop_updates_def loop_res_def prod_eq_iff)
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
      apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
      apply (simp add: input_label_read)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    show ?thesis
      by (rule label_prop_upd_inv_loop_updatesI[OF step INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
  qed

(* ----------------------------- *)
(* STEPS 8: op 1 drop all capabilities that may be left *)

  define os_after_loop_base where
    \<open>os_after_loop_base = (\<lambda>n. (os_after_loop_updates n)(1 := op_state_base (os_label_after_loop_updates n)))\<close>

  define os_label_after_drop_caps where
    \<open>os_label_after_drop_caps = (\<lambda>n. drop_caps (os_label_after_loop_updates n)
      (map (\<lambda>t. Cap t (1 :: 2)) (ocaps (os_label_after_loop_updates n) (1 :: 2))))\<close>

  define os_after_drop_caps where
    \<open>os_after_drop_caps = (\<lambda>n. (os_after_loop_updates n)(1 := op_state_base (os_label_after_drop_caps n)))\<close>

  have dataplane_after_drop_caps:
    \<open>dataplane_tracker_inv
      (os_after_drop_caps n) (cbufs_after_loop_updates n) sg_first_propa\<close>
    for n
  proof -
    have D_drop: \<open>dataflow_topology (summ sg_first_propa) (-+-)\<close>
      using D by (simp add: sg_first_propa_def sg_progress_def)
    have Nxt_drop: \<open>nxt sg_first_propa = graph_to_nxt (summ sg_first_propa)\<close>
      using subgraph_inv(2) by (simp add: sg_first_propa_def sg_progress_def)
    have Intsum_after_label_input0_pre:
      \<open>\<forall>m. intsum (((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
      using os_inv(7)
      by (simp add: os_after_label_input0_def os_label_after_input0_def
          os_after_label_read_input0_def os_label_after_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
          os_label_after_first_propa_def intsum_fst_label_prop_input0_batched intsum_consumes_fold
          op_state_base_def operator_state.defs os_inv(1) obtain_progress_def os_inv(4))
    have Intsum_base:
      \<open>\<forall>m. intsum ((os_after_loop_base n) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
    proof -
      have step:
        \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n)
          = loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
        by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
            os_after_loop_updates_def loop_res_def prod_eq_iff)
      show ?thesis
        using loop_updates_intsum_corrected[OF step] Intsum_after_label_input0_pre
        by (simp add: os_after_loop_base_def)
    qed
    have G_base:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_base n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_base n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_loop_base n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong) (use Intsum_base os_inv(7) in simp)
      finally show ?thesis
        using G by simp
    qed
    have base_inv:
      \<open>dataplane_tracker_inv (os_after_loop_base n) (cbufs_after_loop_updates n) sg_first_propa\<close>
      using dataplane_after_loop_updates[of n]
      by (simp add: os_after_loop_base_def)
    have drop_eq:
      \<open>os_after_drop_caps n =
        (os_after_loop_base n)(1 := drop_caps (os_after_loop_base n (1 :: 3))
          (map (\<lambda>t. Cap t (1 :: 2)) (ocaps (os_after_loop_base n (1 :: 3)) (1 :: 2))))\<close>
      by (simp add: os_after_drop_caps_def os_after_loop_base_def os_label_after_drop_caps_def
          op_state_base_def drop_caps_def operator_state.defs fun_upd_def)
    show ?thesis
      by (rule dataplane_tracker_inv_drop_caps_all
          [where os=\<open>os_after_loop_base n\<close> and nid=\<open>1 :: 3\<close> and p=\<open>1 :: 2\<close>,
            OF D_drop G_base Nxt_drop base_inv drop_eq])
  qed

(* ----------------------------- *)
(* STEPS 9: op 0 reports progress again *)
  define os_after_loop_progress where
    \<open>os_after_loop_progress = os_after_drop_caps\<close>


  define sg_after_ooo_input_progress where
    \<open>sg_after_ooo_input_progress = (\<lambda>n. sg_first_propa\<lparr>
      pt_tr := change_multiplicities (summ sg_first_propa)
        (extract_progress (0 :: 3) (nxt sg_first_propa)
          (snd (obtain_progress (os_after_loop_progress n 0))))
        (pt_tr sg_first_propa)\<rparr>)\<close>

  define os_after_ooo_input_progress where
    \<open>os_after_ooo_input_progress = (\<lambda>n. (os_after_loop_progress n)
      (0 := op_state_base (fst (obtain_progress (os_after_loop_progress n 0)))))\<close>

  have D_loop: \<open>dataflow_topology (summ sg_first_propa) (-+-)\<close>
    using D by (simp add: sg_first_propa_def sg_progress_def)
  have G_after_label_read_input0:
    \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
    for n
  proof -
    have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n) =
      graph_summar_nt (summ sg) (nxt sg) (os_after_label_read_input0 n)\<close>
      by (simp add: sg_first_propa_def sg_progress_def)
    also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
      by (rule graph_summar_nt_intsum_cong)
        (simp add: os_after_label_read_input0_def os_label_after_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def
          os_first_propa_def os_progress_def os_label_after_first_propa_def
          os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs
          input_CONSUMES intsum_consumes_fold)
    then show ?thesis
      using G by (simp add: sg_first_propa_def sg_progress_def)
  qed
  have G_after_label_input0:
    \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
      ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n)))\<close>
    for n
  proof -
    have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
        ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) =
      graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
      by (rule graph_summar_nt_intsum_cong)
        (simp add: os_after_label_input0_def os_label_after_input0_def
          os_after_label_read_input0_def os_label_after_read_input0_def
          intsum_fst_label_prop_input0_batched op_state_base_def operator_state.defs fun_upd_def)

    show ?thesis
      using eq G_after_label_read_input0 by simp
  qed
  have Intsum_after_label_input0:
    \<open>\<forall>m. intsum (((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) m) =
      (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
    for n
    using os_inv(7)
    by (simp add: os_after_label_input0_def os_label_after_input0_def
        os_after_label_read_input0_def os_label_after_read_input0_def
        os_after_input_output_def os_input_after_output_def
        os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
        os_label_after_first_propa_def intsum_fst_label_prop_input0_batched intsum_consumes_fold
        op_state_base_def operator_state.defs os_inv(1) obtain_progress_def os_inv(4))
  have step_loop:
    \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n)
      = loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
    for n
    by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
        os_after_loop_updates_def loop_res_def prod_eq_iff)
  have ocaps_1_os2_after_loop_updates_empty:
    \<open>ocaps ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
      apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
      apply (simp add: input_label_read)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    have loop_empty:
      \<open>ocaps ((snd (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) 2) (1 :: 2) = []\<close>
      by (rule ocaps_1_snd_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF Intsum_after_label_input0[of n] INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    then show ?thesis
      by (simp add: os_after_loop_updates_def loop_res_def)
  qed

  have outpu_1_after_loop_updates_empty:
    \<open>outpu (os_label_after_loop_updates n) (1 :: 2) = []\<close>
    \<open>outpu ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
    \<open>input ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
    \<open>input_ocaps_inv ((os_after_loop_updates n) 2)\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
      apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
      apply (simp add: input_label_read)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    have IOC0: \<open>input_ocaps_inv ((os_after_label_input0 n) 2)\<close>
      using os_inv(8)
      by (simp add: os_after_label_input0_def os_after_label_read_input0_def
          os_after_input_output_def os_after_input_stream_def
          os_first_propa_def os_progress_def)
    have label_out:
      \<open>outpu (fst (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) (1 :: 2) = []\<close>
      by (rule outpu_1_fst_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    have os2_out:
      \<open>outpu ((snd (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) 2) (1 :: 2) = []\<close>
      by (rule outpu_1_snd_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    have os2_input:
      \<open>input ((snd (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) 2) (1 :: 2) = []\<close>
      by (rule input_1_snd_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    show \<open>outpu (os_label_after_loop_updates n) (1 :: 2) = []\<close>
      using label_out by (simp add: os_label_after_loop_updates_def loop_res_def)
    show \<open>outpu ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
      using os2_out by (simp add: os_after_loop_updates_def loop_res_def)
    show \<open>input ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
      using os2_input by (simp add: os_after_loop_updates_def loop_res_def)
    show \<open>input_ocaps_inv ((os_after_loop_updates n) 2)\<close>
      by (rule input_ocaps_inv_snd_snd_loop_updates2
          [OF step_loop[of n] IOC0 Intsum_after_label_input0[of n]
            EN0 DE0 INV0 labels_after_label_input0[of n] WF0])
  qed


  have wf_after_loop_updates_pending:
    \<open>wf_label_prop_updates (os_label_after_loop_updates n)
      (set (input (os_label_after_loop_updates n) (1 :: 2)) \<union>
       set (cbufs_after_loop_updates n ((1 :: 3), (1 :: 2)) @
            outpu ((os_after_loop_updates n) (2 :: 3)) (1 :: 2) @
            map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
              (input ((os_after_loop_updates n) (2 :: 3)) (1 :: 2) @
               cbufs_after_loop_updates n ((2 :: 3), (1 :: 2)) @
               outpu (os_label_after_loop_updates n) (1 :: 2))))\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
      apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
      apply (simp add: input_label_read)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
      apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    show ?thesis
      by (rule loop_updates_msgs_invI[OF step_loop[of n] EN0 DE0 INV0 labels_after_label_input0[of n] WF0])
  qed


  have Intsum_loop:
    \<open>\<forall>m. intsum ((os_after_loop_progress n) m) =
      (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
    for n
  proof
    fix m :: 3
    have base:
      \<open>intsum (((os_after_loop_updates n)(1 := op_state_base (os_label_after_loop_updates n))) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
      using loop_updates_intsum_corrected[OF step_loop[of n]] Intsum_after_label_input0[of n]
      by auto
    show \<open>intsum ((os_after_loop_progress n) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
      using base
      by (cases \<open>m = (1 :: 3)\<close>)
        (simp_all add: os_after_loop_progress_def os_after_drop_caps_def
          os_label_after_drop_caps_def op_state_base_def drop_caps_def operator_state.defs fun_upd_def)
  qed

  have G_loop:
    \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
    for n
  proof -
    have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n) =
      graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
        ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n)))\<close>
      by (rule graph_summar_nt_intsum_cong)
        (use Intsum_loop Intsum_after_label_input0 in simp)
    show ?thesis
      using eq G_after_label_input0 by simp
  qed

  have dataplane_after_ooo_input_progress:
    \<open>dataplane_tracker_inv
      (os_after_ooo_input_progress n) (cbufs_after_loop_updates n)
      (sg_after_ooo_input_progress n)\<close>
    for n
  proof -
    have inv_no_upfro:
      \<open>dataplane_tracker_inv
        ((os_after_loop_progress n)(0 := fst (obtain_progress (os_after_loop_progress n 0))))
        (cbufs_after_loop_updates n)
        (sg_first_propa\<lparr>pt_tr := change_multiplicities (summ sg_first_propa)
          (extract_progress (0 :: 3) (nxt sg_first_propa)
            (snd (obtain_progress (os_after_loop_progress n 0))))
          (pt_tr sg_first_propa)\<rparr>)\<close>
      apply (rule dataplane_tracker_inv_progress
          [where os="os_after_loop_progress n" and cbufs="cbufs_after_loop_updates n"
            and sg="sg_first_propa" and nid="0 :: 3"])
      using dataplane_after_drop_caps[of n]
      apply (simp add: os_after_loop_progress_def)
      apply (rule D_loop)
      apply (rule G_loop)
      apply (rule refl)
      done

    have clean_os:
      \<open>dataplane_tracker_inv
        (os_after_ooo_input_progress n) (cbufs_after_loop_updates n)
        (sg_after_ooo_input_progress n) \<longleftrightarrow>
       dataplane_tracker_inv
        ((os_after_loop_progress n)(0 := fst (obtain_progress (os_after_loop_progress n 0))))
        (cbufs_after_loop_updates n)
        (sg_after_ooo_input_progress n)\<close>
      by (rule dataplane_tracker_inv_clean;
          (simp add: os_after_ooo_input_progress_def
            os_after_loop_progress_def op_state_base_def operator_state.defs obtain_progress_def
            flip: map_append filter_append fold_append))
    show ?thesis
      using clean_os inv_no_upfro by (simp add: sg_after_ooo_input_progress_def)
  qed

  have G_ooo:
    \<open>graph_summar_nt (summ (sg_after_ooo_input_progress n)) (nxt (sg_after_ooo_input_progress n))
      (os_after_ooo_input_progress n)\<close>
    for n
  proof -
    have eq0:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
        (os_after_ooo_input_progress n) =
       graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
      by (rule graph_summar_nt_intsum_cong)
        (simp add: os_after_ooo_input_progress_def os_after_loop_progress_def
          op_state_base_def operator_state.defs obtain_progress_def flip: map_append filter_append fold_append)
    show ?thesis
      using eq0 G_loop by (simp add: sg_after_ooo_input_progress_def)

  qed


(* ----------------------------- *)
(* STEPS 10: op 1 reports progress *)
  define os_label_after_label_progress where
    \<open>os_label_after_label_progress = (\<lambda>n. fst (obtain_progress (os_label_after_drop_caps n)))\<close>

  define sg_after_label_progress where
    \<open>sg_after_label_progress = (\<lambda>n. (sg_after_ooo_input_progress n)\<lparr>
      pt_tr := change_multiplicities (summ (sg_after_ooo_input_progress n))
        (extract_progress (1 :: 3) (nxt (sg_after_ooo_input_progress n))
          (snd (obtain_progress (os_label_after_drop_caps n))))
        (pt_tr (sg_after_ooo_input_progress n))\<rparr>)\<close>

  define os_after_label_progress where
    \<open>os_after_label_progress = (\<lambda>n. (os_after_ooo_input_progress n)
      (1 := op_state_base (os_label_after_label_progress n)))\<close>

  have dataplane_after_label_progress:
    \<open>dataplane_tracker_inv
      (os_after_label_progress n) (cbufs_after_loop_updates n)
      (sg_after_label_progress n)\<close>
    for n
  proof -
    have D_ooo: \<open>dataflow_topology (summ (sg_after_ooo_input_progress n)) (-+-)\<close>
      using D by (simp add: sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have progress_st:
      \<open>snd (obtain_progress (os_label_after_drop_caps n)) =
        snd (obtain_progress (os_after_ooo_input_progress n 1))\<close>
      by (simp add: os_after_ooo_input_progress_def os_after_loop_progress_def
          os_after_drop_caps_def op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
    have base_progress:
      \<open>fst (obtain_progress (os_after_ooo_input_progress n 1)) =
        op_state_base (os_label_after_label_progress n)\<close>
      by (simp add: os_label_after_label_progress_def os_after_ooo_input_progress_def
          os_after_loop_progress_def os_after_drop_caps_def op_state_base_def
          operator_state.defs obtain_progress_def fun_upd_def)
    have inv_progress:
      \<open>dataplane_tracker_inv
        ((os_after_ooo_input_progress n)(1 := fst (obtain_progress (os_after_ooo_input_progress n 1))))
        (cbufs_after_loop_updates n)
        ((sg_after_ooo_input_progress n)\<lparr>pt_tr := change_multiplicities (summ (sg_after_ooo_input_progress n))
          (extract_progress (1 :: 3) (nxt (sg_after_ooo_input_progress n))
            (snd (obtain_progress (os_label_after_drop_caps n))))
          (pt_tr (sg_after_ooo_input_progress n))\<rparr>)\<close>
      apply (rule dataplane_tracker_inv_progress
          [where os="os_after_ooo_input_progress n"
            and cbufs="cbufs_after_loop_updates n"
            and sg="sg_after_ooo_input_progress n"
            and nid="1 :: 3"
            and st="snd (obtain_progress (os_label_after_drop_caps n))"])
      apply (rule dataplane_after_ooo_input_progress)
      apply (rule D_ooo)
      apply (rule G_ooo)
      apply (rule progress_st)
      done

    show ?thesis
      using inv_progress base_progress
      by (simp add: os_after_label_progress_def sg_after_label_progress_def sg_after_ooo_input_progress_def)

  qed

  have labels_after_label_progress:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_label_progress n) t) (min_label (os_label_after_label_progress n) t)\<close>
    for n
    using labels_after_loop_updates[of n]
    by (simp add: os_label_after_label_progress_def os_label_after_drop_caps_def
        obtain_progress_def op_state_base_def operator_state.defs all_edges_def all_vertices_def
        min_label_def drop_caps_def flip: map_append filter_append fold_append)

(* ----------------------------- *)
(* STEPS 11: op 2 reports progress *)
  define sg_after_increment_progress where
    \<open>sg_after_increment_progress = (\<lambda>n. (sg_after_label_progress n)\<lparr>
      pt_tr := change_multiplicities (summ (sg_after_label_progress n))
        (extract_progress (2 :: 3) (nxt (sg_after_label_progress n))
          (snd (obtain_progress (os_after_label_progress n 2))))
        (pt_tr (sg_after_label_progress n))\<rparr>)\<close>

  define os_after_increment_progress where
    \<open>os_after_increment_progress = (\<lambda>n. (os_after_label_progress n)
      (2 := op_state_base (fst (obtain_progress (os_after_label_progress n 2)))))\<close>
  have dataplane_after_increment_progress:
    \<open>dataplane_tracker_inv
      (os_after_increment_progress n) (cbufs_after_loop_updates n)
      (sg_after_increment_progress n)\<close>
    for n
  proof -
    have D_label: \<open>dataflow_topology (summ (sg_after_label_progress n)) (-+-)\<close>
      using D by (simp add: sg_after_label_progress_def sg_after_ooo_input_progress_def
          sg_first_propa_def sg_progress_def)
    have G_label:
      \<open>graph_summar_nt (summ (sg_after_label_progress n)) (nxt (sg_after_label_progress n))
        (os_after_label_progress n)\<close>
    proof -
      have intsum_eq:
        \<open>\<And>nid. intsum (os_after_label_progress n nid) =
          intsum (os_after_ooo_input_progress n nid)\<close>
      proof -
        fix nid :: 3
        show \<open>intsum (os_after_label_progress n nid) =
          intsum (os_after_ooo_input_progress n nid)\<close>
        proof (cases \<open>nid = (1 :: 3)\<close>)
          case True
          then show ?thesis
            by (simp add: os_after_label_progress_def os_label_after_label_progress_def
                os_after_ooo_input_progress_def os_after_loop_progress_def os_after_drop_caps_def
                op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
        next
          case False
          then show ?thesis
            by (simp add: os_after_label_progress_def fun_upd_def)
        qed
      qed
      have eq0:
        \<open>graph_summar_nt (summ (sg_after_ooo_input_progress n)) (nxt (sg_after_ooo_input_progress n))
          (os_after_label_progress n) =
         graph_summar_nt (summ (sg_after_ooo_input_progress n)) (nxt (sg_after_ooo_input_progress n))
          (os_after_ooo_input_progress n)\<close>
        by (rule graph_summar_nt_intsum_cong) (rule intsum_eq)

      show ?thesis
        using eq0 G_ooo by (simp add: sg_after_label_progress_def)
    qed

    have base_progress:
      \<open>fst (obtain_progress (os_after_label_progress n 2)) =
        op_state_base (fst (obtain_progress (os_after_label_progress n 2)))\<close>
      by (simp add: op_state_base_def operator_state.defs)
    have inv_progress:
      \<open>dataplane_tracker_inv
        ((os_after_label_progress n)(2 := fst (obtain_progress (os_after_label_progress n 2))))
        (cbufs_after_loop_updates n)
        ((sg_after_label_progress n)\<lparr>pt_tr := change_multiplicities (summ (sg_after_label_progress n))
          (extract_progress (2 :: 3) (nxt (sg_after_label_progress n))
            (snd (obtain_progress (os_after_label_progress n 2))))
          (pt_tr (sg_after_label_progress n))\<rparr>)\<close>
      by (rule dataplane_tracker_inv_progress[OF dataplane_after_label_progress D_label G_label refl])
    show ?thesis
      using inv_progress base_progress
      by (simp add: os_after_increment_progress_def sg_after_increment_progress_def)

  qed

  obtain caps' where dt_inv':
    \<open>Src_caps_inv (caps' n) (os_after_loop_progress n)\<close>
    \<open>Trg_caps_inv (caps' n) (outputs_at_target (summ sg_first_propa)
      (os_after_loop_progress n) >> (cbufs_after_loop_updates n))\<close>
    \<open>c_pts_inv
      (change_multiplicities (summ sg_first_propa)
        (extract_prog Enum.enum (nxt sg_first_propa) (os_after_loop_progress n))
        (pt_tr sg_first_propa)) (caps' n)\<close>
    \<open>front_inv (os_after_loop_progress n) (pt_tr sg_first_propa)\<close>
    \<open>imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa)\<close>
    \<open>chnls_imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa)
      (outputs_at_target (summ sg_first_propa)
        (os_after_loop_progress n) >> (cbufs_after_loop_updates n))\<close>
    \<open>change_deltas_inv (os_after_loop_progress n)\<close>
    \<open>propagation_inv (summ sg_first_propa) (pt_tr sg_first_propa)\<close>
    \<open>extract_prog_changes_above_impl_inv (summ sg_first_propa) (nxt sg_first_propa)
      (pt_tr sg_first_propa) (os_after_loop_progress n)\<close>
    \<open>produ_consu_inter_supported (nxt sg_first_propa)
      (os_after_loop_progress n) (pt_tr sg_first_propa)\<close>
  for n
  proof -
    have ex_caps:
      \<open>\<forall>n. \<exists>cap.
        Src_caps_inv cap (os_after_loop_progress n) \<and>
        Trg_caps_inv cap (outputs_at_target (summ sg_first_propa)
          (os_after_loop_progress n) >> (cbufs_after_loop_updates n)) \<and>
        c_pts_inv
          (change_multiplicities (summ sg_first_propa)
            (extract_prog Enum.enum (nxt sg_first_propa) (os_after_loop_progress n))
            (pt_tr sg_first_propa)) cap \<and>
        front_inv (os_after_loop_progress n) (pt_tr sg_first_propa) \<and>
        imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa) \<and>
        chnls_imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa)
          (outputs_at_target (summ sg_first_propa)
            (os_after_loop_progress n) >> (cbufs_after_loop_updates n)) \<and>
        change_deltas_inv (os_after_loop_progress n) \<and>
        propagation_inv (summ sg_first_propa) (pt_tr sg_first_propa) \<and>
        extract_prog_changes_above_impl_inv (summ sg_first_propa) (nxt sg_first_propa)
          (pt_tr sg_first_propa) (os_after_loop_progress n) \<and>
        produ_consu_inter_supported (nxt sg_first_propa)
          (os_after_loop_progress n) (pt_tr sg_first_propa)\<close>
    proof
      fix n
      show \<open>\<exists>cap.
        Src_caps_inv cap (os_after_loop_progress n) \<and>
        Trg_caps_inv cap (outputs_at_target (summ sg_first_propa)
          (os_after_loop_progress n) >> (cbufs_after_loop_updates n)) \<and>
        c_pts_inv
          (change_multiplicities (summ sg_first_propa)
            (extract_prog Enum.enum (nxt sg_first_propa) (os_after_loop_progress n))
            (pt_tr sg_first_propa)) cap \<and>
        front_inv (os_after_loop_progress n) (pt_tr sg_first_propa) \<and>
        imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa) \<and>
        chnls_imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa)
          (outputs_at_target (summ sg_first_propa)
            (os_after_loop_progress n) >> (cbufs_after_loop_updates n)) \<and>
        change_deltas_inv (os_after_loop_progress n) \<and>
        propagation_inv (summ sg_first_propa) (pt_tr sg_first_propa) \<and>
        extract_prog_changes_above_impl_inv (summ sg_first_propa) (nxt sg_first_propa)
          (pt_tr sg_first_propa) (os_after_loop_progress n) \<and>
        produ_consu_inter_supported (nxt sg_first_propa)
          (os_after_loop_progress n) (pt_tr sg_first_propa)\<close>
        using dataplane_after_drop_caps[of n, unfolded dataplane_tracker_inv_def]
        by (simp add: os_after_loop_progress_def)
    qed
    show ?thesis
      using choice[OF ex_caps] that by blast
  qed

  define second_progress where \<open>second_progress = (\<lambda>n.
    extract_progress (0 :: 3) (nxt sg_first_propa)
      (snd (obtain_progress (os_after_loop_progress n 0))) @
    extract_progress (1 :: 3) (nxt sg_first_propa)
      (snd (obtain_progress (os_label_after_drop_caps n))) @
    extract_progress (2 :: 3) (nxt sg_first_propa)
      (snd (obtain_progress (os_after_loop_progress n 2))))\<close>

  have c_pts_after_second_progress_caps':
    \<open>c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary)
      (second_progress n) c') l = caps' n l\<close>
    for n l
    using dt_inv'(3)[of n]
    by (simp add: c_pts_inv_def second_progress_def extract_prog_def
        sg_first_propa_def sg_progress_def os_after_loop_progress_def os_after_drop_caps_def
        subgraph_inv(1,2) op_state_base_def operator_state.defs obtain_progress_def
        flip: fold_append change_multiplicities_append_alt)

  obtain c'' where second_propa:
    \<open>propagate_all (summ sg_first_propa)
      (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) = Some (c'' n)\<close>
    \<open>\<forall>loc. frontier (c_imp (c'' n) loc) =
      ifrontier (summ sg_first_propa) (-+-)
        (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) loc\<close>
    \<open>dataflow_topology_from_tree.inv_implications_nonneg (c'' n)\<close>
    \<open>dataflow_topology_from_tree.inv_imp_plus_work_nonneg (c'' n)\<close>
    \<open>dataflow_topology.inv_imps_work_sum (summ sg_first_propa) (-+-) (c'' n)\<close>
  for n
  proof -
    have ex_c:
      \<open>\<forall>n. \<exists>c2.
        propagate_all (summ sg_first_propa)
          (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) = Some c2 \<and>
        (\<forall>loc. frontier (c_imp c2 loc) =
          ifrontier (summ sg_first_propa) (-+-)
            (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) loc) \<and>
        dataflow_topology_from_tree.inv_implications_nonneg c2 \<and>
        dataflow_topology_from_tree.inv_imp_plus_work_nonneg c2 \<and>
        dataflow_topology.inv_imps_work_sum (summ sg_first_propa) (-+-) c2\<close>
    proof
      fix n
      show \<open>\<exists>c2.
        propagate_all (summ sg_first_propa)
          (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) = Some c2 \<and>
        (\<forall>loc. frontier (c_imp c2 loc) =
          ifrontier (summ sg_first_propa) (-+-)
            (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) loc) \<and>
        dataflow_topology_from_tree.inv_implications_nonneg c2 \<and>
        dataflow_topology_from_tree.inv_imp_plus_work_nonneg c2 \<and>
        dataflow_topology.inv_imps_work_sum (summ sg_first_propa) (-+-) c2\<close>
        using change_multiplicities_and_propagate_all_correctness
          [OF D, of \<open>pt_tr sg_first_propa\<close> \<open>second_progress n\<close>,
            unfolded subgraph_inv(1), simplified]
        apply -
        apply (drule meta_mp)
        subgoal
          using dt_inv'(8)[unfolded propagation_inv_def] subgraph_inv(1)
          by (simp add: sg_first_propa_def sg_progress_def)



        apply (drule meta_mp)
        subgoal
          using dt_inv'(8)[unfolded propagation_inv_def] subgraph_inv(1) by auto
        apply (drule meta_mp)
        subgoal
          using dt_inv'(8)[unfolded propagation_inv_def] subgraph_inv(1) by auto


        apply (drule meta_mp)
        subgoal
          apply (clarsimp simp flip: fold_append change_multiplicities_append_alt
              simp add: second_progress_def split_beta Misc.set_map_filter op_state_base_def
              extract_progress_def image_iff
              split: prod.splits option.splits event.splits)

          subgoal for l t
            apply (elim disjE exE; (clarsimp simp add: obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)?)
            subgoal for p
              using conjunct1[OF dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format,
                    of p t 0 0, simplified]]
              by (simp add: os_after_loop_progress_def)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format,
                  of p t 0 0, simplified]
              by (simp add: os_after_loop_progress_def)



            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 0, simplified] apply -
              by (clarsimp simp add: os_after_loop_progress_def op_state_base_def obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)


            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 1, simplified] apply -
              by (clarsimp simp add: os_after_loop_progress_def os_after_drop_caps_def
                  op_state_base_def obtain_progress_def Misc.set_map_filter image_iff
                  del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 1, simplified] apply -
              by (clarsimp simp add: os_after_loop_progress_def os_after_drop_caps_def
                  op_state_base_def obtain_progress_def Misc.set_map_filter image_iff
                  del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 1, simplified] apply -
              by (clarsimp simp add: os_after_loop_progress_def os_after_drop_caps_def
                  op_state_base_def obtain_progress_def Misc.set_map_filter image_iff
                  del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 2, simplified] apply -
              by (clarsimp simp add: op_state_base_def obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 2, simplified] apply -
              by (clarsimp simp add: op_state_base_def obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 2, simplified] apply -
              by (clarsimp simp add: op_state_base_def obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)
            done

          done
        apply (drule meta_mp)
        subgoal
          apply (clarsimp simp add: second_progress_def)

          subgoal for l t m
            apply (subst frontier_less_equal_iff[symmetric])
            apply (rule frontier_less_equal_le_trans
                [of \<open>ifrontier (summ sg_first_propa) (+) (pt_tr sg_first_propa) l\<close>])
            subgoal
              apply (elim disjE)
              subgoal
                using dt_inv'(9)[of n, unfolded extract_prog_changes_above_impl_inv_def
                    changes_above_impl_inv_def, simplified, rule_format,
                    where xs=Nil and nid=0, simplified]
                apply (clarsimp simp add: os_after_loop_progress_def op_state_base_def obtain_progress_def subgraph_inv(1,2) set_map_filter
                    split_beta operator_state.defs os_inv(1) image_iff split: option.splits)

                done
              subgoal
                using dt_inv'(9)[of n, unfolded extract_prog_changes_above_impl_inv_def
                    changes_above_impl_inv_def, simplified, rule_format,
                    where xs=Nil and nid=1, simplified]
                apply (clarsimp simp add: os_after_loop_progress_def os_after_drop_caps_def
                    op_state_base_def obtain_progress_def subgraph_inv(1,2) set_map_filter
                    split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
                done
              subgoal
                using dt_inv'(9)[of n, unfolded extract_prog_changes_above_impl_inv_def
                    changes_above_impl_inv_def, simplified, rule_format,
                    where xs=Nil and nid=2, simplified]
                apply (clarsimp simp add: op_state_base_def obtain_progress_def subgraph_inv(1,2) set_map_filter
                    split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
                done
              done
            using dt_inv'(5)[unfolded imp_front_inv_def, rule_format, of l] by simp
          done
        apply (drule meta_mp)
        subgoal
          using raw_summary_no_self_loop by auto
        by (clarsimp simp flip: fold_append map_append
            simp add: sg_first_propa_def sg_progress_def subgraph_inv(1,2) CONSUMES_CONSUMES)

    qed
    show ?thesis
      using choice[OF ex_c] that by blast
  qed

(* STEPS 12: op 1 reads the final frontier from the propagation *)
  define label_front_after_second_propa where
    \<open>label_front_after_second_propa = (\<lambda>n. frontier \<circ> (\<lambda>p. c_imp (c'' n) (Loc (1 :: 3) (Trg p))))\<close>

  define os_label_after_second_propa where
    \<open>os_label_after_second_propa = (\<lambda>n. (os_label_after_label_progress n)\<lparr>
      front := label_front_after_second_propa n, initia := True\<rparr>)\<close>

  define sg_after_second_propa where
    \<open>sg_after_second_propa = (\<lambda>n. (sg_after_increment_progress n)\<lparr>
      pt_tr := c'' n\<rparr>)\<close>

  define os_after_second_propa where
    \<open>os_after_second_propa = (\<lambda>n. (os_after_increment_progress n)
      (1 := op_state_base (os_label_after_second_propa n)))\<close>

  have dataplane_after_second_propa: \<open>dataplane_tracker_inv
      (os_after_second_propa n) (cbufs_after_loop_updates n)
      (sg_after_second_propa n)\<close>
    for n
  proof -
    have D_increment: \<open>dataflow_topology (summ (sg_after_increment_progress n)) (-+-)\<close>
      using D by (simp add: sg_after_increment_progress_def sg_after_label_progress_def
          sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have reachable_increment: \<open>reachable_locations (summ (sg_after_increment_progress n)) = UNIV\<close>
      using subgraph_inv(1) by (simp add: sg_after_increment_progress_def sg_after_label_progress_def
          sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have propagate_increment:
      \<open>propagate_all (summ (sg_after_increment_progress n)) (pt_tr (sg_after_increment_progress n)) = Some (c'' n)\<close>
      using second_propa(1)[of n]
      by (simp add: sg_after_increment_progress_def sg_after_label_progress_def
          sg_after_ooo_input_progress_def os_after_label_progress_def os_after_ooo_input_progress_def
          os_after_loop_progress_def second_progress_def
          flip: fold_append change_multiplicities_append_alt)


    have G_increment:
      \<open>graph_summar_nt (summ (sg_after_increment_progress n)) (nxt (sg_after_increment_progress n))
        (os_after_increment_progress n)\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
          (os_after_increment_progress n) =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_increment_progress_def os_after_label_progress_def
            os_after_ooo_input_progress_def os_label_after_label_progress_def os_after_loop_progress_def
            os_after_drop_caps_def op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
      then show ?thesis
        using G_loop[of n]
        by (simp add: sg_after_increment_progress_def sg_after_label_progress_def
            sg_after_ooo_input_progress_def)
    qed
    define front_c where \<open>front_c = frontier \<circ> (\<lambda>p. c_imp (c'' n) (Loc (1 :: 3) (Trg p)))\<close>

    have inv_front_no_upfro: 
      \<open>dataplane_tracker_inv
        (os_after_second_propa n) (cbufs_after_loop_updates n)
        ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>)\<close>
    proof -
      define os_front where \<open>os_front = map_entry (1 :: 3) (front_update (\<lambda>_. front_c)) (os_after_increment_progress n)\<close>

      have inv_map:
        \<open>dataplane_tracker_inv os_front (cbufs_after_loop_updates n)
          ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>)\<close>
        unfolding os_front_def front_c_def
        by (rule dataplane_tracker_inv_front_update
            [OF D_increment reachable_increment propagate_increment G_increment dataplane_after_increment_progress,
              where nid = \<open>1 :: 3\<close>, simplified])

      have clean_initia:
        \<open>dataplane_tracker_inv
          (os_after_second_propa n) (cbufs_after_loop_updates n)
          ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>) \<longleftrightarrow>
          dataplane_tracker_inv os_front (cbufs_after_loop_updates n)
          ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>)\<close>
        by (rule dataplane_tracker_inv_clean)
          (simp_all add: os_after_second_propa_def os_front_def os_label_after_second_propa_def
            label_front_after_second_propa_def front_c_def os_after_increment_progress_def
            os_after_label_progress_def op_state_base_def operator_state.defs)
      show ?thesis
        using clean_initia inv_map by simp
    qed
    show ?thesis
      using inv_front_no_upfro by (simp add: sg_after_second_propa_def)
  qed

  have labels_after_second_propa:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_second_propa n) t) (min_label (os_label_after_second_propa n) t)\<close>
    for n
    using labels_after_label_progress[of n]
    by (simp add: os_label_after_second_propa_def all_edges_def all_vertices_def min_label_def)


(* ----------------------------- *)
(* STEPS 13: op 1 produces all the wcc components from the labels *)
  define label_produces_below_times where
    \<open>label_produces_below_times = (\<lambda>n.
      filter
        (\<lambda>t. \<not> frontier_less_equal
          (exit_scope myfst (front (os_label_after_second_propa n) 0 + front (os_label_after_second_propa n) 1))
          (myfst t) \<and> myfst t \<in> set (timestamps (os_label_after_second_propa n)))
        (ocaps (os_label_after_second_propa n) 0))\<close>

  define label_produces_batch where
    \<open>label_produces_batch = (\<lambda>n. label_prop_output_batch
      (os_label_after_second_propa n) (label_produces_below_times n) ::
      ((nat \<times> nat + nat set set) \<times> (2, (nat, nat) myprod) capability) list)\<close>

  define os_label_after_produces where
    \<open>os_label_after_produces = (\<lambda>n. drop_caps
      (produces (os_label_after_second_propa n) (label_produces_batch n))
      (map (\<lambda>t. Cap t (0 :: 2)) (label_produces_below_times n)))\<close>

  define os_after_label_produces where
    \<open>os_after_label_produces = (\<lambda>n. (os_after_second_propa n)
      (1 := op_state_base (os_label_after_produces n)))\<close>

  have dataplane_after_label_produces:
    \<open>dataplane_tracker_inv
      (os_after_label_produces n) (cbufs_after_loop_updates n)
      (sg_after_second_propa n)\<close>
    for n
  proof -
    have intsum_label_input0_10:
      \<open>intsum (os_label_after_input0 n) (1 :: 2) (0 :: 2) = []\<close>
      using Intsum_after_label_input0[of n, rule_format, of 1]
      by (simp add: os_after_label_input0_def op_state_base_def operator_state.defs raw_summary_def)
    have ocaps0_loop:
      \<open>ocaps (os_label_after_loop_updates n) (0 :: 2) = ocaps (os_label_after_input0 n) 0\<close>
      unfolding os_label_after_loop_updates_def loop_res_def
      by (subst ocaps_0_fst_snd_loop_updates) (rule intsum_label_input0_10, simp)

    have intsum_label_first_00:
      \<open>intsum os_label_after_first_propa (0 :: 2) (0 :: 2) = [MyPair 0 0]\<close>
      using os_inv(7)[rule_format, of 1]
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs raw_summary_def)
    have ocaps0_first_mysnd:
      \<open>\<forall>t \<in> set (ocaps os_label_after_first_propa (0 :: 2)). mysnd t = 0\<close>
      using label_prop_inv(4)
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs)
    have input0_msgs_mysnd:
      \<open>\<forall>t \<in> snd ` set (input0_msgs n). mysnd t = 0\<close>
      using label_prop_inv(4) buffers_inv input_stream_inv
      by (force simp add: input0_msgs_def input_data_def input_events_def
          buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def
          os_inv(1) operator_state.defs split: event.splits dest!: setltakenD)


    have ocaps0_read_mysnd:
      \<open>\<forall>t \<in> set (ocaps (os_label_after_read_input0 n) (0 :: 2)). mysnd t = 0\<close>
      using ocaps0_first_mysnd input0_msgs_mysnd intsum_label_first_00
      by (auto simp add: os_label_after_read_input0_def fold_consumes zero_myprod_def split: prod.splits)
    have ocaps0_second_mysnd:
      \<open>\<forall>t \<in> set (ocaps (os_label_after_second_propa n) (0 :: 2)). mysnd t = 0\<close>
      using ocaps0_loop ocaps0_read_mysnd
      by (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
          os_label_after_drop_caps_def os_label_after_input0_def drop_caps_def
          obtain_progress_def operator_state.defs)

    have D_second: \<open>dataflow_topology (summ (sg_after_second_propa n)) (-+-)\<close>
      using D by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
          sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have Nxt_second: \<open>nxt (sg_after_second_propa n) = graph_to_nxt (summ (sg_after_second_propa n))\<close>
      using subgraph_inv(2) by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
          sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have G_second:
      \<open>graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
        (os_after_second_propa n)\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
          (os_after_second_propa n) =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_second_propa_def os_label_after_second_propa_def
            os_after_increment_progress_def os_after_label_progress_def os_after_ooo_input_progress_def
            os_label_after_label_progress_def os_after_loop_progress_def os_after_drop_caps_def
            op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
      then show ?thesis
        using G_loop[of n]
        by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
            sg_after_label_progress_def sg_after_ooo_input_progress_def)
    qed
    have input0_loop_updates:
      \<open>input (fst (snd (loop_updates cb lp os'))) (0 :: 2) = input lp 0\<close>
      for cb lp os'
      by (induct cb lp os' rule: loop_updates.induct)
        (subst loop_updates.simps;
          clarsimp split: prod.splits;
          metis label_prop_input1_loop_updates_input_label_0)

    have input0_second_empty:
      \<open>input (os_after_second_propa n 1) (0 :: 2) = []\<close>
      using input_0_after_loop_updates_empty[of n]
      by (simp add: os_after_second_propa_def os_label_after_second_propa_def
          os_label_after_label_progress_def os_label_after_drop_caps_def drop_caps_def
          obtain_progress_def op_state_base_def operator_state.defs)
    have inv_produces: \<open>dataplane_tracker_inv
        ((os_after_second_propa n)(1 := drop_caps
          (produces (os_after_second_propa n 1) (label_produces_batch n))
          (map (\<lambda>t. Cap t (0 :: 2)) (label_produces_below_times n))))
        (cbufs_after_loop_updates n) (sg_after_second_propa n)\<close>
      apply (rule dataplane_tracker_inv_produces_drop
          [of \<open>os_after_second_propa n\<close> \<open>1 :: 3\<close> \<open>os_after_second_propa n 1\<close>
            \<open>cbufs_after_loop_updates n\<close> \<open>sg_after_second_propa n\<close>
            \<open>label_produces_batch n\<close>
            \<open>map (\<lambda>t. Cap t (0 :: 2)) (label_produces_below_times n)\<close>])
      apply (simp add: dataplane_after_second_propa)
      apply (rule D_second)
      apply (simp add: G_second)
      apply (rule Nxt_second)
      subgoal for x cap
        using ocaps0_second_mysnd
        apply (clarsimp simp add: label_produces_batch_def label_prop_output_batch_def
            label_produces_below_times_def os_after_second_propa_def os_label_after_second_propa_def
            op_state_base_def operator_state.defs)
        by (metis myprod.collapse)
      subgoal for p'
        apply (cases \<open>p' = (0 :: 2)\<close>)
        subgoal
          by (simp add: label_produces_below_times_def os_after_second_propa_def
              os_label_after_second_propa_def op_state_base_def operator_state.defs
              mset_filter filter_map comp_def)
        subgoal
          by (simp add: filter_False)
        done
      subgoal for p'
        by (cases \<open>p' = (0 :: 2)\<close>)
          (auto simp add: label_produces_below_times_def input0_second_empty filter_False)

      done


    show ?thesis
      using inv_produces
      by (simp add: os_after_label_produces_def os_label_after_produces_def
          os_after_second_propa_def os_label_after_second_propa_def
          op_state_base_def drop_caps_def produces_def)

  qed


  have labels_after_label_produces:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_produces n) t) (min_label (os_label_after_produces n) t)\<close>
    for n
    using labels_after_second_propa[of n]
    by (simp add: os_label_after_produces_def)


  let ?input_caps_after_prefix =
    "\<lambda>n. mset (ocaps (os 0) (0 :: 2)) +
      event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
      event.time `# filter_mset is_Drop (mset (ltaken n lxs))"
  let ?input_frontier_after_prefix =
    "\<lambda>n. frontier (zmset_of (?input_caps_after_prefix n))"

  have input_caps_in_lset:
    \<open>t \<in># mset (ocaps (os 0) (0 :: 2)) \<Longrightarrow> t \<in> event.time ` lset lxs\<close> for t
  proof -
    assume t_in: \<open>t \<in># mset (ocaps (os 0) (0 :: 2))\<close>
    obtain n where vacant: \<open>vacant t (?input_caps_after_prefix n)\<close>
      using input_stream_inv
      unfolding timely_input_stream_def timely_progress_def
      by auto
    let ?C = \<open>mset (ocaps (os 0) (0 :: 2))\<close>
    let ?M = \<open>event.time `# filter_mset is_Mint (mset (ltaken n lxs))\<close>
    let ?D = \<open>event.time `# filter_mset is_Drop (mset (ltaken n lxs))\<close>
    have vacant_t: \<open>count (?C + ?M - ?D) t = 0\<close>
      using vacant unfolding vacant_def by simp
    have live_before_drops: \<open>0 < count (?C + ?M) t\<close>
      using t_in by simp
    have drop_pos: \<open>0 < count ?D t\<close>
      using vacant_t live_before_drops
      by (cases \<open>count ?D t\<close>) auto
    then obtain e where e_in:
      \<open>e \<in># filter_mset is_Drop (mset (ltaken n lxs))\<close>
      and e_time: \<open>event.time e = t\<close>
      by auto
    then have \<open>e \<in> set (ltaken n lxs)\<close>
      by simp
    then have \<open>e \<in> lset lxs\<close>
      by (rule setltakenD)
    then show ?thesis
      using e_time by blast
  qed

  have input_cap_after_prefix_mysnd0:
    \<open>x \<in># ?input_caps_after_prefix n \<Longrightarrow> mysnd x = 0\<close> for n x
  proof -
    assume x_in: \<open>x \<in># ?input_caps_after_prefix n\<close>
    have x_live:
      \<open>x \<in># mset (ocaps (os 0) (0 :: 2)) \<or>
        x \<in># event.time `# filter_mset is_Mint (mset (ltaken n lxs))\<close>
      using in_diffD[OF x_in] by auto
    then have \<open>x \<in> event.time ` lset lxs\<close>
    proof
      assume \<open>x \<in># mset (ocaps (os 0) (0 :: 2))\<close>
      then show ?thesis
        by (rule input_caps_in_lset)
    next
      assume \<open>x \<in># event.time `# filter_mset is_Mint (mset (ltaken n lxs))\<close>
      then obtain e where \<open>e \<in># filter_mset is_Mint (mset (ltaken n lxs))\<close>
        and \<open>event.time e = x\<close>
        by auto
      then show ?thesis
        using setltakenD[of e n lxs] by auto
    qed
    then show ?thesis
      using label_prop_inv(4) by auto
  qed

  have input_frontier_mysnd0:
    \<open>x \<in>\<^sub>A ?input_frontier_after_prefix n \<Longrightarrow> mysnd x = 0\<close> for n x
  proof -
    assume x_in: \<open>x \<in>\<^sub>A ?input_frontier_after_prefix n\<close>
    have \<open>x \<in># ?input_caps_after_prefix n\<close>
      using x_in
      apply (subst count_greater_zero_iff[symmetric])
      apply (simp add: in_frontier_iff)
      done
    then show ?thesis
      by (rule input_cap_after_prefix_mysnd0)
  qed

  have input_frontier_exit_scopeD:
    \<open>frontier_less_equal (exit_scope myfst (?input_frontier_after_prefix n)) (myfst t) \<Longrightarrow>
      mysnd t = 0 \<Longrightarrow>
      frontier_less_equal (?input_frontier_after_prefix n) t\<close> for n t
  proof -
    assume projected:
      \<open>frontier_less_equal (exit_scope myfst (?input_frontier_after_prefix n)) (myfst t)\<close>
    assume t_zero: \<open>mysnd t = 0\<close>
    obtain y where y_in: \<open>y \<in>\<^sub>A exit_scope myfst (?input_frontier_after_prefix n)\<close>
      and y_le: \<open>y \<le> myfst t\<close>
      using projected unfolding frontier_less_equal_iff by blast
    from y_in obtain x where x_in: \<open>x \<in>\<^sub>A ?input_frontier_after_prefix n\<close>
      and x_fst: \<open>myfst x = y\<close>
      by (rule exit_scope_memberE)
    have x_zero: \<open>mysnd x = 0\<close>
      by (rule input_frontier_mysnd0[OF x_in])
    have \<open>x \<le> t\<close>
      using y_le x_fst x_zero t_zero
      by (cases x; cases t; simp)
    then show ?thesis
      using x_in unfolding frontier_less_equal_iff by blast
  qed

  have no_second_propa_output_frontier:
    \<open>\<not> frontier_less_equal
        (exit_scope myfst
          (frontier (c_imp (c'' n) (Loc 1 (Trg 0))) +
           frontier (c_imp (c'' n) (Loc 1 (Trg 1)))))
        (myfst t)\<close>
    if input_frontier_fresh:
      \<open>\<not> frontier_less_equal (?input_frontier_after_prefix n) t\<close>
      and t_live:
      \<open>t |\<in>| ts lxs \<or>
        cBex (cset_from_list (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0))) (\<lambda>x. t = snd x) \<or>
        cBex (cfilter (\<lambda>t. \<exists>x\<in>set (ocaps (os 1) 0). t = myfst x) (cset_from_list (timestamps os_label_prop))) (\<lambda>x. t = MyPair x 0)\<close>
    for n t


    unfolding second_propa(2)[rule_format, of n "Loc 1 (Trg 1)"]
      second_propa(2)[rule_format, of n "Loc 1 (Trg 0)"]

    apply safe
    apply (simp add: exit_scope_plus_distrib)
    apply (drule frontier_less_equal_pluss_le)
    subgoal
      apply (simp add: sg_first_propa_def sg_progress_def subgraph_inv(1))
      apply (rule exit_scope_ifrontier_L1T0_le_L1T1_empty_loop)
      subgoal
        using D by (simp add: sg_first_propa_def sg_progress_def subgraph_inv(1))
      subgoal
        using c_pts_after_second_progress_caps'[of n \<open>Loc (1 :: 3) (Src (1 :: 2))\<close>]
          dt_inv'(1)[of n]
        by (simp add: Src_caps_inv_def os_after_loop_progress_def
            os_after_drop_caps_def os_label_after_drop_caps_def
            op_state_base_def operator_state.defs ocaps_drop_caps_all)
      subgoal
        using c_pts_after_second_progress_caps'[of n \<open>Loc (2 :: 3) (Trg (1 :: 2))\<close>]
          dt_inv'(2)[of n] outpu_1_after_loop_updates_empty(1)[of n]
        by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary subgraph_inv(1)
            sg_first_propa_def sg_progress_def cbufs_after_loop_updates_def loop_res_def
            os_after_loop_progress_def os_after_drop_caps_def os_label_after_drop_caps_def
            drop_caps_def op_state_base_def operator_state.defs)
      subgoal
        using c_pts_after_second_progress_caps'[of n \<open>Loc (2 :: 3) (Src (1 :: 2))\<close>]
          dt_inv'(1)[of n] ocaps_1_os2_after_loop_updates_empty[of n]
        by (simp add: Src_caps_inv_def os_after_loop_progress_def os_after_drop_caps_def)
      subgoal
        using c_pts_after_second_progress_caps'[of n \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>]
          dt_inv'(2)[of n] outpu_1_after_loop_updates_empty(2)[of n]
        by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary subgraph_inv(1)
            sg_first_propa_def sg_progress_def cbufs_after_loop_updates_def loop_res_def
            os_after_loop_progress_def os_after_drop_caps_def
            op_state_base_def operator_state.defs)
      done
    subgoal
      apply (subgoal_tac "ifrontier (summ sg_first_propa) (-+-) (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) (Loc 1 (Trg 0)) =
                          frontier (zmset_of (mset (ocaps (os 0) 0) + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) - event.time `# filter_mset is_Drop (mset (ltaken n lxs))))")
      defer
      subgoal premises auxx
        apply (simp add: sg_first_propa_def sg_progress_def)
        unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D] UNIV_3_2
        apply (clarsimp simp add: split_beta subgraph_inv(1))
        subgoal premises self_path
          apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c') (Loc (0 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z")
          defer
          subgoal
            apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                 (Loc (0 :: 3) (Trg (0 :: 2))) = caps' n (Loc 0 (Trg 0))")
            defer
            subgoal
              using c_pts_after_second_progress_caps'[of n \<open>Loc (0 :: 3) (Trg (0 :: 2))\<close>]
              by simp
            apply (subgoal_tac "caps' n (Loc (0 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z")
            defer
            subgoal
              using dt_inv'(2)[of n] buffers_inv(2)
              by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary subgraph_inv(1)
                  sg_first_propa_def sg_progress_def
                  cbufs_after_loop_updates_def loop_res_def cbufs_after_label_read_input0_def
                  cbufs_after_input_output_def os_after_loop_progress_def os_after_drop_caps_def
                  os_after_loop_updates_def os_after_label_input0_def
                  os_after_label_read_input0_def os_after_input_output_def os_input_after_output_def
                  os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
                  input0_msgs_def BULK_BENQ_def os_inv(1,4) op_state_base_def
                  operator_state.defs obtain_progress_def)
            apply simp
            done
          apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c') (Loc (1 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z")
          defer
          subgoal
            apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                 (Loc (1 :: 3) (Trg (0 :: 2))) = caps' n (Loc 1 (Trg 0))")
            defer
            subgoal
              using c_pts_after_second_progress_caps'[of n \<open>Loc (1 :: 3) (Trg (0 :: 2))\<close>]
              by simp
            apply (subgoal_tac "caps' n (Loc (1 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z")
            defer
            subgoal
              using dt_inv'(2)[of n]
              by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary subgraph_inv(1)
                  sg_first_propa_def sg_progress_def
                  cbufs_after_loop_updates_def loop_res_def cbufs_after_label_read_input0_def
                  cbufs_after_input_output_def os_after_loop_progress_def os_after_drop_caps_def
                  os_after_loop_updates_def os_after_label_input0_def
                  os_after_label_read_input0_def os_after_input_output_def os_input_after_output_def
                  os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
                  input0_msgs_def BULK_BENQ_def os_inv(1,4) op_state_base_def
                  operator_state.defs obtain_progress_def)
            apply simp
            done
          apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c') (Loc (0 :: 3) (Src (0 :: 2))) =
              zmset_of (mset (ocaps (os 0) 0) + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) - event.time `# filter_mset is_Drop (mset (ltaken n lxs)))")
          defer
          subgoal
            apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                 (Loc (0 :: 3) (Src (0 :: 2))) = caps' n (Loc 0 (Src 0))")
            defer
            subgoal
              using c_pts_after_second_progress_caps'[of n \<open>Loc (0 :: 3) (Src (0 :: 2))\<close>]
              by simp
            apply (subgoal_tac "caps' n (Loc (0 :: 3) (Src (0 :: 2))) =
                 zmset_of (mset (ocaps (os 0) 0) + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) - event.time `# filter_mset is_Drop (mset (ltaken n lxs)))")
            defer
            subgoal
              using dt_inv'(1)[of n]
                mset_ocaps_updates[of "ltaken n lxs" "ldropn n lxs" "ocaps (fst (obtain_progress os_input)) (0 :: 2)"]
                input_stream_inv os_inv(1)
              apply (simp add: Src_caps_inv_def input_events_def
                  os_after_loop_progress_def os_after_drop_caps_def
                  os_after_loop_updates_def loop_res_def os_after_label_input0_def
                  os_after_label_read_input0_def os_after_input_output_def os_input_after_output_def
                  os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
                  os_inv(4) op_state_base_def operator_state.defs obtain_progress_def)
              apply (drule arg_cong[where f=zmset_of])
              apply (simp add: to_zmset_correct)
              done
            apply simp
            done
          apply simp
          done
        done
      subgoal
        apply simp
        apply (drule input_frontier_exit_scopeD[of n t])
        subgoal
          using t_live label_prop_inv(4)
          apply (clarsimp del: disjCI simp add: cimage_iff image_iff split_beta split: event.splits)
          apply (elim disjE)
          subgoal
            apply (clarsimp simp add: cin.rep_eq ts_def cset_of_llist.rep_eq split: event.splits)
            subgoal for a b
              by force
            done
          subgoal
            by (force simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
          subgoal
            by auto
          done
        using input_frontier_fresh
        by blast
      done
    done

(* ----------------------------- *)
(* STEPS 14: op 1 flushes outpu 0 buffer with all WCC  *)
  define os_label_after_final_output where
    \<open>os_label_after_final_output = (\<lambda>n. (os_label_after_produces n)\<lparr>outpu :=
      (outpu (os_label_after_produces n))(0 := [])\<rparr>)\<close>

  define os_after_final_output where
    \<open>os_after_final_output = (\<lambda>n. (os_after_label_produces n)
      (1 := op_state_base (os_label_after_final_output n)))\<close>


  have dataplane_after_final_output:
    \<open>dataplane_tracker_inv
      (os_after_final_output n) (cbufs_after_loop_updates n)
      (sg_after_second_propa n)\<close>
    for n
  proof -
    have G_second:
      \<open>graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
        (os_after_second_propa n)\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
          (os_after_second_propa n) =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_second_propa_def os_label_after_second_propa_def
            os_after_increment_progress_def os_after_label_progress_def os_after_ooo_input_progress_def
            os_label_after_label_progress_def os_after_loop_progress_def os_after_drop_caps_def
            op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
      then show ?thesis
        using G_loop[of n]
        by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
            sg_after_label_progress_def sg_after_ooo_input_progress_def)
    qed
    have G_after_label_produces:
      \<open>graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
        (os_after_label_produces n)\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
          (os_after_label_produces n) =
        graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
          (os_after_second_propa n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_label_produces_def os_label_after_produces_def
            os_after_second_propa_def op_state_base_def operator_state.defs drop_caps_def produces_def)
      then show ?thesis
        using G_second by simp
    qed
    have Summ_second:
      \<open>summ (sg_after_second_propa n) = antichain_from_list \<circ>\<circ> raw_summary\<close>
      using subgraph_inv(1)
      by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
          sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    show ?thesis
      apply (rule dataplane_tracker_inv_update_outputs_outside
          [OF dataplane_after_label_produces[of n], where nid=\<open>1 :: 3\<close> and p=\<open>0 :: 2\<close> and xs=Nil])
      apply (simp add: os_after_final_output_def os_label_after_final_output_def
          os_after_label_produces_def op_state_base_def operator_state.defs fun_eq_iff)
      apply (simp add: Summ_second raw_summary_def)
      apply (rule G_after_label_produces)
      done

  qed



  have labels_after_final_output:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_final_output n) t)
      (min_label (os_label_after_final_output n) t)\<close>
    for n
    using labels_after_label_produces[of n]
    by (simp add: os_label_after_final_output_def all_edges_def all_vertices_def min_label_def)

  have ocaps0_after_final_output_mysnd:
    \<open>\<forall>t \<in> set (ocaps (os_after_final_output n 1) (0 :: 2)). mysnd t = 0\<close>
    for n
  proof -
    have intsum_label_input0_10:
      \<open>intsum (os_label_after_input0 n) (1 :: 2) (0 :: 2) = []\<close>
      using Intsum_after_label_input0[of n, rule_format, of 1]
      by (simp add: os_after_label_input0_def op_state_base_def operator_state.defs raw_summary_def)
    have ocaps0_loop:
      \<open>ocaps (os_label_after_loop_updates n) (0 :: 2) = ocaps (os_label_after_input0 n) 0\<close>
      unfolding os_label_after_loop_updates_def loop_res_def
      by (subst ocaps_0_fst_snd_loop_updates) (rule intsum_label_input0_10, simp)
    have intsum_label_first_00:
      \<open>intsum os_label_after_first_propa (0 :: 2) (0 :: 2) = [MyPair 0 0]\<close>
      using os_inv(7)[rule_format, of 1]
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs raw_summary_def)
    have ocaps0_first_mysnd:
      \<open>\<forall>t \<in> set (ocaps os_label_after_first_propa (0 :: 2)). mysnd t = 0\<close>
      using label_prop_inv(4)
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs)
    have input0_msgs_mysnd:
      \<open>\<forall>t \<in> snd ` set (input0_msgs n). mysnd t = 0\<close>
      using label_prop_inv(4) buffers_inv input_stream_inv
      by (force simp add: input0_msgs_def input_data_def input_events_def
          buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def
          os_inv(1) operator_state.defs split: event.splits dest!: setltakenD)
    have ocaps0_read_mysnd:
      \<open>\<forall>t \<in> set (ocaps (os_label_after_read_input0 n) (0 :: 2)). mysnd t = 0\<close>
      using ocaps0_first_mysnd input0_msgs_mysnd intsum_label_first_00
      by (auto simp add: os_label_after_read_input0_def fold_consumes zero_myprod_def split: prod.splits)
    have ocaps0_second_mysnd:
      \<open>\<forall>t \<in> set (ocaps (os_label_after_second_propa n) (0 :: 2)). mysnd t = 0\<close>
      using ocaps0_loop ocaps0_read_mysnd
      by (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
          os_label_after_drop_caps_def os_label_after_input0_def drop_caps_def
          obtain_progress_def operator_state.defs)
    show ?thesis
      using ocaps0_second_mysnd
      by (auto simp add: os_after_final_output_def os_label_after_final_output_def
          os_after_label_produces_def os_label_after_produces_def
          os_after_second_propa_def os_label_after_second_propa_def
          os_label_after_label_progress_def os_label_after_drop_caps_def
          os_after_increment_progress_def os_after_label_progress_def
          os_after_ooo_input_progress_def os_after_loop_progress_def os_after_drop_caps_def
          op_state_base_def operator_state.defs drop_caps_def produces_def obtain_progress_def
          dest!: in_set_list_diffD)
  qed

  have outpu_0_after_final_output_empty:
    \<open>outpu (os_after_final_output n (0 :: 3)) (0 :: 2) = []\<close>
    for n
    by (simp add: os_after_final_output_def os_after_label_produces_def
        os_after_second_propa_def os_after_increment_progress_def
        os_after_label_progress_def os_after_ooo_input_progress_def
        os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
        os_after_label_input0_def os_after_label_read_input0_def
        os_after_input_output_def os_input_after_output_def os_after_input_stream_def
        os_input_after_stream_def os_first_propa_def os_progress_def
        loop_res_def op_state_base_def operator_state.defs obtain_progress_def os_inv(1))

  have labels_stable_after_second_propa_closed:
    \<open>t \<in> set (timestamps (os_label_after_second_propa n)) \<Longrightarrow>
      \<not> frontier_less_equal
        (exit_scope myfst (front (os_label_after_second_propa n) 0 +
          front (os_label_after_second_propa n) 1)) t \<Longrightarrow>
      labels_stable (all_edges (os_label_after_second_propa n) t)
        (min_label (os_label_after_second_propa n) t)\<close>
    for n t
    apply (rule ccontr)
    apply (erule not_labels_stable_covered_witnessE)
    apply (rule label_prop_covered_inv_transportI[OF covered_after_loop_updates[of n], where M'=\<open>{}\<close>])
    apply (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
        os_label_after_drop_caps_def drop_caps_def obtain_progress_def)
    apply (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
        os_label_after_drop_caps_def drop_caps_def obtain_progress_def)
    apply (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
        os_label_after_drop_caps_def drop_caps_def obtain_progress_def)
    apply (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
        os_label_after_drop_caps_def drop_caps_def obtain_progress_def)
    apply (simp add: outpu_1_after_loop_updates_empty
        loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((1 :: 3), (1 :: 2))\<close>]
        loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((2 :: 3), (1 :: 2))\<close>])
    apply assumption
    apply simp
    done


  define final_output where
    \<open>final_output = (\<lambda> n. label_prop_output_batch
                             (drop_caps
                               (fst (snd (loop_updates cbufs
                                           (fst (label_prop_input0_batched
                                                  (CONSUMES 0 (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))
                                                    (CONSUMES 0 (outpu (os 0) 0) (CONSUMES 0 (cbufs (1, 0)) (os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), initia := True\<rparr>))))
                                                  (input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))))
                                           os)))
                               (map (\<lambda>t. Cap t 1)
                                 (ocaps
                                   (fst (snd (loop_updates cbufs
                                               (fst (label_prop_input0_batched
                                                      (CONSUMES 0 (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))
                                                        (CONSUMES 0 (outpu (os 0) 0) (CONSUMES 0 (cbufs (1, 0)) (os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), initia := True\<rparr>))))
                                                      (input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))))
                                               os)))
                                   1))
                              \<lparr>consu := [], inter := [], produ := [], front := frontier \<circ> (\<lambda>p. c_imp (c'' n) (Loc 1 (Trg p))), initia := True\<rparr>)
                             (filter
                               (\<lambda>t. myfst t
                                     \<in> (\<lambda>(d, y). myfst y) `
                                        (set (input (os 1) 0) \<union> (set (cbufs (1, 0)) \<union> (set (outpu (os 0) 0) \<union> case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined) ` {x \<in> set (ltaken n lxs). is_Data x}))) \<or>
                                     myfst t \<in> set (timestamps os_label_prop))
                               (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (frontier (c_imp (c'' n) (Loc 1 (Trg 0))) + frontier (c_imp (c'' n) (Loc 1 (Trg 1))))) (myfst t))
                                 (ocaps
                                   (drop_caps
                                     (fst (snd (loop_updates cbufs
                                                 (fst (label_prop_input0_batched
                                                        (CONSUMES 0 (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))
                                                          (CONSUMES 0 (outpu (os 0) 0) (CONSUMES 0 (cbufs (1, 0)) (os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), initia := True\<rparr>))))
                                                        (input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))))
                                                 os)))
                                     (map (\<lambda>t. Cap t 1)
                                       (ocaps
                                         (fst (snd (loop_updates cbufs
                                                     (fst (label_prop_input0_batched
                                                            (CONSUMES 0 (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))
                                                              (CONSUMES 0 (outpu (os 0) 0) (CONSUMES 0 (cbufs (1, 0)) (os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), initia := True\<rparr>))))
                                                            (input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))))
                                                     os)))
                                         1)))
                                   0))))\<close>

  have label_prop_upd_inv_after_final_output:
    \<open>label_prop_upd_inv (os_label_after_final_output n)\<close>
    for n
    apply (simp add: os_label_after_final_output_def os_label_after_produces_def
        os_label_after_second_propa_def os_label_after_label_progress_def
        os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
    apply (rule label_prop_upd_inv_after_loop_updates)
    done


  have timestamps_after_final_output_eq:
    \<open>timestamps (os_label_after_final_output n) =
      rev (map (\<lambda>(d, t). myfst t) (label_input0_msgs n)) @ timestamps os_label_prop\<close>
    for n
    by (simp add: os_label_after_final_output_def os_label_after_produces_def
        produces_def drop_caps_def os_label_after_second_propa_def
        os_label_after_label_progress_def os_label_after_drop_caps_def obtain_progress_def
        os_label_after_loop_updates_def loop_res_def os_label_after_input0_def
        os_label_after_read_input0_def fold_consumes os_label_after_first_propa_def
        os_inv(4) operator_state.defs)

  have timestamps_after_second_propa_eq:
    \<open>timestamps (os_label_after_second_propa n) =
      rev (map (\<lambda>(d, t). myfst t) (label_input0_msgs n)) @ timestamps os_label_prop\<close>
    for n
    by (simp add: os_label_after_second_propa_def
        os_label_after_label_progress_def os_label_after_drop_caps_def obtain_progress_def
        drop_caps_def os_label_after_loop_updates_def loop_res_def os_label_after_input0_def
        os_label_after_read_input0_def fold_consumes os_label_after_first_propa_def
        os_inv(4) operator_state.defs)

  have ocaps0_after_second_propa_eq:
    \<open>ocaps (os_label_after_second_propa n) (0 :: 2) =
      ocaps (os 1) 0 @ map snd (input0_msgs n)\<close>
    for n
  proof -
    have intsum_label_input0_10:
      \<open>intsum (os_label_after_input0 n) (1 :: 2) (0 :: 2) = []\<close>
      using Intsum_after_label_input0[of n, rule_format, of 1]
      by (simp add: os_after_label_input0_def op_state_base_def operator_state.defs raw_summary_def)
    have ocaps0_loop:
      \<open>ocaps (os_label_after_loop_updates n) (0 :: 2) = ocaps (os_label_after_input0 n) 0\<close>
      unfolding os_label_after_loop_updates_def loop_res_def
      by (subst ocaps_0_fst_snd_loop_updates) (rule intsum_label_input0_10, simp)
    have intsum_label_first_00:
      \<open>intsum os_label_after_first_propa (0 :: 2) (0 :: 2) = [MyPair 0 0]\<close>
      using os_inv(7)[rule_format, of 1]
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs raw_summary_def)
    have concat_single: \<open>concat (map (\<lambda>(d, t). [t]) xs) = map snd xs\<close> for xs :: \<open>('a \<times> 'b) list\<close>
      by (induct xs) auto
    have ocaps0_read:
      \<open>ocaps (os_label_after_read_input0 n) (0 :: 2) = ocaps (os 1) 0 @ map snd (input0_msgs n)\<close>
      using intsum_label_first_00
      by (simp add: os_label_after_read_input0_def fold_consumes os_label_after_first_propa_def
          os_inv(4) operator_state.defs concat_single flip: zero_myprod_def)
    show ?thesis
      using ocaps0_loop ocaps0_read
      by (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
          os_label_after_drop_caps_def os_label_after_input0_def drop_caps_def
          obtain_progress_def operator_state.defs)
  qed

  have ocaps0_after_final_output_set:
    \<open>set (ocaps (os_after_final_output n 1) (0 :: 2)) =
      {t \<in> set (ocaps (os 1) 0) \<union> snd ` set (input0_msgs n).
        frontier_less_equal
          (exit_scope myfst (front (os_label_after_second_propa n) 0 +
            front (os_label_after_second_propa n) 1)) (myfst t) \<or>
        myfst t \<notin> set (timestamps (os_label_after_second_propa n))}\<close>
    for n
  proof -
    have *: \<open>set (ocaps (os_after_final_output n 1) (0 :: 2)) =
      {t \<in> set (ocaps (os_label_after_second_propa n) (0 :: 2)).
        \<not> (\<not> frontier_less_equal
            (exit_scope myfst (front (os_label_after_second_propa n) 0 +
              front (os_label_after_second_propa n) 1)) (myfst t) \<and>
           myfst t \<in> set (timestamps (os_label_after_second_propa n)))}\<close>
      by (simp add: os_after_final_output_def os_label_after_final_output_def
          os_after_label_produces_def os_label_after_produces_def
          label_produces_below_times_def produces_def drop_caps_def
          op_state_base_def operator_state.defs filter_map comp_def capability.sel)
    show ?thesis
      unfolding *
      by (auto simp add: ocaps0_after_second_propa_eq)
  qed

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
              by (simp  del: filter.simps add: image_iff subgraph_inv outputs_at_target_raw_summary csets_inv(2) label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))

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
          using os_inv(10) apply simp
          using buffers_inv(2) apply simp
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
          subgoal
            apply (subst wf_label_prop_updates_cong[where os'=os_label_prop])
            using label_prop_inv(7)
            by (simp_all add: buffers_inv image_Un Un_assoc BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) os_inv(4) operator_state.defs(3))
          subgoal
            using label_prop_inv(8)
            apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def os_inv(4) operator_state.defs(3))
            apply (erule label_prop_covered_inv_transportI)
            apply simp_all
            apply blast
            done
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

(* ----------------------------- *)
(* STEPS 1: op 0 reports progress *)
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

(* ----------------------------- *)
(* STEPS 2: op 1 reads the initial frontier from propagation *)
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

(* ----------------------------- *)
(* STEPS 3: op 0 produces n elements from the input stream *)
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

(* ----------------------------- *)
(* STEPS 4: op 0 flushes the outpu buffer *)
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

(* ----------------------------- *)
(* STEPS 5: op 1 consumes all the data in the channel *)
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

(* ----------------------------- *)
(* STEPS 6: op 1 processes all the new edges in the input 0 *)
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

(* ----------------------------- *)
(* STEPS 7: op 1 loops all the data, and processes everything until the labels converges *)
            apply (rule transitive_closurep_trans'(2))
            apply (rule step_Taus_set_op)
            apply (rule step_Taus_dataflow_op_Taus_intro)
            apply (rule step_star_map_op)
            apply (rule step_comp_op_R_Tau_start)
            apply (rule step_tau_pow_loop_updates_alt)
            apply simp
            subgoal
              unfolding op_state_base_def
              by (simp add: os_inv(7)[rule_format]  operator_state.defs os_inv(4))
            using os_inv(9) apply simp
            using os_inv(8) apply simp
            subgoal
              apply (simp only: CONSUMES_CONSUMES)
              apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI)
              apply (simp add: operator_state.defs os_inv(4) input_CONSUMES)
              apply (simp add:  label_prop_inv(5) input_CONSUMES)
              apply (simp add:  label_prop_inv(5) input_CONSUMES)
              using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified] 
              apply (auto del: disjCI simp add: input_CONSUMES os_inv(4) operator_state.defs wf_label_prop_updates_un)
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
                subgoal
                  apply (simp add:  label_prop_inv(5) input_CONSUMES)
                  using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified] 
                  apply (auto del: disjCI simp add: input_CONSUMES os_inv(4) operator_state.defs wf_label_prop_updates_un)
                  done

                done
              done
            subgoal
              apply (simp only: image_Un set_append set_map flip: Un_assoc)
              apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
                  [where rest=\<open>[]\<close>])
              apply (simp add: os_inv(4) operator_state.defs input_CONSUMES)
              apply (simp add: os_inv(4) operator_state.defs input_CONSUMES)
              apply (simp add: os_inv(4) operator_state.defs input_CONSUMES)
              subgoal
                using label_prop_inv(5)  by simp
              subgoal
                using label_prop_inv(1)  by simp
              subgoal
                apply simp
                using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified] 
                by (simp add: input_CONSUMES os_inv(4) operator_state.defs wf_label_prop_updates_un)
              subgoal
                apply simp
                using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified] 
                apply (auto del: disjCI simp add: split_beta  wf_label_prop_updates_clean_image[unfolded split_beta]  image_iff input_CONSUMES os_inv(4) operator_state.defs wf_label_prop_updates_un split: capability.splits)
                done
              done
            subgoal
              by (simp add:  operator_state.defs os_inv(4))
            subgoal
              by (simp add:  operator_state.defs os_inv(4))
            apply (rule refl)+

(* ----------------------------- *)
(* STEPS 8: op 1 drop all capabilities that may be left *)
            apply (rule transitive_closurep_trans'(2))
            apply (rule step_Taus_set_op)
            apply (rule step_Taus_dataflow_op_Taus_intro)
            apply (rule step_star_map_op)
            apply (rule step_comp_op_R_Tau_start)
            apply (rule step_taus_loop_)
            apply (rule step_star_map_op)
            apply (rule step_comp_op_L_Tau_start)
            apply (rule step_star_map_op)
            apply (rule step_label_propagation_op_drop_caps)
            subgoal
              using input_0_after_loop_updates_empty[of n]
              by (simp add: os_label_after_loop_updates_def loop_res_def
                  cbufs_after_label_read_input0_def cbufs_after_input_output_def
                  os_label_after_input0_def os_label_after_read_input0_def label_input0_msgs_def
                  input0_msgs_def input_data_def input_events_def os_label_after_first_propa_def
                  label_front_after_first_propa_def sg_first_propa_def
                  os_after_label_input0_def os_after_label_read_input0_def
                  os_after_input_output_def os_after_input_stream_def os_first_propa_def os_progress_def
                  os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs input_CONSUMES)

            subgoal
              using input_1_after_loop_updates_empty[of n]
              by (simp add: os_label_after_loop_updates_def loop_res_def
                  cbufs_after_label_read_input0_def cbufs_after_input_output_def
                  os_label_after_input0_def os_label_after_read_input0_def label_input0_msgs_def
                  input0_msgs_def input_data_def input_events_def os_label_after_first_propa_def
                  label_front_after_first_propa_def sg_first_propa_def
                  os_after_label_input0_def os_after_label_read_input0_def
                  os_after_input_output_def os_after_input_stream_def os_first_propa_def os_progress_def
                  os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs input_CONSUMES)


            apply (rule refl)+
            subgoal
              by simp
            apply (rule refl)+

(* ----------------------------- *)
(* STEPS 9: op 0 reports progress again *)
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

(* ----------------------------- *)
(* STEPS 10: op 1 reports progress *)
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

(* ----------------------------- *)
(* STEPS 11: op 2 reports progress *)
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

(* ----------------------------- *)
(* STEPS 12: op 1 reads the new frontier from the propagation *)
            apply (rule converse_rtranclp_into_rtranclp) 
            apply (rule step_set_op_intro_Tau_2)
            apply simp
            apply (rule step_Tau_dataflow_op_Inp_Inl_intro[where ?conf'="c'' n"])
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
            subgoal
              using second_propa(1)[of n, simplified]
              by (simp add: input_data_def os_progress_def input_events_def input0_msgs_def label_input0_msgs_def os_first_propa_def os_input_after_stream_def os_input_after_output_def label_front_after_first_propa_def os_after_input_stream_def os_after_input_output_def os_label_after_first_propa_def os_label_after_read_input0_def os_label_after_input0_def cbufs_after_input_output_def os_after_label_read_input0_def os_after_label_input0_def cbufs_after_label_read_input0_def loop_res_def os_label_after_loop_updates_def sg_progress_def os_after_loop_updates_def os_after_loop_progress_def os_after_drop_caps_def os_label_after_drop_caps_def drop_caps_def second_progress_def sg_first_propa_def os_inv(1,4) op_state_base_def operator_state.defs obtain_progress_def CONSUMES_CONSUMES flip: fold_append change_multiplicities_append_alt)

            apply (rule refl)+
            apply (simp add: flip: fold_append change_multiplicities_append_alt)

(* ----------------------------- *)
(* STEPS 13: op 1 produces all the wcc components from the labels *)
            apply (rule converse_rtranclp_into_rtranclp) 
            apply (rule step_set_op_intro_Tau_2)
            apply simp
            apply (rule step_Tau_dataflow_op_Tau_intro)
            apply (rule step_map_op)
            apply (rule step_comp_op_R_Tau)
            apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
            apply (rule step_map_op)
            apply (rule step_label_propagation_op_output)
            apply (rule refl)+
            apply (simp add: flip: fold_append change_multiplicities_append_alt)
            subgoal       
              unfolding label_prop_output_batch_def
              apply (clarsimp del: disjCI simp add: image_iff filter_empty_conv obtain_progress_def simp flip: fold_append change_multiplicities_append_alt)
              apply (subst ocaps_drop_caps_port_disjoint)
              apply auto
              apply (subst ocaps_0_fst_snd_loop_updates)
              apply simp

              subgoal
                using os_inv(7) by (simp add: operator_state.defs os_inv(4) raw_summary_def)
              subgoal
                apply (rule bexI[of _ t, rotated])
                subgoal
                  using prems(2) apply -
                  apply (clarsimp del: disjCI simp add:  outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                  apply hypsubst_thin
                  subgoal for e
                    apply (cases e; simp)
                    apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)

                    subgoal for v1 v2
                      using stream_move(3)[rule_format, of v1 v2] apply -
                      apply (drule meta_mp)
                      subgoal
                        by (metis cin_code)
                      subgoal
                        apply (rule disjI2)+
                        apply (intro exI[of _ e] impI allI conjI)
                        apply argo
                        using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                        done
                      done
                    done
                  subgoal
                    apply (clarsimp del: disjCI simp add:  outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                    apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)
                    subgoal
                      using label_prop_inv(6)
                        [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of t ] apply -
                      apply (drule meta_mp)
                      subgoal
                        by auto
                      apply (metis zero_myprod_def)
                      done
                    subgoal
                      by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                    subgoal
                      by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                    done
                  subgoal
                    apply (clarsimp del: disjCI)
                    apply (metis UnCI label_prop_inv(4) myprod.collapse)
                    done
                  done
                subgoal
                  apply (intro conjI)
                  subgoal
                    apply (rule no_second_propa_output_frontier[OF stream_move(2)])
                    using prems(2)
                    by (clarsimp del: disjCI simp add: cimage_iff image_iff split_beta split: event.splits)

                  subgoal
                    using prems(2) apply -
                    apply (clarsimp del: disjCI simp add: image_iff cimage_iff split_beta split: event.splits)
                    apply (elim disjE)
                    subgoal
                      apply (clarsimp del: disjCI simp add: ts_def operator_state.defs os_inv(4) split: event.splits) 
                      apply (rule disjI1)
                      subgoal for e
                        apply (cases e; simp)
                        subgoal for tt d
                          apply (cases d; simp)
                          subgoal for v1 v2
                            apply (rule exI[of _ e])
                            apply simp
                            using stream_move(3)[rule_format, of v1 v2] apply -
                            apply (drule meta_mp)
                            subgoal
                              by (meson cin_code)
                            subgoal
                              by simp
                            done
                          done
                        done
                      done
                    subgoal
                      apply (clarsimp del: disjCI simp add: outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) split: event.splits) 
                      subgoal for e
                        apply (cases e; simp)
                        subgoal for l
                          apply (cases l; cases t; simp)
                          apply (metis myprod.sel(1) snd_eqD)
                          done
                        subgoal
                          using os_inv(5)[unfolded ty1_check_def os_inv operator_state.defs, simplified]
                            os_inv(6)[unfolded label_prob_ty2_check_def os_inv operator_state.defs, simplified]
                          by (metis snd_eqD)
                        done
                      done
                    subgoal
                      by (force simp add: os_inv operator_state.defs)
                    done
                  done
                done
              done
            apply (rule refl)+
            apply simp
            apply (rule refl)+
            apply simp
            apply (rule refl)+
            apply simp
            apply (rule refl)+
            apply simp
            apply (rule refl)+
            apply (simp add: obtain_progress_def flip: filter_filter fold_append map_append filter_append change_multiplicities_append_alt)

(* ----------------------------- *)
(* STEPS 14: op 1 flushes outpu 0 buffer with all WCC  *)
            apply (rule relpowp_imp_rtranclp[
                  where n="length (outpu (os 1) 0) + length (final_output n)"]) 
            apply (rule step_set_op_steps_Out_intro[where xs="outpu (os 1) 0 @ map (\<lambda> (d, c). (d, time c)) (final_output n)"  and p="(1, 0)"])
            apply (rule steps_Tau_dataflow_op_steps_Out_intro[where xs="outpu (os 1) 0 @ map (\<lambda> (d, c). (d, time c)) (final_output n)" and nid = 1 and p = 0])
            apply (rule steps_map_op[where xs="map (\<lambda>x. Out (Inr (Inr (1, 0))) (Inr x)) (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))", rotated 2])
            apply (rule steps_comp_op_R_Out[where xs="map Inr (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))" and p="Inr (1, 0)"])
            apply (rule steps_Out_loop_op_intro[where xs="map Inr (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))" and p="Inr (1, 0)"])
            apply (rule steps_map_op[where xs="map (\<lambda>x. Out (Inl (Inr (1, 0))) (Inr x)) (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))" , rotated 2])
            apply (rule steps_comp_op_L_Out[where xs="map Inr (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))"])
            apply (rule steps_map_op[where xs="map (\<lambda>x. Out (Some 0) (Inr x)) (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))", rotated 2])
            apply (rule steps_label_propagation_op_Write_Some[where ys=Nil])
            apply simp
            apply (rule refl)+
            apply (subst outpu_0_fst_snd_loop_updates)
            subgoal
              apply (subst (3) filter_True)
              subgoal
                by (auto simp add: label_prop_output_batch_def final_output_def split_beta comp_def os_inv(4) operator_state.defs)
              apply (rule map_cong)
              subgoal
                by (auto simp add: final_output_def split_beta comp_def os_inv(4) operator_state.defs)
              subgoal
                by simp
              done
            apply (rule refl)+
            apply force
            apply fastforce
            apply (rule refl)+
            apply simp
            apply (rule refl)+
            apply simp
            apply simp
            apply (rule refl)+
            apply simp
            apply (rule refl)+
            apply simp
            apply simp
            apply simp
            apply (rule refl)+

(* ----------------------------- *)
(* STEPS 15: set_op picks the desired WCC  *)
            apply (rule rtranclp.intros(1))
            apply (rule step_set_op_intro_Out)
            apply (rule refl)+
            subgoal
              unfolding final_output_def
              using prems(2) apply -
              apply (clarsimp del: disjCI simp add: cimage_iff)
              apply hypsubst_thin
              apply (rule disjI2)
              apply (rule disjI1)
              apply (intro cBexI[of _ "(Inr (ccs (set (icoll (map (\<lambda>(x, t'). Data t' (projl x)) (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0)) @@- lxs) t) \<union> all_edges os_label_prop (myfst t))), Cap t 0)"])
              apply simp_all
              unfolding label_prop_output_batch_def
              apply (clarsimp del: disjCI simp add: image_iff filter_empty_conv obtain_progress_def simp flip: fold_append change_multiplicities_append_alt)

              apply (rule exI[of _ t])
              apply (intro conjI)
              subgoal
                apply (subst ocaps_drop_caps_port_disjoint)
                apply auto
                apply (subst ocaps_0_fst_snd_loop_updates)
                subgoal
                  using os_inv(7) by (simp add: operator_state.defs os_inv(4) raw_summary_def)
                using prems(2) apply -
                apply (clarsimp del: disjCI simp add:  outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                apply hypsubst_thin
                subgoal for e
                  apply (cases e; simp)
                  apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)

                  subgoal for v1 v2
                    using stream_move(3)[rule_format, of v1 v2] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (metis cin_code)
                    subgoal
                      apply (rule disjI2)+
                      apply (intro exI[of _ e] impI allI conjI)
                      apply argo
                      using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                      done
                    done
                  subgoal for a b
                    using stream_move(3)[rule_format, of a b] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (metis cin_code)
                    subgoal
                      apply (rule disjI2)+
                      apply (intro exI[of _ e] impI allI conjI)
                      apply argo
                      using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                      done
                    done
                  subgoal for a b
                    using stream_move(3)[rule_format, of a b] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (metis cin_code)
                    subgoal
                      apply (rule disjI2)+
                      apply (intro exI[of _ e] impI allI conjI)
                      apply argo
                      using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                      done
                    done
                  subgoal for a b
                    using stream_move(3)[rule_format, of a b] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (metis cin_code)
                    subgoal
                      apply (rule disjI2)+
                      apply (intro exI[of _ e] impI allI conjI)
                      apply argo
                      using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                      done
                    done
                  done
                subgoal
                  apply (clarsimp del: disjCI simp add:  outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                  apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of t ] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of undefined] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of undefined] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of undefined] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  done
                subgoal
                  apply (clarsimp del: disjCI)
                  apply (metis UnCI label_prop_inv(4) myprod.collapse)
                  done
                subgoal
                  apply (subst ocaps_0_fst_snd_loop_updates)
                  subgoal
                    using os_inv(7) by (simp add: operator_state.defs os_inv(4) raw_summary_def)
                  apply (thin_tac "((nid, p), WCC, t) |\<in>| _")
                  apply (clarsimp del: disjCI simp add: outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                  apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of t] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  done
                subgoal
                  apply (subst ocaps_0_fst_snd_loop_updates)
                  subgoal
                    using os_inv(7) by (simp add: operator_state.defs os_inv(4) raw_summary_def)
                  apply (thin_tac "((nid, p), WCC, t) |\<in>| _")
                  apply (clarsimp del: disjCI)
                  apply (rule disjI1)
                  using label_prop_inv(4) os_inv(4)
                  apply (simp add: operator_state.defs)
                  apply (metis UnCI myprod.collapse)
                  done
                done
              subgoal
                by (rule no_second_propa_output_frontier[OF stream_move(2)])
              subgoal
                apply (clarsimp del: disjCI simp add: image_iff cimage_iff split_beta split: event.splits)
                apply (elim disjE)
                subgoal
                  apply (clarsimp del: disjCI simp add: ts_def operator_state.defs os_inv(4) split: event.splits)
                  apply (rule disjI1)
                  subgoal for e
                    apply (cases e; simp)
                    subgoal for tt d
                      apply (cases d; simp)
                      subgoal for v1 v2
                        using stream_move(3)[rule_format, of v1 v2] apply -
                        apply (drule meta_mp)
                        subgoal
                          by (meson cin_code)
                        subgoal
                          apply (rule bexI[of _ "(Inl (v1, v2), tt)"])
                          apply simp
                          apply (simp add: image_iff)
                          apply (rule disjI2)+
                          apply (rule exI[of _ "Data tt (v1, v2)"])
                          apply simp

                          done

                        done
                      done
                    done
                  done
                subgoal
                  apply (clarsimp del: disjCI simp add: outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) split: event.splits)
                  subgoal for e
                    apply (cases e; simp)
                    subgoal for l
                      apply (cases l; cases t; simp)
                      apply (rule disjI1)
                      apply (elim disjE)
                      subgoal for a b x1 x2
                        apply (rule bexI[of _ "(Inl (a, b), MyPair x1 x2)"])
                        apply simp
                        apply simp
                        done
                      subgoal for a b x1 x2
                        apply (rule bexI[of _ "(Inl (a, b), MyPair x1 x2)"])
                        apply simp
                        apply simp
                        done
                      subgoal for a b x1 x2
                        apply (rule bexI[of _ "(Inl (a, b), MyPair x1 x2)"])
                        apply simp
                        apply simp
                        done
                      done
                    subgoal
                      using os_inv(5)[unfolded ty1_check_def os_inv operator_state.defs, simplified]
                        os_inv(6)[unfolded label_prob_ty2_check_def os_inv operator_state.defs, simplified]
                      apply (elim disjE)
                      subgoal
                        apply (rule disjI1)
                        apply (rule bexI[of _ "(e, t)"])
                        apply simp
                        apply simp
                        done
                      subgoal
                        apply (rule disjI1)
                        apply (rule bexI[of _ "(e, t)"])
                        apply simp
                        apply simp
                        done
                      subgoal
                        apply (rule disjI1)
                        apply (rule bexI[of _ "(e, t)"])
                        apply simp
                        apply simp
                        done
                      done
                    done
                  done
                subgoal
                  by (force simp add: os_inv operator_state.defs)
                done
              subgoal
                apply (simp add: operator_state.defs os_inv(4))
                apply (subst Un_commute)
                apply (subst all_edges_fst_label_prop_input0_batched_input_eq)
                subgoal
                  by (simp add: input_CONSUMES)
                subgoal
                  using label_prop_inv(5)
                  apply (simp add: label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def operator_state.defs os_inv(4))
                  apply blast
                  done


                subgoal
                  apply (rule wf_label_prop_updates_subset[where
                        S="set (chns (1, 1) @ map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))"])
                  apply (rule wf_label_prop_updates_os_mono[OF label_prop_inv(7) _ _ _ refl])
                  apply (simp add: os_inv(4) operator_state.defs)
                  apply (simp add: os_inv(4) operator_state.defs)
                  apply (simp add: os_inv(4) operator_state.defs)
                  apply (simp add: input_CONSUMES os_inv(4) operator_state.defs buffers_inv BULK_BENQ_def inputs_at_target_def outputs_at_target_raw_summary subgraph_inv(1))
                  done

                subgoal
                  apply (simp add: split_beta input_CONSUMES)
                  apply (rule sym)
                  apply (subgoal_tac
                      "ccs (all_edges \<lparr>intsum = intsum (os 1), consu = consu (os 1), inter = operator_state.inter (os 1),
                        produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1),
                        ocaps = ocaps (os 1), initia = initia (os 1), en1 = Inl, de1 = projl, is_en1 = isl,
                        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr> (myfst t) \<union>
                      set (icoll (map (\<lambda>(x, t'). Data t' (projl x))
                        (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0)) @@- lxs) t)) =
                     ccs (all_edges \<lparr>intsum = intsum (os 1), consu = consu (os 1), inter = operator_state.inter (os 1),
                        produ = produ (os 1), input = input (os 1), outpu = outpu (os 1),
                        front = frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), ocaps = ocaps (os 1), initia = True,
                        en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr,
                        timestamps = T, graph = G, vertices = V, label = L\<rparr> (myfst t) \<union>
                      (\<Union>x\<in>(set (input (os 1) 0) \<union>
                          (set (cbufs (1, 0)) \<union>
                            (set (outpu (os 0) 0) \<union>
                              case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined) `
                                {x \<in> set (ltaken n lxs). is_Data x}))) \<inter>
                          {x. myfst (snd x) \<le> myfst t}.
                          {projl (fst x), (snd (projl (fst x)), fst (projl (fst x)))}))")
                  subgoal
                    apply simp
                    apply (rule Wcc.components_from_labels_correct)
                    subgoal
                      using labels_after_loop_updates[of n, rule_format, of \<open>myfst t\<close>]
                      apply (simp add: os_label_after_loop_updates_def loop_res_def
                          os_label_after_input0_def)
                      apply (subst (asm) all_edges_fst_label_prop_input0_batched_input_eq)
                      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
                          label_input0_msgs_def input_CONSUMES operator_state.defs os_inv(4))
                      apply (simp add: label_prop_inv(5) os_label_after_read_input0_def
                          os_label_after_first_propa_def input_CONSUMES)
                      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def
                          subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
                      apply (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
                          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
                          all_vertices_def all_edges_def neighbors_def)[1]
                      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
                          label_front_after_first_propa_def
                          os_after_label_input0_def os_after_label_read_input0_def
                          os_after_input_output_def os_input_after_output_def
                          os_after_input_stream_def os_input_after_stream_def
                          os_first_propa_def os_progress_def sg_first_propa_def sg_progress_def
                          cbufs_after_label_read_input0_def cbufs_after_input_output_def
                          input0_msgs_def label_input0_msgs_def input_data_def input_events_def
                          input_CONSUMES os_inv(1,4) operator_state.defs obtain_progress_def
                          split_beta)
                      done
                    subgoal
                      apply (subgoal_tac \<open>labels_stable (all_edges (os_label_after_second_propa n) (myfst t))
                        (min_label (os_label_after_second_propa n) (myfst t))\<close>)
                      prefer 2
                      subgoal
                        apply (rule labels_stable_after_second_propa_closed)
                        subgoal
                          using timely_input_stream_ldropn_no_data_le_if_not_frontier_less_equal[OF input_stream_inv stream_move(1) stream_move(2)]
                          apply (simp add: timestamps_after_second_propa_eq input0_msgs_def label_input0_msgs_def
                              input_data_def input_events_def cimage_iff cin.rep_eq ts_def cset_of_llist.rep_eq
                              buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1)
                              inputs_at_target_def in_lset_ltaken_ldropn
                              del: label_propagation_op_logic_front_initia
                              ooo_input_op_logic_front_initia increment_op_logic_front_initia
                              operator_state_front_initia_upd_collapse split: event.splits)
                          apply (elim disjE)
                          subgoal
                            apply (simp add: image_iff in_lset_ltaken_ldropn)
                            apply (erule exE)
                            apply (rule disjI1)
                            apply (rule_tac x=x in exI)
                            apply simp
                            apply (case_tac x)
                            apply simp_all
                            by (metis in_lset_ltaken_ldropn order_refl)
                          subgoal
                            by auto
                          subgoal
                            apply (erule cBexE)
                            using os_inv(4)
                            by (auto simp add: operator_state.defs)
                          done
                        subgoal
                          apply (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
                              os_label_after_drop_caps_def label_front_after_second_propa_def drop_caps_def
                              obtain_progress_def operator_state.defs)
                          apply (rule no_second_propa_output_frontier[OF stream_move(2)])
                          using os_inv(4)
                          by (auto simp add: operator_state.defs)
                        done
                      apply (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
                          os_label_after_drop_caps_def drop_caps_def obtain_progress_def
                          os_label_after_loop_updates_def loop_res_def os_label_after_input0_def)
                      apply (subst (asm) all_edges_fst_label_prop_input0_batched_input_eq)
                      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
                          label_input0_msgs_def input_CONSUMES operator_state.defs os_inv(4))
                      apply (simp add: label_prop_inv(5) os_label_after_read_input0_def
                          os_label_after_first_propa_def input_CONSUMES)
                      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def
                          subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
                      apply (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
                          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
                          all_vertices_def all_edges_def neighbors_def)[1]
                      apply (simp add: all_edges_def all_vertices_def neighbors_def
                          os_label_after_read_input0_def os_label_after_first_propa_def
                          label_front_after_first_propa_def
                          os_after_label_input0_def os_after_label_read_input0_def
                          os_after_input_output_def os_input_after_output_def
                          os_after_input_stream_def os_input_after_stream_def
                          os_first_propa_def os_progress_def sg_first_propa_def sg_progress_def
                          cbufs_after_label_read_input0_def cbufs_after_input_output_def
                          input0_msgs_def label_input0_msgs_def input_data_def input_events_def
                          input_CONSUMES os_inv(1,4) operator_state.defs split_beta)
                      done
                    done



                  subgoal premises prems
                    apply (subst set_icoll_lshift)
                    subgoal
                      using input_stream_inv timely_input_stream_expires_le by blast
                    apply (subst (2) set_icoll_ltaken_if_no_ldropn_data_le[where n=n])
                    subgoal
                      using timely_input_stream_expires_le[OF timely_input_stream_ldrop[OF stream_move(1) input_stream_inv]] by blast
                    subgoal
                      using timely_input_stream_ldropn_no_data_le_if_not_frontier_less_equal[OF input_stream_inv stream_move(1) stream_move(2)] by blast
                    apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary
                        subgraph_inv(1) inputs_at_target_def set_icoll_llist_of)
                    apply (simp add: all_edges_def all_vertices_def neighbors_def)
                    apply (rule label_prop_collected_edge_payloads_ccs_eq)
                    subgoal
                      using label_prop_inv(4)
                      by (force simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary
                          subgraph_inv(1) inputs_at_target_def)
                    subgoal
                      using label_prop_inv(4)
                      by (force dest!: setltakenD)
                    subgoal
                      using prems(1) label_prop_inv(4)
                      by (force simp add: cimage_iff cin.rep_eq ts_def cset_of_llist.rep_eq
                          buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1)
                          inputs_at_target_def split: event.splits dest!: setltakenD)
                    done
                  done

                done

              subgoal
                apply (elim disjE)
                subgoal
                  apply (erule ts_lsetE)
                  subgoal for d
                    using label_prop_inv(4)
                    apply (drule_tac x=t in bspec)
                    apply (rule UnI1)
                    apply (rule UnI1)
                    apply (rule image_eqI[where x=\<open>Data t d\<close>])
                    apply simp
                    apply simp
                    by (cases t; simp)
                  done
                subgoal
                  apply (erule cBexE)
                  subgoal for x
                    using label_prop_inv(4)
                    apply (drule_tac x=\<open>snd x\<close> in bspec)
                    apply (rule UnI1)
                    apply (rule UnI2)
                    apply (rule image_eqI[where x=x])
                    apply simp
                    apply (simp add: in_cset_from_list buffers_inv)
                    by (cases \<open>snd x\<close>; simp)
                  done
                subgoal
                  apply (erule cBexE)
                  by simp
                done
              done

            subgoal
              using prems(1) by assumption
            apply (rule refl)+


            subgoal
              apply (rule wb_upto_b_sym)
              apply (rule wb_upto_b_base)
              apply (unfold R_def[simplified])
              apply (rule exI[of _ "cUn (Pair (1, 0) |`| cset_from_list (outpu (os 1) 0 @ map  (\<lambda> (d, c). (d, time c)) (final_output n))) S"])
              apply (rule exI[of _ "cinsert ((nid, p), WCC, t) D"])
              apply (rule exI[of _ "ldropn n lxs"])
              apply (rule exI[of _ "os_after_final_output n"])
              apply (rule exI[of _ "os_label_after_final_output n"])
              apply (rule exI[of _ "cbufs((1, 0) := Nil, (1, 1) := Nil, (2, 1) := Nil)"])
              apply (rule exI[of _ "sg_after_second_propa n"])
              apply (intro conjI)
              subgoal
                apply (rule arg_cong3[where f=set_op])
                apply (rule refl)
                apply (rule refl)
                apply (rule arg_cong2[where f=dataflow_op])
                subgoal
                  by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
                      sg_after_label_progress_def sg_after_ooo_input_progress_def
                      sg_first_propa_def sg_progress_def)
                subgoal
                  apply (subst dataflow_tree_to_operator_def)
                  apply (simp only: dataflow_tree_to_operator_aux.simps Let_def prod.case
                      fst_conv snd_conv add_0 one_add_one diff_zero)
                  apply (rule arg_cong[where f=\<open>map_op (case_sum id id) (case_sum id id)\<close>])
                  apply (rule comp_op_buf_cong)
                  subgoal
                    by (auto simp add: fun_eq_iff split: sum.splits)
                  subgoal
                    apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                    apply (rule arg_cong[where f=\<open>ooo_input_op _\<close>])
                    by (simp add: os_after_final_output_def os_after_label_produces_def
                        os_after_second_propa_def os_after_increment_progress_def
                        os_after_label_progress_def os_after_ooo_input_progress_def
                        os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
                        os_after_label_input0_def os_after_label_read_input0_def
                        os_after_input_output_def os_input_after_output_def os_after_input_stream_def
                        os_input_after_stream_def os_first_propa_def os_progress_def input_events_def
                        input_data_def loop_res_def op_state_base_def operator_state.defs
                        obtain_progress_def os_inv(1,4))
                  subgoal
                    apply (rule loop_op_buf_cong)
                    subgoal
                      by (auto simp add: fun_eq_iff eq_diff_eq one_add_one split: sum.splits)
                    subgoal
                      apply (rule arg_cong[where f=\<open>map_op (case_sum id id) (case_sum id id)\<close>])
                      apply (rule comp_op_buf_cong)
                      subgoal
                        by (auto simp add: fun_eq_iff eq_diff_eq split: sum.splits)
                      subgoal
                        apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                        apply (rule arg_cong[where f=label_propagation_op])
                        by (simp add: os_label_after_final_output_def
                            os_label_after_produces_def label_produces_batch_def
                            label_produces_below_times_def os_label_after_second_propa_def
                            label_front_after_second_propa_def os_label_after_label_progress_def
                            os_label_after_drop_caps_def os_label_after_loop_updates_def
                            loop_res_def os_label_after_input0_def label_input0_msgs_def
                            os_label_after_read_input0_def input0_msgs_def input_data_def
                            input_events_def os_label_after_first_propa_def
                            label_front_after_first_propa_def sg_first_propa_def
                            sg_progress_def cbufs_after_label_read_input0_def
                            cbufs_after_input_output_def os_after_label_input0_def
                            os_after_label_read_input0_def os_after_input_output_def
                            os_after_input_stream_def os_first_propa_def os_progress_def
                            obtain_progress_def CONSUMES_CONSUMES image_Un image_image
                            Un_ac disj_ac flip: fold_append)
                      subgoal
                        apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                        apply (rule arg_cong[where f=\<open>increment_op _ _ _\<close>])
                        apply (simp add: os_after_final_output_def os_after_label_produces_def
                            os_after_second_propa_def os_after_increment_progress_def
                            os_after_label_progress_def os_after_ooo_input_progress_def
                            os_after_loop_progress_def os_after_drop_caps_def
                            os_after_loop_updates_def loop_res_def)
                        apply (simp add: os_after_label_input0_def os_after_label_read_input0_def
                            os_after_input_output_def os_after_input_stream_def
                            os_first_propa_def os_progress_def
                            cbufs_after_label_read_input0_def cbufs_after_input_output_def
                            snd_snd_loop_updates_cbufs_irrelevant2)
                        apply (rule trans[of _ \<open>snd (snd (loop_updates cbufs
                            (os_label_after_input0 n) os)) 2
                            \<lparr>consu := [], inter := [], produ := []\<rparr>\<close>])
                        subgoal
                          by (rule operator_state_eqI)
                            (simp_all add: op_state_base_def obtain_progress_def)
                        apply (rule arg_cong[where
                              f=\<open>\<lambda>x. x\<lparr>consu := [], inter := [], produ := []\<rparr>\<close>])
                        apply (rule arg_cong[where
                              f=\<open>\<lambda>l. snd (snd (loop_updates cbufs l os)) 2\<close>])
                        apply (simp add: os_label_after_input0_def label_input0_msgs_def
                            os_label_after_read_input0_def input0_msgs_def input_data_def
                            input_events_def os_label_after_first_propa_def
                            label_front_after_first_propa_def sg_first_propa_def
                            sg_progress_def CONSUMES_CONSUMES flip: fold_append)
                        done
                      subgoal
                        apply (rule ballI)
                        apply (erule IntE)
                        apply (thin_tac \<open>p \<in> inputs X\<close> for p X)
                        apply (case_tac p)
                        apply simp
                        apply (clarsimp split: prod.splits if_splits)
                        apply (clarsimp simp add: ran_def)
                        apply (rename_tac x)
                        apply (case_tac x)
                        apply simp
                        apply (clarsimp split: prod.splits if_splits)
                        done
                      done
                    subgoal
                      apply (rule ballI)
                      apply (erule IntE)
                      apply (thin_tac \<open>p \<in> inputs X\<close> for p X)
                      apply (case_tac p)
                      apply simp
                      apply (clarsimp split: prod.splits if_splits)
                      apply (clarsimp simp add: ran_def)
                      apply (rename_tac x)
                      apply (case_tac x)
                      apply simp
                      apply (clarsimp split: prod.splits if_splits)
                      done
                    done
                  subgoal
                    apply (rule ballI)
                    apply (erule IntE)
                    apply (thin_tac \<open>p \<in> inputs X\<close> for p X)
                    apply (case_tac p)
                    apply simp
                    apply (clarsimp split: prod.splits if_splits)
                    apply (clarsimp simp add: ran_def)
                    apply (rename_tac x)
                    apply (case_tac x)
                    apply simp
                    apply (clarsimp split: prod.splits if_splits)
                    done
                  done
                done
              subgoal (* TIP 1: this reduces to cset equality. TIP 2: You probably want to do a case distinction if the given arbitrary t is frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t) or not *)
                apply (rule arg_cong2[where f=set_spec_op, OF _ refl])
                apply (subgoal_tac \<open>outpu (os_after_final_output n 1) (0 :: 2) = []\<close>)
                prefer 2
                subgoal
                  by (simp add: os_after_final_output_def os_label_after_final_output_def
                      op_state_base_def operator_state.defs)
                apply (subgoal_tac \<open>input (os_after_final_output n 1) (0 :: 2) = []\<close>)
                prefer 2
                subgoal
                  using input_0_after_loop_updates_empty[of n]
                  by (simp add: os_after_final_output_def os_label_after_final_output_def
                      os_after_label_produces_def os_label_after_produces_def
                      os_after_second_propa_def os_label_after_second_propa_def
                      os_label_after_label_progress_def os_label_after_drop_caps_def
                      drop_caps_def op_state_base_def operator_state.defs produces_def
                      obtain_progress_def)
                apply simp
                  (* Remaining goal (after killing outpu-after and splitting the @):
                     cUn (cUn S OutOld) SPold
                   = cUn (cUn (Pair (1,0) |`| cUn OutOld' FinalImg) S) SPnew
                   where FinalImg = (\<lambda>(d,c). (d, time c)) |`| cset_from_list (final_output n).
                   Plan: hoist (a) the ccs payload equality (\<forall>t0 with mysnd t0 = 0) and
                   (b) labels_stable for timestamps closed at the SECOND-PROPA frontier;
                   then extensional via cset_eq_iff, case-splitting on the second-propa
                   (c'') frontier — NOT the old front (os 1) — because
                   label_produces_below_times/final_output filter on the c'' frontier:
                   - fle-new (live): x \<in> SPold \<longleftrightarrow> x \<in> SPnew (caps survive the produces
                     drop by ocaps0_after_final_output_set; FinalImg contradicts fle-new);
                   - \<not>fle-new (closed): SPnew index excludes t0 (cap dropped + ldropn
                     expired), so x \<in> SPold \<longleftrightarrow> x \<in> Pair (1,0) |`| FinalImg via (b). *)
                apply (subgoal_tac \<open>\<forall>t0 :: (nat, nat) myprod. mysnd t0 = 0 \<longrightarrow>
                    ccs (set (icoll (map (\<lambda>(x, t'). Data t' (projl x))
                          (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0)) @@- lxs) t0) \<union>
                        all_edges os_label_prop (myfst t0)) =
                    ccs (set (icoll (map (\<lambda>(x, t'). Data t' (projl x))
                          (((outputs_at_target (summ (sg_after_second_propa n)) (os_after_final_output n) >>
                             cbufs((1, 0) := [], (1, 1) := [], (2, 1) := [])) >>
                            inputs_at_target (os_after_final_output n)) (1, 0)) @@- ldropn n lxs) t0) \<union>
                        all_edges (os_label_after_final_output n) (myfst t0))\<close>)
                prefer 2
                subgoal
                  apply (intro allI impI)
                  apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                      os_label_after_second_propa_def os_label_after_label_progress_def
                      os_label_after_drop_caps_def os_label_after_loop_updates_def loop_res_def
                      label_produces_batch_def label_produces_below_times_def
                      drop_caps_def produces_def obtain_progress_def)
                  apply (subst set_icoll_lshift)
                  subgoal
                    using input_stream_inv timely_input_stream_expires_le by blast
                  apply (simp add: outputs_at_target_raw_summary inputs_at_target_def
                      buffers_inv BULK_BENQ_def subgraph_inv(1) set_icoll_llist_of)
                  apply (simp only: os_label_after_input0_def)
                  apply (simp only: os_label_after_read_input0_def os_label_after_first_propa_def)
                  apply (simp only: label_input0_msgs_def input0_msgs_def input_data_def input_events_def)
                  apply (simp add: input_CONSUMES)
                  apply (subst all_edges_fst_label_prop_input0_batched_input_eq)
                  apply (simp add: input_CONSUMES label_prop_inv(5) label_prop_upd_inv_def
                      operator_state.defs os_inv(4,7))
                  using label_prop_inv(5)
                  apply (simp add: label_prop_upd_inv_def input_CONSUMES
                      operator_state.defs os_inv(4,7) all_edges_def all_vertices_def neighbors_def)
                  apply metis
                  using label_prop_inv(7)
                    [unfolded inputs_at_target_def buffers_inv BULK_BENQ_def
                      subgraph_inv outputs_at_target_raw_summary operator_state.defs,
                      simplified]
                  apply (auto simp add: os_inv(4) operator_state.defs input_CONSUMES
                      wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def)[1]
                  apply (simp add: all_edges_def all_vertices_def neighbors_def)
                  apply (subst set_icoll_lshift)
                  subgoal
                    using timely_input_stream_expires_le[OF timely_input_stream_ldrop[OF stream_move(1) input_stream_inv]] by blast
                  apply (simp add: set_icoll_llist_of)
                  apply (subst set_icoll_ltaken_ldropn[where n=n])
                  subgoal
                    using timely_input_stream_expires_le[OF timely_input_stream_ldrop[OF stream_move(1) input_stream_inv]] by blast
                  subgoal
                    apply (simp add: sg_after_second_propa_def sg_after_increment_progress_def
                        sg_after_label_progress_def sg_after_ooo_input_progress_def
                        sg_first_propa_def sg_progress_def outputs_at_target_raw_summary
                        subgraph_inv(1) outpu_0_after_final_output_empty)
                    apply (rule label_prop_collected_edge_payloads_ccs_eq_ldropn)
                    subgoal
                      using label_prop_inv(4)
                      by (force simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary
                          subgraph_inv(1) inputs_at_target_def)
                    subgoal
                      using label_prop_inv(4)
                      by (force dest!: setltakenD)
                    subgoal
                      by simp
                    subgoal
                      by (simp add: os_inv(4) operator_state.defs)
                    done
                  done
                apply (subgoal_tac \<open>\<forall>t \<in> set (timestamps (os_label_after_second_propa n)).
                    \<not> frontier_less_equal (exit_scope myfst (front (os_label_after_second_propa n) 0 +
                      front (os_label_after_second_propa n) 1)) t \<longrightarrow>
                    labels_stable (all_edges (os_label_after_second_propa n) t)
                      (min_label (os_label_after_second_propa n) t)\<close>)
                prefer 2
                subgoal
                  using labels_stable_after_second_propa_closed by blast
                apply (simp only: cset_eq_iff)
                apply (rule allI)
                subgoal for x
                  apply (case_tac \<open>frontier_less_equal
                      (exit_scope myfst (front (os_label_after_second_propa n) 0 +
                        front (os_label_after_second_propa n) 1))
                      (myfst (snd (snd x)))\<close>)
                  subgoal (* live at the new (second-propa) frontier: x \<in> SPold \<longleftrightarrow> x \<in> SPnew *)
                    apply (clarsimp simp flip: cin.rep_eq simp add: image_iff)
                    apply (rule iffI)
                    apply (elim disjE)
                    apply simp
                    subgoal (* x \<in> OutOld \<Longrightarrow> x \<in> Pair(1,0)`(OutOld \<union> FinalImg) *)
                      by (force simp flip: cin.rep_eq
                          simp add: cset_from_list_def cset_of_llist.rep_eq image_iff)
                    subgoal (* x \<in> SPold \<Longrightarrow> x \<in> SPnew *)
                      apply (rule disjI2)+
                      apply (clarsimp simp flip: cin.rep_eq
                          simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                      apply (subst cimage_iff)
                      apply (rename_tac t0)
                      apply (subgoal_tac \<open>mysnd t0 = 0\<close>)
                      prefer 2
                      subgoal
                        apply (thin_tac \<open>\<forall>t0. mysnd t0 = 0 \<longrightarrow> P t0\<close> for P)
                        apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                        apply (thin_tac \<open>x = y\<close> for y)
                        apply (elim disjE)
                        subgoal
                          apply (clarsimp simp add: ts_def cin.rep_eq cset_of_llist.rep_eq
                              image_iff simp del: label_propagation_op_logic_front_initia
                              ooo_input_op_logic_front_initia increment_op_logic_front_initia
                              operator_state_front_initia_upd_collapse split: event.splits)
                          apply (case_tac x)
                          prefer 2
                          subgoal by clarsimp
                          prefer 2
                          subgoal by clarsimp
                          apply clarsimp
                          using label_prop_inv(4)
                          by (metis (mono_tags, lifting) UnCI event.sel(1) imageI)
                        subgoal
                          using label_prop_inv(4)[unfolded buffers_inv]
                          by (fastforce simp flip: cin.rep_eq
                              simp add: cset_of_llist.rep_eq cset_from_list_def image_iff)
                        subgoal
                          by clarsimp
                        done
                      apply (rule_tac x=t0 in cBexI)
                      apply simp
                      apply (subgoal_tac \<open>(((outputs_at_target (summ (sg_after_second_propa n)) (os_after_final_output n) >>
                             cbufs((1, 0) := [], (1, 1) := [], (2, 1) := [])) >>
                            inputs_at_target (os_after_final_output n)) (1, 0)) = []\<close>)
                      prefer 2
                      subgoal
                        by (simp add: outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def
                            inputs_at_target_def sg_after_second_propa_def sg_after_increment_progress_def
                            sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def
                            sg_progress_def outpu_0_after_final_output_empty)
                      apply (subgoal_tac \<open>\<forall>d t'. (d, t') \<in> set (input (os 1) (0 :: 2)) \<longrightarrow>
                           t' \<in> set (ocaps (os 1) (0 :: 2))\<close>)
                      prefer 2
                      subgoal
                        using label_prop_inv(6)[unfolded input_ocaps_inv_def, rule_format]
                          os_inv(7)[rule_format, of 1]
                        by (fastforce simp add: raw_summary_def zero_myprod_def[symmetric]
                            simp del: label_propagation_op_logic_front_initia
                            ooo_input_op_logic_front_initia increment_op_logic_front_initia
                            operator_state_front_initia_upd_collapse)
                      apply (elim disjE)
                      subgoal for t0 (* t0 \<in> ts lxs *)
                        apply (clarsimp simp flip: cin.rep_eq
                            simp add: image_iff cset_from_list_def cset_of_llist.rep_eq ts_def
                            split: event.splits)
                        apply (rename_tac y)
                        apply (simp add: BULK_BENQ_def)
                        apply (case_tac y)
                        prefer 2
                        subgoal by clarsimp
                        prefer 2
                        subgoal by clarsimp
                        apply clarsimp
                        subgoal for a b
                          apply (subgoal_tac \<open>Data t0 (a, b) \<in> set (ltaken n lxs) \<or>
                               Data t0 (a, b) \<in> lset (ldropn n lxs)\<close>)
                          prefer 2
                          subgoal
                              by (simp add: cin.rep_eq cset_of_llist.rep_eq
                                in_lset_ltaken_ldropn[symmetric]
                                del: label_propagation_op_logic_front_initia
                                ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                operator_state_front_initia_upd_collapse)
                          apply (erule disjE)
                          prefer 2
                          subgoal
                            apply (drule_tac x=\<open>Data t0 (a, b)\<close> in spec)
                            by (clarsimp simp add: cin.rep_eq cset_of_llist.rep_eq
                                simp del: label_propagation_op_logic_front_initia
                                ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                operator_state_front_initia_upd_collapse)
                          apply (subgoal_tac \<open>t0 \<in> set (ocaps (os_after_final_output n 1) (0 :: 2))\<close>)
                          prefer 2
                          subgoal
                            apply (simp only: ocaps0_after_final_output_set mem_Collect_eq Un_iff)
                            apply (rule conjI)
                            subgoal
                              apply (rule disjI2)
                              apply (simp only: input0_msgs_def input_data_def input_events_def
                                  set_append set_map image_Un Un_iff)
                              apply (rule disjI2, rule disjI2)
                              apply (rule image_eqI[where x=\<open>(Inl (a, b), t0)\<close>])
                              apply simp
                              apply (rule image_eqI[where x=\<open>Data t0 (a, b)\<close>])
                              apply simp
                              by simp
                            subgoal
                              by simp
                            done
                          apply (subgoal_tac \<open>myfst t0 \<in> set (timestamps (os_label_after_final_output n))\<close>)
                          prefer 2
                          subgoal
                            apply (simp only: timestamps_after_final_output_eq set_append set_rev
                                set_map Un_iff)
                            apply (rule disjI1)
                            apply (rule image_eqI[where x=\<open>(Inl (a, b), t0)\<close>])
                            apply simp
                            apply (simp only: label_input0_msgs_def input0_msgs_def input_data_def
                                input_events_def set_append set_map Un_iff)
                            apply (rule disjI2, rule disjI2, rule disjI2)
                            apply (rule image_eqI[where x=\<open>Data t0 (a, b)\<close>])
                            apply simp
                            by simp
                          apply (metis myprod.collapse)
                          done
                        done
                      subgoal for t0 (* t0 \<in> old buffer times *)
                        apply (clarsimp simp flip: cin.rep_eq
                            simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                        subgoal for a
                          apply (simp add: BULK_BENQ_def)
                          apply (subgoal_tac \<open>t0 \<in> set (ocaps (os_after_final_output n 1) (0 :: 2))\<close>)
                          prefer 2
                          subgoal
                            apply (simp only: ocaps0_after_final_output_set mem_Collect_eq Un_iff)
                            apply (rule conjI)
                            subgoal
                              apply (elim disjE)
                              subgoal (* input buffer: cap via input_ocaps_inv *)
                                apply (rule disjI1)
                                apply (subgoal_tac \<open>(a, t0) \<in> set (input (os 1) (0 :: 2))\<close>)
                                prefer 2
                                subgoal by (simp add: inputs_at_target_def)
                                by blast
                              subgoal (* cbufs part *)
                                apply (rule disjI2)
                                apply (simp only: input0_msgs_def set_append set_map image_Un Un_iff)
                                apply (rule disjI1)
                                apply (rule image_eqI[where x=\<open>(a, t0)\<close>])
                                apply simp
                                by simp
                              subgoal (* outpu part *)
                                apply (rule disjI2)
                                apply (simp only: input0_msgs_def set_append set_map image_Un Un_iff)
                                apply (rule disjI2, rule disjI1)
                                apply (rule image_eqI[where x=\<open>(a, t0)\<close>])
                                apply simp
                                by (simp add: outputs_at_target_raw_summary subgraph_inv(1))
                              done
                            subgoal
                              by simp
                            done
                          apply (subgoal_tac \<open>myfst t0 \<in> set (timestamps (os_label_after_final_output n))\<close>)
                          prefer 2
                          subgoal
                            apply (simp only: timestamps_after_final_output_eq set_append set_rev
                                set_map Un_iff)
                            apply (rule disjI1)
                            apply (rule image_eqI[where x=\<open>(a, t0)\<close>])
                            apply simp
                            apply (simp only: label_input0_msgs_def input0_msgs_def set_append Un_iff)
                            apply (elim disjE)
                            apply (simp add: inputs_at_target_def)
                            apply simp
                            by (simp add: outputs_at_target_raw_summary subgraph_inv(1))
                          apply (metis myprod.collapse)
                          done
                        done
                      subgoal (* t0 \<in> MyPair-filter of old timestamps/ocaps *)
                        by (force simp flip: cin.rep_eq
                            simp add: image_iff cset_from_list_def cset_of_llist.rep_eq
                            timestamps_after_final_output_eq timestamps_after_second_propa_eq
                            ocaps0_after_final_output_set)
                      done
                    subgoal (* reverse direction: RHS \<Longrightarrow> LHS *)
                      apply (clarsimp simp flip: cin.rep_eq
                          simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                      apply (elim disjE)
                      subgoal (* Pair`(OutOld \<union> FinalImg): OutOld direct; FinalImg contradicts fle-new *)
                        apply (clarsimp simp flip: cin.rep_eq
                            simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                        apply (subgoal_tac \<open>\<forall>p. front (os_label_after_second_propa n) p =
                             frontier (c_imp (c'' n) (Loc 1 (Trg p)))\<close>)
                        prefer 2
                        subgoal
                          by (simp add: os_label_after_second_propa_def
                              label_front_after_second_propa_def)
                        by (clarsimp simp add: final_output_def label_prop_output_batch_def
                            image_iff)
                      subgoal (* x \<in> SPnew \<Longrightarrow> contradiction with \<not> x \<in> SPold *)
                        apply (clarsimp simp flip: cin.rep_eq
                            simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                        subgoal for xa
                          apply (subgoal_tac \<open>(((outputs_at_target (summ (sg_after_second_propa n)) (os_after_final_output n) >>
                                 cbufs((1, 0) := [], (1, 1) := [], (2, 1) := [])) >>
                                inputs_at_target (os_after_final_output n)) (1, 0)) = []\<close>)
                          prefer 2
                          subgoal
                              by (simp add: outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def
                                inputs_at_target_def sg_after_second_propa_def sg_after_increment_progress_def
                                sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def
                                sg_progress_def outpu_0_after_final_output_empty
                                del: label_propagation_op_logic_front_initia
                                ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                operator_state_front_initia_upd_collapse)
                          apply (subgoal_tac \<open>mysnd xa = 0\<close>)
                          prefer 2
                          subgoal
                            apply (thin_tac \<open>\<forall>t0. mysnd t0 = 0 \<longrightarrow> P t0\<close> for P)
                            apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                            apply (thin_tac \<open>x = y\<close> for y)
                            apply (thin_tac \<open>\<not> x' |\<in>| A\<close> for x' A)+
                            apply (elim disjE)
                            subgoal
                              apply (clarsimp simp add: ts_def cin.rep_eq cset_of_llist.rep_eq
                                  image_iff simp del: label_propagation_op_logic_front_initia
                                  ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                  operator_state_front_initia_upd_collapse split: event.splits)
                              apply (rename_tac ev)
                              apply (case_tac ev)
                              prefer 2
                              subgoal by clarsimp
                              prefer 2
                              subgoal by clarsimp
                              apply clarsimp
                              subgoal for a b
                                apply (subgoal_tac \<open>Data xa (a, b) \<in> lset lxs\<close>)
                                prefer 2
                                subgoal
                                  by (simp add: in_lset_ltaken_ldropn[of _ lxs n])
                                using label_prop_inv(4)
                                by (metis (mono_tags, lifting) UnCI event.sel(1) imageI)
                              done
                            subgoal
                            by (simp add: BULK_BENQ_def cin.rep_eq cimage.rep_eq
                                  cset_of_llist.rep_eq
                                  del: label_propagation_op_logic_front_initia
                                  ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                  operator_state_front_initia_upd_collapse)
                            subgoal
                              by clarsimp
                            done
                          apply (thin_tac \<open>\<not> x' |\<in>| S\<close> for x')
                          apply (erule notE)
                          apply (subst cimage_iff)
                          apply (rule_tac x=xa in cBexI)
                          subgoal
                            by (simp add: BULK_BENQ_def)
                          apply (elim disjE)
                          subgoal (* xa \<in> ts (ldropn n lxs) \<Longrightarrow> xa \<in> ts lxs *)
                            apply (thin_tac \<open>\<forall>t0. mysnd t0 = 0 \<longrightarrow> P t0\<close> for P)
                            apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                            apply (thin_tac \<open>x = y\<close> for y)
                            apply (clarsimp simp flip: cin.rep_eq
                                simp add: image_iff cset_from_list_def cset_of_llist.rep_eq ts_def
                                split: event.splits)
                            apply (rename_tac ev)
                            apply (case_tac ev)
                            prefer 2
                            subgoal by clarsimp
                            prefer 2
                            subgoal by clarsimp
                            apply clarsimp
                            subgoal for a b
                              apply (subgoal_tac \<open>Data xa (a, b) \<in> lset lxs\<close>)
                              prefer 2
                              subgoal
                                  by (simp add: cin.rep_eq cset_of_llist.rep_eq
                                    in_lset_ltaken_ldropn[of _ lxs n]
                                    del: label_propagation_op_logic_front_initia
                                    ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                    operator_state_front_initia_upd_collapse)
                              apply (drule_tac x=\<open>Data xa (a, b)\<close> in spec)
                              by (clarsimp simp add: cin.rep_eq cset_of_llist.rep_eq
                                  simp del: label_propagation_op_logic_front_initia
                                  ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                  operator_state_front_initia_upd_collapse)
                            done
                          subgoal (* xa \<in> times of the emptied new buffers *)
                              by (simp add: BULK_BENQ_def cin.rep_eq cimage.rep_eq
                                cset_of_llist.rep_eq
                                del: label_propagation_op_logic_front_initia
                                ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                operator_state_front_initia_upd_collapse)
                          subgoal (* MyPair-filter-new \<Longrightarrow> index-old *)
                            apply (thin_tac \<open>\<forall>t0. mysnd t0 = 0 \<longrightarrow> P t0\<close> for P)
                            apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                            apply (thin_tac \<open>x = y\<close> for y)
                            apply (elim exE conjE bexE)
                            apply (subst (asm) ocaps0_after_final_output_set)
                            apply (subst (asm) timestamps_after_final_output_eq)
                            apply clarsimp
                            subgoal for x'
                              apply (erule disjE)
                              subgoal (* y = myfst of a consumed message *)
                                apply (thin_tac \<open>x' \<in> A \<or> x' \<in> B\<close> for A B)
                                apply (clarsimp simp add: image_iff)
                                subgoal for d t'
                                  apply (simp only: label_input0_msgs_def input0_msgs_def
                                      set_append Un_iff)
                                  apply (elim disjE)
                                  subgoal (* from input (os 1) 0 *)
                                    apply (subgoal_tac \<open>mysnd t' = 0\<close>)
                                    prefer 2
                                    subgoal
                                      using label_prop_inv(4)[unfolded buffers_inv]
                                      by (fastforce simp add: BULK_BENQ_def inputs_at_target_def
                                          image_iff)
                                    apply (subgoal_tac \<open>MyPair (myfst t') 0 = t'\<close>)
                                    prefer 2
                                    subgoal
                                      by (metis myprod.collapse)
                                    apply (simp only: cin.rep_eq cimage.rep_eq
                                        cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                    by (fastforce simp add: inputs_at_target_def image_iff)
                                  subgoal (* from cbufs (1, 0) *)
                                    apply (subgoal_tac \<open>mysnd t' = 0\<close>)
                                    prefer 2
                                    subgoal
                                      using label_prop_inv(4)[unfolded buffers_inv]
                                      by (fastforce simp add: BULK_BENQ_def image_iff)
                                    apply (subgoal_tac \<open>MyPair (myfst t') 0 = t'\<close>)
                                    prefer 2
                                    subgoal
                                      by (metis myprod.collapse)
                                    apply (simp only: cin.rep_eq cimage.rep_eq
                                        cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                    by (fastforce simp add: image_iff)
                                  subgoal (* from outpu (os 0) 0 *)
                                    apply (subgoal_tac \<open>mysnd t' = 0\<close>)
                                    prefer 2
                                    subgoal
                                      using label_prop_inv(4)[unfolded buffers_inv]
                                      by (fastforce simp add: BULK_BENQ_def
                                          outputs_at_target_raw_summary subgraph_inv(1) image_iff)
                                    apply (subgoal_tac \<open>MyPair (myfst t') 0 = t'\<close>)
                                    prefer 2
                                    subgoal
                                      by (metis myprod.collapse)
                                    apply (simp only: cin.rep_eq cimage.rep_eq
                                        cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                    by (fastforce simp add: outputs_at_target_raw_summary
                                        subgraph_inv(1) image_iff)
                                  subgoal (* from the consumed prefix: contradicts \<not> ts lxs *)
                                    apply (simp only: input_data_def input_events_def set_map)
                                    apply (clarsimp simp add: image_iff)
                                    apply (rename_tac ev)
                                    apply (case_tac ev)
                                    prefer 2
                                    subgoal by clarsimp
                                    prefer 2
                                    subgoal by clarsimp
                                    apply clarsimp
                                    subgoal for a b
                                      apply (erule notE)
                                      apply (subgoal_tac \<open>mysnd t' = 0\<close>)
                                      prefer 2
                                      subgoal
                                        using label_prop_inv(4)
                                        by (metis (mono_tags, lifting) UnCI event.sel(1)
                                            imageI setltakenD)
                                      apply (subgoal_tac \<open>MyPair (myfst t') 0 = t'\<close>)
                                      prefer 2
                                      subgoal
                                        by (metis myprod.collapse)
                                      apply (subgoal_tac \<open>Data t' (a, b) \<in> lset lxs\<close>)
                                      prefer 2
                                      subgoal
                                        by (simp add: in_lset_ltaken_ldropn[of _ lxs n])
                                      apply (simp only: ts_def)
                                      apply (subst cimage_iff)
                                      apply (rule_tac x=\<open>Data t' (a, b)\<close> in cBexI)
                                      subgoal
                                        by simp
                          by (simp add: cin.rep_eq cset_of_llist.rep_eq
                              del: label_propagation_op_logic_front_initia
                              ooo_input_op_logic_front_initia increment_op_logic_front_initia
                              operator_state_front_initia_upd_collapse)
                                    done
                                  done
                                done
                              subgoal (* y \<in> old timestamps *)
                                apply (erule disjE)
                                subgoal (* cap in old ocaps: contradicts the negated filter-old *)
                                  by blast
                                subgoal (* cap consumed: xa is the consumed time itself *)
                                  apply (clarsimp simp add: image_iff)
                                  subgoal for d
                                    apply (simp only: input0_msgs_def set_append Un_iff)
                                    apply (elim disjE)
                                    subgoal (* from cbufs (1, 0) *)
                                      apply (subgoal_tac \<open>mysnd x' = 0\<close>)
                                      prefer 2
                                      subgoal
                                        using label_prop_inv(4)[unfolded buffers_inv]
                                        by (fastforce simp add: BULK_BENQ_def image_iff)
                                      apply (subgoal_tac \<open>MyPair (myfst x') 0 = x'\<close>)
                                      prefer 2
                                      subgoal
                                        by (metis myprod.collapse)
                                      apply (simp only: cin.rep_eq cimage.rep_eq
                                          cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                      by (fastforce simp add: image_iff)
                                    subgoal (* from outpu (os 0) 0 *)
                                      apply (subgoal_tac \<open>mysnd x' = 0\<close>)
                                      prefer 2
                                      subgoal
                                        using label_prop_inv(4)[unfolded buffers_inv]
                                        by (fastforce simp add: BULK_BENQ_def
                                            outputs_at_target_raw_summary subgraph_inv(1) image_iff)
                                      apply (subgoal_tac \<open>MyPair (myfst x') 0 = x'\<close>)
                                      prefer 2
                                      subgoal
                                        by (metis myprod.collapse)
                                      apply (simp only: cin.rep_eq cimage.rep_eq
                                          cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                      by (fastforce simp add: outputs_at_target_raw_summary
                                          subgraph_inv(1) image_iff)
                                    subgoal (* from the consumed prefix: contradicts \<not> ts lxs *)
                                      apply (simp only: input_data_def input_events_def set_map)
                                      apply (clarsimp simp add: image_iff)
                                      apply (rename_tac ev)
                                      apply (case_tac ev)
                                      prefer 2
                                      subgoal by clarsimp
                                      prefer 2
                                      subgoal by clarsimp
                                      apply clarsimp
                                      subgoal for a b
                                        apply (erule notE)
                                        apply (subgoal_tac \<open>mysnd x' = 0\<close>)
                                        prefer 2
                                        subgoal
                                          using label_prop_inv(4)
                                          by (metis (mono_tags, lifting) UnCI event.sel(1)
                                              imageI setltakenD)
                                        apply (subgoal_tac \<open>MyPair (myfst x') 0 = x'\<close>)
                                        prefer 2
                                        subgoal
                                          by (metis myprod.collapse)
                                        apply (subgoal_tac \<open>Data x' (a, b) \<in> lset lxs\<close>)
                                        prefer 2
                                        subgoal
                                          by (simp add: in_lset_ltaken_ldropn[of _ lxs n])
                                        apply (simp only: ts_def)
                                        apply (subst cimage_iff)
                                        apply (rule_tac x=\<open>Data x' (a, b)\<close> in cBexI)
                                        subgoal
                                          by simp
                          by (simp add: cin.rep_eq cset_of_llist.rep_eq
                              del: label_propagation_op_logic_front_initia
                              ooo_input_op_logic_front_initia increment_op_logic_front_initia
                              operator_state_front_initia_upd_collapse)
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      done
                    done
                  subgoal (* closed at the new frontier: x \<in> SPold \<longleftrightarrow> x \<in> Pair (1,0) |`| FinalImg *)
                    (* Plan: open with the live-case clarsimp (flip cin.rep_eq, image_iff,
                       cset_from_list_def, cset_of_llist.rep_eq), rule iffI.
                       LHS\<Longrightarrow>RHS: S and OutOld direct; SPold-witness t0 is excluded from
                       SPnew (ocaps0_after_final_output_set needs fle \<or> \<notin>ts-second, both
                       false here; ts (ldropn) excluded by
                       timely_input_stream_ldropn_no_data_le_if_not_frontier_less_equal),
                       so x lands in FinalImg: t0 \<in> label_produces_below_times n (cap via
                       the live-case source analysis, \<not>fle-new given, myfst t0 \<in> ts-second
                       via timestamps_after_second_propa_eq); emitted payload equals the
                       SPold payload by the hoisted payload \<forall>-fact + icoll (ldropn) t0 = {}
                       (expiry) + Wcc.components_from_labels_correct with labels_inv
                       (labels_after_final_output) and the sorried STABILITY subgoal_tac.
                       RHS\<Longrightarrow>LHS: FinalImg \<Longrightarrow> SPold via ocaps0_after_second_propa_eq
                       (below-times \<subseteq> old-caps \<union> consumed) mirroring the proven
                       MyPair-filter-new leaf; SPnew \<Longrightarrow> SPold as in the live case. *)
                    apply (subgoal_tac \<open>final_output n = label_produces_batch n\<close>)
                    prefer 2
                    subgoal
                      unfolding final_output_def label_produces_batch_def
                      apply (rule arg_cong2[where f=label_prop_output_batch])
                      subgoal
                        by (simp add: os_label_after_second_propa_def
                            os_label_after_label_progress_def os_label_after_drop_caps_def
                            obtain_progress_def os_label_after_loop_updates_def loop_res_def
                            os_label_after_input0_def os_label_after_read_input0_def
                            os_label_after_first_propa_def label_front_after_second_propa_def
                            label_front_after_first_propa_def
                            cbufs_after_label_read_input0_def cbufs_after_input_output_def
                            os_after_label_input0_def os_after_label_read_input0_def
                            os_after_input_output_def os_input_after_output_def
                            os_after_input_stream_def os_input_after_stream_def
                            os_first_propa_def os_progress_def sg_first_propa_def
                            label_input0_msgs_def input0_msgs_def input_data_def
                            input_events_def CONSUMES_CONSUMES flip: fold_append)
                      subgoal
                        apply (simp add: label_produces_below_times_def
                            timestamps_after_second_propa_eq os_label_after_second_propa_def
                            os_label_after_label_progress_def os_label_after_drop_caps_def
                            obtain_progress_def os_label_after_loop_updates_def loop_res_def
                            os_label_after_input0_def os_label_after_read_input0_def
                            os_label_after_first_propa_def label_front_after_second_propa_def
                            label_front_after_first_propa_def
                            cbufs_after_label_read_input0_def cbufs_after_input_output_def
                            os_after_label_input0_def os_after_label_read_input0_def
                            os_after_input_output_def os_input_after_output_def
                            os_after_input_stream_def os_input_after_stream_def
                            os_first_propa_def os_progress_def sg_first_propa_def
                            drop_caps_def
                            label_input0_msgs_def input0_msgs_def input_data_def
                            input_events_def CONSUMES_CONSUMES filter_filter conj_commute
                            del: label_propagation_op_logic_front_initia
                            ooo_input_op_logic_front_initia increment_op_logic_front_initia
                            operator_state_front_initia_upd_collapse
                            flip: fold_append)
                        apply (rule filter_cong[OF refl])
                        apply (simp only: image_Un image_image)
                        by blast
                      done
                    apply (subgoal_tac \<open>\<forall>t0 :: (nat, nat) myprod. \<not> frontier_less_equal
                        (exit_scope myfst (front (os_label_after_second_propa n) 0 +
                          front (os_label_after_second_propa n) 1)) (myfst t0) \<longrightarrow>
                        set (icoll (ldropn n lxs) t0) = {}\<close>)
                    prefer 2
                    subgoal (* closed second-propa frontier leaves no data in ldropn *)
                      apply (subgoal_tac \<open>front (os_label_after_second_propa n) (0 :: 2) =
                          frontier (zmset_of (mset (ocaps (os 0) 0) +
                            event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
                            event.time `# filter_mset is_Drop (mset (ltaken n lxs))))\<close>)
                      prefer 2
                      subgoal
                        apply (simp add: os_label_after_second_propa_def
                            label_front_after_second_propa_def
                            second_propa(2)[rule_format, of n \<open>Loc 1 (Trg 0)\<close>])
                        apply (simp add: sg_first_propa_def sg_progress_def)
                        unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D]
                          UNIV_3_2
                        apply (clarsimp simp add: split_beta subgraph_inv(1))
                        subgoal premises self_path
                          apply (subgoal_tac \<open>c_pts (change_multiplicities
                               (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                               (Loc (0 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z\<close>)
                          defer
                          subgoal
                            apply (subgoal_tac \<open>c_pts (change_multiplicities
                                 (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                                 (Loc (0 :: 3) (Trg (0 :: 2))) = caps' n (Loc 0 (Trg 0))\<close>)
                            defer
                            subgoal
                              using c_pts_after_second_progress_caps'[of n
                                  \<open>Loc (0 :: 3) (Trg (0 :: 2))\<close>]
                              by simp
                            apply (subgoal_tac \<open>caps' n (Loc (0 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z\<close>)
                            defer
                            subgoal
                              using dt_inv'(2)[of n] buffers_inv(2)
                              by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary
                                  subgraph_inv(1) sg_first_propa_def sg_progress_def
                                  cbufs_after_loop_updates_def loop_res_def
                                  cbufs_after_label_read_input0_def cbufs_after_input_output_def
                                  os_after_loop_progress_def os_after_drop_caps_def
                                  os_after_loop_updates_def os_after_label_input0_def
                                  os_after_label_read_input0_def os_after_input_output_def
                                  os_input_after_output_def os_after_input_stream_def
                                  os_input_after_stream_def os_first_propa_def os_progress_def
                                  input0_msgs_def BULK_BENQ_def os_inv(1,4) op_state_base_def
                                  operator_state.defs obtain_progress_def)
                            apply simp
                            done
                          apply (subgoal_tac \<open>c_pts (change_multiplicities
                               (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                               (Loc (1 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z\<close>)
                          defer
                          subgoal
                            apply (subgoal_tac \<open>c_pts (change_multiplicities
                                 (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                                 (Loc (1 :: 3) (Trg (0 :: 2))) = caps' n (Loc 1 (Trg 0))\<close>)
                            defer
                            subgoal
                              using c_pts_after_second_progress_caps'[of n
                                  \<open>Loc (1 :: 3) (Trg (0 :: 2))\<close>]
                              by simp
                            apply (subgoal_tac \<open>caps' n (Loc (1 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z\<close>)
                            defer
                            subgoal
                              using dt_inv'(2)[of n]
                              by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary
                                  subgraph_inv(1) sg_first_propa_def sg_progress_def
                                  cbufs_after_loop_updates_def loop_res_def
                                  cbufs_after_label_read_input0_def cbufs_after_input_output_def
                                  os_after_loop_progress_def os_after_drop_caps_def
                                  os_after_loop_updates_def os_after_label_input0_def
                                  os_after_label_read_input0_def os_after_input_output_def
                                  os_input_after_output_def os_after_input_stream_def
                                  os_input_after_stream_def os_first_propa_def os_progress_def
                                  input0_msgs_def BULK_BENQ_def os_inv(1,4) op_state_base_def
                                  operator_state.defs obtain_progress_def)
                            apply simp
                            done
                          apply (subgoal_tac \<open>c_pts (change_multiplicities
                               (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                               (Loc (0 :: 3) (Src (0 :: 2))) =
                               zmset_of (mset (ocaps (os 0) 0) +
                                 event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
                                 event.time `# filter_mset is_Drop (mset (ltaken n lxs)))\<close>)
                          defer
                          subgoal
                            apply (subgoal_tac \<open>c_pts (change_multiplicities
                                 (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                                 (Loc (0 :: 3) (Src (0 :: 2))) = caps' n (Loc 0 (Src 0))\<close>)
                            defer
                            subgoal
                              using c_pts_after_second_progress_caps'[of n
                                  \<open>Loc (0 :: 3) (Src (0 :: 2))\<close>]
                              by simp
                            apply (subgoal_tac \<open>caps' n (Loc (0 :: 3) (Src (0 :: 2))) =
                                 zmset_of (mset (ocaps (os 0) 0) +
                                   event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
                                   event.time `# filter_mset is_Drop (mset (ltaken n lxs)))\<close>)
                            defer
                            subgoal
                              using dt_inv'(1)[of n]
                                mset_ocaps_updates[of \<open>ltaken n lxs\<close> \<open>ldropn n lxs\<close>
                                  \<open>ocaps (fst (obtain_progress os_input)) (0 :: 2)\<close>]
                                input_stream_inv os_inv(1)
                              apply (simp add: Src_caps_inv_def input_events_def
                                  os_after_loop_progress_def os_after_drop_caps_def
                                  os_after_loop_updates_def loop_res_def os_after_label_input0_def
                                  os_after_label_read_input0_def os_after_input_output_def
                                  os_input_after_output_def os_after_input_stream_def
                                  os_input_after_stream_def os_first_propa_def os_progress_def
                                  os_inv(4) op_state_base_def operator_state.defs
                                  obtain_progress_def)
                              apply (drule arg_cong[where f=zmset_of])
                              apply (simp add: to_zmset_correct)
                              done
                            apply simp
                            done
                          apply simp
                          done
                        done
                      apply (intro allI impI)
                      apply (subgoal_tac \<open>icoll (ldropn n lxs) t0 = []\<close>)
                      apply simp
                      apply (rule icoll_empty_if_no_data_le)
                      subgoal for t0 t' d
                        apply (rule timely_input_stream_ldropn_no_data_le_if_not_frontier_less_equal
                            [OF input_stream_inv stream_move(1), of t0 t' d])
                        apply (subgoal_tac \<open>\<not> frontier_less_equal
                             (front (os_label_after_second_propa n) (0 :: 2)) t0\<close>)
                        apply simp
                        apply (rule conjunct1[OF not_frontier_less_equal_sum])
                        apply (rule frontier_less_equal_exit_scope)
                        apply assumption
                        by assumption
                      done
                    apply (subgoal_tac \<open>(((outputs_at_target (summ (sg_after_second_propa n)) (os_after_final_output n) >>
                          cbufs((1, 0) := [], (1, 1) := [], (2, 1) := [])) >>
                         inputs_at_target (os_after_final_output n)) (1, 0)) = []\<close>)
                    prefer 2
                    subgoal
                      by (simp add: outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def
                          inputs_at_target_def sg_after_second_propa_def
                          sg_after_increment_progress_def sg_after_label_progress_def
                          sg_after_ooo_input_progress_def sg_first_propa_def
                          sg_progress_def outpu_0_after_final_output_empty)
                    apply (subgoal_tac \<open>all_edges (os_label_after_final_output n) =
                        all_edges (os_label_after_second_propa n) \<and>
                        min_label (os_label_after_final_output n) =
                        min_label (os_label_after_second_propa n)\<close>)
                    prefer 2
                    subgoal
                      by (simp add: os_label_after_final_output_def os_label_after_produces_def
                          produces_def drop_caps_def all_edges_def all_vertices_def
                          neighbors_def min_label_def fun_eq_iff)
                    apply (subgoal_tac \<open>en2 (os_label_after_second_propa n) =
                        (Inr :: nat set set \<Rightarrow> nat \<times> nat + nat set set)\<close>)
                    prefer 2
                    subgoal
                      by (simp add: os_label_after_second_propa_def
                          os_label_after_label_progress_def os_label_after_drop_caps_def
                          obtain_progress_def os_label_after_loop_updates_def loop_res_def
                          os_label_after_input0_def os_label_after_read_input0_def
                          os_label_after_first_propa_def drop_caps_def os_inv(4)
                          operator_state.defs)
                    apply (subgoal_tac \<open>\<forall>t0 :: (nat, nat) myprod. mysnd t0 = 0 \<longrightarrow>
                        \<not> frontier_less_equal (exit_scope myfst
                          (front (os_label_after_second_propa n) 0 +
                           front (os_label_after_second_propa n) 1)) (myfst t0) \<longrightarrow>
                        ccs (set (icoll (map (\<lambda>(x, t'). Data t' (projl x))
                            (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0)) @@- lxs) t0) \<union>
                          all_edges os_label_prop (myfst t0)) =
                        ccs (all_edges (os_label_after_second_propa n) (myfst t0))\<close>)
                    prefer 2
                    subgoal
                      apply (intro allI impI)
                      apply (drule_tac x=t0 in spec)
                      apply (drule mp, assumption)
                      by (simp add: BULK_BENQ_def)
                    subgoal
                      apply (clarsimp simp flip: cin.rep_eq
                          simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                      apply (rule iffI)
                      apply (elim disjE)
                      subgoal by simp
                      subgoal
                        by (force simp flip: cin.rep_eq
                            simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                      subgoal
                        apply (rule disjI1)
                        apply (clarsimp simp flip: cin.rep_eq
                            simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                        apply (subgoal_tac \<open>mysnd xa = 0\<close>)
                        prefer 2
                        subgoal
                          apply (thin_tac \<open>\<forall>t0. mysnd t0 = 0 \<longrightarrow> P t0\<close> for P)
                          apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                          apply (thin_tac \<open>x = y\<close> for y)
                          apply (elim disjE)
                          subgoal
                            apply (clarsimp simp add: ts_def cin.rep_eq cset_of_llist.rep_eq
                                image_iff simp del: label_propagation_op_logic_front_initia
                                ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                operator_state_front_initia_upd_collapse split: event.splits)
                            apply (rename_tac ev)
                            apply (case_tac ev)
                            prefer 2
                            subgoal by clarsimp
                            prefer 2
                            subgoal by clarsimp
                            apply clarsimp
                            using label_prop_inv(4)
                            by (metis (mono_tags, lifting) UnCI event.sel(1) imageI)
                          subgoal
                            using label_prop_inv(4)[unfolded buffers_inv]
                            by (fastforce simp flip: cin.rep_eq
                                simp add: cset_of_llist.rep_eq cset_from_list_def image_iff)
                          subgoal
                            by clarsimp
                          done
                        apply (rule cimageI)
                        apply (rule cUnI2)
                        apply (subst cimage_iff)
                        apply (rule_tac x=\<open>(Inr (ccs (set (icoll (map (\<lambda>(x, t'). Data t' (projl x))
                             (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0)) @@- lxs) xa) \<union>
                             all_edges os_label_prop (myfst xa))), Cap xa (0 :: 2))\<close> in cBexI)
                        apply simp
                        apply (simp add: cset_of_llist.rep_eq label_produces_batch_def
                            label_prop_output_batch_def label_produces_below_times_def)
                        apply (subgoal_tac \<open>xa \<in> set (ocaps (os_label_after_second_propa n) (0 :: 2)) \<and>
                             myfst xa \<in> set (timestamps (os_label_after_second_propa n))\<close>)
                        prefer 2
                        subgoal
                          apply (elim disjE)
                          subgoal (* timestamp from lxs: closed times must be in the consumed prefix *)
                            apply (clarsimp simp add: cin.rep_eq ts_def cset_of_llist.rep_eq
                                image_iff simp del: label_propagation_op_logic_front_initia
                                ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                operator_state_front_initia_upd_collapse)
                            subgoal for xb
                              apply (cases xb)
                              subgoal for t d
                                apply clarsimp
                                apply (cases d)
                                subgoal for a b
                                  apply (subgoal_tac \<open>Data t (a, b) \<in> set (ltaken n lxs)\<close>)
                                  subgoal
                                    apply (rule conjI)
                                    subgoal
                                      apply (simp add: ocaps0_after_second_propa_eq
                                          input0_msgs_def input_data_def input_events_def)
                                      apply (rule disjI2)+
                                      apply (rule image_eqI[where x=\<open>Data t (a, b)\<close>])
                                      apply simp
                                      by simp
                                    apply (simp add: timestamps_after_second_propa_eq
                                        label_input0_msgs_def input0_msgs_def input_data_def input_events_def)
                                    apply (rule disjI1)
                                    apply (rule image_eqI[where x=\<open>Data t (a, b)\<close>])
                                    apply simp
                                    by simp
                                  apply (subgoal_tac \<open>Data t (a, b) \<in> set (ltaken n lxs) \<or>
                                          Data t (a, b) \<in> lset (ldropn n lxs)\<close>)
                                  prefer 2
                                  subgoal
                                    by (simp add: in_lset_ltaken_ldropn[of _ lxs n])
                                  apply (erule disjE)
                                  subgoal by simp
                                  apply (subgoal_tac \<open>icoll (ldropn n lxs) t = []\<close>)
                                  subgoal
                                    apply (subgoal_tac \<open>(a, b) \<in> set (icoll (ldropn n lxs) t)\<close>)
                                    subgoal
                                      apply (drule arg_cong[where f=set])
                                      by simp
                                    apply (rule set_icoll_lsetI)
                                    apply (rule timely_input_stream_expires_le[OF timely_input_stream_ldrop[OF stream_move(1) input_stream_inv]])
                                    apply assumption
                                    by simp
                                  apply (drule_tac x=t and P=\<open>\<lambda>t0. \<not> frontier_less_equal
                                          (exit_scope myfst (front (os_label_after_second_propa n) 0 +
                                            front (os_label_after_second_propa n) 1)) (myfst t0) \<longrightarrow>
                                          icoll (ldropn n lxs) t0 = []\<close> in spec)
                                  apply (drule mp, assumption)
                                  by assumption
                                done
                              subgoal by auto
                              subgoal by auto
                              done
                            done
                          subgoal (* timestamp from old buffers *)
                            apply (rule conjI)
                            subgoal
                              apply (simp add: ocaps0_after_second_propa_eq input0_msgs_def)
                              apply (simp flip: cin.rep_eq add: cimage_iff cBex_cUn
                                  cBex.rep_eq cset_of_llist.rep_eq image_iff
                                  inputs_at_target_def outputs_at_target_raw_summary
                                  subgraph_inv(1) BULK_BENQ_def)
                              apply (erule bexE)
                              apply (elim UnE)
                              subgoal for y
                                apply (rule disjI1)
                                apply (subgoal_tac \<open>(0 :: (nat, nat) myprod) \<in>
                                        set (intsum (os 1) (0 :: 2) (0 :: 2))\<close>)
                                subgoal
                                  using label_prop_inv(6)[unfolded input_ocaps_inv_def,
                                      rule_format, of \<open>snd y\<close> 0 0 0]
                                  by simp
                                using spec[OF os_inv(7), of 1]
                                by (simp add: raw_summary_def zero_myprod_def)
                              subgoal by blast
                              subgoal by blast
                              done
                            subgoal
                              apply (simp add: timestamps_after_second_propa_eq
                                  label_input0_msgs_def input0_msgs_def)
                              apply (simp flip: cin.rep_eq add: cimage_iff cBex_cUn
                                  cBex.rep_eq cset_of_llist.rep_eq image_iff
                                  inputs_at_target_def outputs_at_target_raw_summary
                                  subgraph_inv(1) BULK_BENQ_def)
                              apply (erule bexE)
                              apply (elim UnE)
                              subgoal for y
                                apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
                                apply (rule bexI[where x=y])
                                apply (cases y, simp)
                                by assumption
                              subgoal for y
                                apply (rule disjI2, rule disjI2, rule disjI1)
                                apply (rule bexI[where x=y])
                                apply (cases y, simp)
                                by assumption
                              subgoal for y
                                apply (rule disjI2, rule disjI1)
                                apply (rule bexI[where x=y])
                                apply (cases y, simp)
                                by assumption
                              done
                            done
                          subgoal (* timestamp from old ocaps/timestamps *)
                            apply (elim exE conjE bexE)
                            apply (rule conjI)
                            subgoal for y xb
                              apply (simp add: ocaps0_after_second_propa_eq)
                              apply (rule disjI1)
                              apply (subgoal_tac \<open>mysnd xb = 0\<close>)
                              subgoal
                                apply (subgoal_tac \<open>MyPair (myfst xb) 0 = xb\<close>)
                                apply simp
                                by (cases xb, simp)
                              using label_prop_inv(4)
                              by blast
                            subgoal
                              by (simp add: timestamps_after_second_propa_eq)
                            done
                          done



                        subgoal for xa
                          apply (rule image_eqI[where x=\<open>myfst xa\<close>])
                          subgoal
                            apply (simp add: Wcc.components_from_labels_correct
                                labels_after_second_propa)
                            by (metis myprod.collapse)
                          subgoal
                            apply (rule image_eqI[where x=xa])
                            apply simp
                            by simp
                          done
                        done

                      subgoal (* reverse direction: RHS \<Longrightarrow> LHS *)
                        apply (elim disjE)
                        apply (clarsimp simp flip: cin.rep_eq
                            simp add: image_iff cset_of_llist.rep_eq)
                        apply (elim disjE)
                        subgoal (* x \<in> OutOld: direct *)
                          by (force simp flip: cin.rep_eq
                              simp add: image_iff cset_of_llist.rep_eq)
                        subgoal (* x \<in> FinalImg \<Longrightarrow> x \<in> SPold *)
                          apply (clarsimp simp flip: cin.rep_eq
                              simp add: image_iff cset_of_llist.rep_eq
                              label_produces_batch_def label_prop_output_batch_def
                              label_produces_below_times_def)
                          subgoal for xa
                            apply (subgoal_tac \<open>components_from_labels
                                   (all_edges (os_label_after_second_propa n) (myfst xa))
                                   (min_label (os_label_after_second_propa n) (myfst xa)) =
                                   ccs (all_edges (os_label_after_second_propa n) (myfst xa))\<close>)
                            prefer 2
                            subgoal
                              apply (rule Wcc.components_from_labels_correct)
                              subgoal using labels_after_second_propa by blast
                              subgoal by blast
                              done
                            apply (drule_tac x=\<open>MyPair (myfst xa) 0\<close> and
                                P=\<open>\<lambda>t0. mysnd t0 = 0 \<longrightarrow> ccs (set (icoll (map (\<lambda>(x, t'). Data t' (projl x))
                                     (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0)) @@- lxs) t0) \<union>
                                     all_edges os_label_prop (myfst t0)) =
                                     ccs (set (icoll (ldropn n lxs) t0) \<union> all_edges (os_label_after_second_propa n) (myfst t0))\<close> in spec)
                            apply (drule mp)
                            subgoal by simp
                            apply (drule_tac x=\<open>MyPair (myfst xa) 0\<close> and
                                P=\<open>\<lambda>t0. \<not> frontier_less_equal (exit_scope myfst (front (os_label_after_second_propa n) 0 +
                                     front (os_label_after_second_propa n) 1)) (myfst t0) \<longrightarrow>
                                     icoll (ldropn n lxs) t0 = []\<close> in spec)
                            apply (drule mp)
                            subgoal by simp
                            apply (thin_tac \<open>\<not> x' |\<in>| S\<close> for x')
                            apply (erule notE)
                            apply (subst cimage_iff)
                            apply (rule_tac x=\<open>MyPair (myfst xa) 0\<close> in cBexI)
                            subgoal by simp
                            apply (subgoal_tac \<open>myfst xa \<in> (\<lambda>(d, y). myfst y) ` set (label_input0_msgs n) \<or>
                                   myfst xa \<in> set (timestamps os_label_prop)\<close>)
                            prefer 2
                            subgoal by (simp add: timestamps_after_second_propa_eq)
                            apply (thin_tac \<open>myfst xa \<in> set (timestamps (os_label_after_second_propa n))\<close>)
                            apply (thin_tac \<open>P = Q\<close> for P Q)+
                            apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                            apply (erule disjE)
                            subgoal (* myfst xa is the time of a consumed message *)
                              apply (clarsimp simp add: image_iff)
                              subgoal for d t'
                                apply (simp only: label_input0_msgs_def input0_msgs_def
                                    set_append Un_iff)
                                apply (elim disjE)
                                subgoal (* from input (os 1) 0 *)
                                  apply (subgoal_tac \<open>mysnd t' = 0\<close>)
                                  prefer 2
                                  subgoal
                                    using label_prop_inv(4)[unfolded buffers_inv]
                                    by (fastforce simp add: BULK_BENQ_def inputs_at_target_def
                                        image_iff)
                                  apply (subgoal_tac \<open>MyPair (myfst t') 0 = t'\<close>)
                                  prefer 2
                                  subgoal
                                    by (metis myprod.collapse)
                                  apply (simp only: cin.rep_eq cimage.rep_eq
                                      cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                  by (fastforce simp add: inputs_at_target_def image_iff)
                                subgoal (* from cbufs (1, 0) *)
                                  apply (subgoal_tac \<open>mysnd t' = 0\<close>)
                                  prefer 2
                                  subgoal
                                    using label_prop_inv(4)[unfolded buffers_inv]
                                    by (fastforce simp add: BULK_BENQ_def image_iff)
                                  apply (subgoal_tac \<open>MyPair (myfst t') 0 = t'\<close>)
                                  prefer 2
                                  subgoal
                                    by (metis myprod.collapse)
                                  apply (simp only: cin.rep_eq cimage.rep_eq
                                      cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                  by (fastforce simp add: image_iff)
                                subgoal (* from outpu (os 0) 0 *)
                                  apply (subgoal_tac \<open>mysnd t' = 0\<close>)
                                  prefer 2
                                  subgoal
                                    using label_prop_inv(4)[unfolded buffers_inv]
                                    by (fastforce simp add: BULK_BENQ_def
                                        outputs_at_target_raw_summary subgraph_inv(1) image_iff)
                                  apply (subgoal_tac \<open>MyPair (myfst t') 0 = t'\<close>)
                                  prefer 2
                                  subgoal
                                    by (metis myprod.collapse)
                                  apply (simp only: cin.rep_eq cimage.rep_eq
                                      cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                  by (fastforce simp add: outputs_at_target_raw_summary
                                      subgraph_inv(1) image_iff)
                                subgoal (* from the consumed prefix: lands in ts lxs *)
                                  apply (simp only: input_data_def input_events_def set_map)
                                  apply (clarsimp simp add: image_iff)
                                  apply (rename_tac ev)
                                  apply (case_tac ev)
                                  prefer 2
                                  subgoal by clarsimp
                                  prefer 2
                                  subgoal by clarsimp
                                  apply clarsimp
                                  subgoal for a b
                                    apply (subgoal_tac \<open>mysnd t' = 0\<close>)
                                    prefer 2
                                    subgoal
                                      using label_prop_inv(4)
                                      by (metis (mono_tags, lifting) UnCI event.sel(1)
                                          imageI setltakenD)
                                    apply (subgoal_tac \<open>MyPair (myfst t') 0 = t'\<close>)
                                    prefer 2
                                    subgoal
                                      by (metis myprod.collapse)
                                    apply (subgoal_tac \<open>Data t' (a, b) \<in> lset lxs\<close>)
                                    prefer 2
                                    subgoal
                                      by (simp add: in_lset_ltaken_ldropn[of _ lxs n])
                                    apply (thin_tac \<open>\<not> frontier_less_equal P Q\<close> for P Q)
                                    apply (erule notE)
                                    apply (simp only: ts_def)
                                    apply (subst cimage_iff)
                                    apply (rule_tac x=\<open>Data t' (a, b)\<close> in cBexI)
                                    subgoal
                                      by simp
                                    by (simp add: cin.rep_eq cset_of_llist.rep_eq)
                                  done
                                done
                              done
                            subgoal (* myfst xa is an old timestamp *)
                              apply (subgoal_tac \<open>xa \<in> set (ocaps (os 1) 0) \<or>
                                     xa \<in> snd ` set (input0_msgs n)\<close>)
                              prefer 2
                              subgoal by (simp add: ocaps0_after_second_propa_eq)
                              apply (thin_tac \<open>xa \<in> set (ocaps (os_label_after_second_propa n) 0)\<close>)
                              apply (erule disjE)
                              subgoal (* cap in old ocaps: filter-old *)
                                apply (rule cUnI2)
                                apply (subst cimage_iff)
                                apply (rule_tac x=\<open>myfst xa\<close> in cBexI)
                                subgoal by simp
                                apply (subst cin_cfilter)
                                apply (rule conjI)
                                subgoal by (simp add: cin.rep_eq cset_of_llist.rep_eq
                                    del: label_propagation_op_logic_front_initia
                                    ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                    operator_state_front_initia_upd_collapse)
                                subgoal by blast
                                done
                              subgoal (* cap consumed: xa is the consumed time itself *)
                                apply (clarsimp simp add: image_iff)
                                subgoal for d
                                  apply (simp only: input0_msgs_def set_append Un_iff)
                                  apply (elim disjE)
                                  subgoal (* from cbufs (1, 0) *)
                                    apply (subgoal_tac \<open>mysnd xa = 0\<close>)
                                    prefer 2
                                    subgoal
                                      using label_prop_inv(4)[unfolded buffers_inv]
                                      by (fastforce simp add: BULK_BENQ_def image_iff)
                                    apply (subgoal_tac \<open>MyPair (myfst xa) 0 = xa\<close>)
                                    prefer 2
                                    subgoal
                                      by (metis myprod.collapse)
                                    apply (simp only: cin.rep_eq cimage.rep_eq
                                        cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                    by (fastforce simp add: image_iff)
                                  subgoal (* from outpu (os 0) 0 *)
                                    apply (subgoal_tac \<open>mysnd xa = 0\<close>)
                                    prefer 2
                                    subgoal
                                      using label_prop_inv(4)[unfolded buffers_inv]
                                      by (fastforce simp add: BULK_BENQ_def
                                          outputs_at_target_raw_summary subgraph_inv(1) image_iff)
                                    apply (subgoal_tac \<open>MyPair (myfst xa) 0 = xa\<close>)
                                    prefer 2
                                    subgoal
                                      by (metis myprod.collapse)
                                    apply (simp only: cin.rep_eq cimage.rep_eq
                                        cset_of_llist.rep_eq lset_llist_of BULK_BENQ_def)
                                    by (fastforce simp add: outputs_at_target_raw_summary
                                        subgraph_inv(1) image_iff)
                                  subgoal (* from the consumed prefix: lands in ts lxs *)
                                    apply (simp only: input_data_def input_events_def set_map)
                                    apply (clarsimp simp add: image_iff)
                                    apply (rename_tac ev)
                                    apply (case_tac ev)
                                    prefer 2
                                    subgoal by clarsimp
                                    prefer 2
                                    subgoal by clarsimp
                                    apply clarsimp
                                    subgoal for a b
                                      apply (subgoal_tac \<open>mysnd xa = 0\<close>)
                                      prefer 2
                                      subgoal
                                        using label_prop_inv(4)
                                        by (metis (mono_tags, lifting) UnCI event.sel(1)
                                            imageI setltakenD)
                                      apply (subgoal_tac \<open>MyPair (myfst xa) 0 = xa\<close>)
                                      prefer 2
                                      subgoal
                                        by (metis myprod.collapse)
                                      apply (subgoal_tac \<open>Data xa (a, b) \<in> lset lxs\<close>)
                                      prefer 2
                                      subgoal
                                        by (simp add: in_lset_ltaken_ldropn[of _ lxs n])
                                      apply (thin_tac \<open>\<not> frontier_less_equal P Q\<close> for P Q)
                                      apply (erule notE)
                                      apply (simp only: ts_def)
                                      apply (subst cimage_iff)
                                      apply (rule_tac x=\<open>Data xa (a, b)\<close> in cBexI)
                                      subgoal
                                        by simp
                                      by (simp add: cin.rep_eq cset_of_llist.rep_eq)
                                    done
                                  done
                                done
                              done
                            done
                          done
                        subgoal (* x \<in> S: direct *)
                          by simp
                        subgoal (* x \<in> SPnew \<Longrightarrow> x \<in> SPold *)
                          apply (clarsimp simp flip: cin.rep_eq
                              simp add: image_iff cset_of_llist.rep_eq)
                          subgoal for xa
                            apply (subgoal_tac \<open>(((outputs_at_target (summ (sg_after_second_propa n)) (os_after_final_output n) >>
                                   cbufs((1, 0) := [], (1, 1) := [], (2, 1) := [])) >>
                                  inputs_at_target (os_after_final_output n)) (1, 0)) = []\<close>)
                            prefer 2
                            subgoal
                              by (simp add: BULK_BENQ_def)
                            apply (subgoal_tac \<open>mysnd xa = 0\<close>)
                            prefer 2
                            subgoal
                              apply (thin_tac \<open>\<forall>t0. mysnd t0 = 0 \<longrightarrow> P t0\<close> for P)
                              apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                              apply (thin_tac \<open>x = y\<close> for y)
                              apply (thin_tac \<open>final_output n = y\<close> for y)
                              apply (thin_tac \<open>\<not> x' |\<in>| A\<close> for x' A)+
                              apply (elim disjE)
                              subgoal
                                apply (clarsimp simp add: ts_def cin.rep_eq cset_of_llist.rep_eq
                                    image_iff simp del: label_propagation_op_logic_front_initia
                                    ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                    operator_state_front_initia_upd_collapse split: event.splits)
                                apply (rename_tac ev)
                                apply (case_tac ev)
                                prefer 2
                                subgoal by clarsimp
                                prefer 2
                                subgoal by clarsimp
                                apply clarsimp
                                subgoal for a b
                                  apply (subgoal_tac \<open>Data xa (a, b) \<in> lset lxs\<close>)
                                  prefer 2
                                  subgoal
                                    by (simp add: in_lset_ltaken_ldropn[of _ lxs n])
                                  using label_prop_inv(4)
                                  by (metis (mono_tags, lifting) UnCI event.sel(1) imageI)
                                done
                              subgoal
                              by (simp add: BULK_BENQ_def cin.rep_eq cimage.rep_eq
                                    cset_of_llist.rep_eq
                                    del: label_propagation_op_logic_front_initia
                                    ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                    operator_state_front_initia_upd_collapse)
                              subgoal
                                by clarsimp
                              done
                            apply (subgoal_tac \<open>\<not> (\<exists>y. y \<in> set (timestamps (os_label_after_final_output n)) \<and>
                                 (\<exists>x\<in>set (ocaps (os_after_final_output n 1) 0). y = myfst x) \<and>
                                 xa = MyPair y 0)\<close>)
                            prefer 2
                            subgoal
                              apply (thin_tac \<open>P = Q\<close> for P Q)+
                              apply (thin_tac \<open>\<forall>t0. mysnd t0 = 0 \<longrightarrow> P t0\<close> for P)
                              apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                              apply (thin_tac \<open>\<forall>t0. \<not> P (myfst t0) \<longrightarrow>
                                    icoll (ldropn n lxs) t0 = []\<close> for P)
                              apply (thin_tac \<open>\<not> x' |\<in>| A\<close> for x' A)+
                              apply (auto simp add: ocaps0_after_final_output_set
                                  timestamps_after_final_output_eq timestamps_after_second_propa_eq)
                              by ((metis (mono_tags, lifting) case_prod_conv imageI)+)
                            apply (thin_tac \<open>\<not> x' |\<in>| S\<close> for x')
                            apply (thin_tac \<open>\<not> frontier_less_equal P Q\<close> for P Q)
                            apply (erule notE)
                            apply (subst cimage_iff)
                            apply (rule_tac x=xa in cBexI)
                            subgoal
                              by (simp add: BULK_BENQ_def)
                            apply (elim disjE)
                            subgoal (* xa \<in> ts (ldropn n lxs) \<Longrightarrow> xa \<in> ts lxs *)
                              apply (thin_tac \<open>\<forall>t0. mysnd t0 = 0 \<longrightarrow> P t0\<close> for P)
                              apply (thin_tac \<open>\<forall>t\<in>set (timestamps (os_label_after_second_propa n)). Q t\<close> for Q)
                              apply (thin_tac \<open>x = y\<close> for y)
                              apply (clarsimp simp flip: cin.rep_eq
                                  simp add: image_iff cset_of_llist.rep_eq ts_def
                                  split: event.splits)
                              apply (rename_tac ev)
                              apply (case_tac ev)
                              prefer 2
                              subgoal by clarsimp
                              prefer 2
                              subgoal by clarsimp
                              apply clarsimp
                              subgoal for a b
                                apply (subgoal_tac \<open>Data xa (a, b) \<in> lset lxs\<close>)
                                prefer 2
                                subgoal
                                  by (simp add: cin.rep_eq cset_of_llist.rep_eq
                                      in_lset_ltaken_ldropn[of _ lxs n]
                                      del: label_propagation_op_logic_front_initia
                                      ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                      operator_state_front_initia_upd_collapse)
                                apply (drule_tac x=\<open>Data xa (a, b)\<close> in spec)
                              by (clarsimp simp add: cin.rep_eq cset_of_llist.rep_eq
                                  simp del: label_propagation_op_logic_front_initia
                                  ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                  operator_state_front_initia_upd_collapse)
                              done
                            subgoal (* xa \<in> times of the emptied new buffers *)
                            by (simp add: BULK_BENQ_def cin.rep_eq cimage.rep_eq
                                  cset_of_llist.rep_eq
                                  del: label_propagation_op_logic_front_initia
                                  ooo_input_op_logic_front_initia increment_op_logic_front_initia
                                  operator_state_front_initia_upd_collapse)
                            subgoal (* MyPair-filter-new: impossible for a closed xa *)
                              by blast
                            done
                          done
                        done



                      done


                    done














                  done
                done
              subgoal
                using subgraph_inv(1)
                by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
                    sg_after_label_progress_def sg_after_ooo_input_progress_def
                    sg_first_propa_def sg_progress_def)
              subgoal
                using subgraph_inv(2)
                by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
                    sg_after_label_progress_def sg_after_ooo_input_progress_def
                    sg_first_propa_def sg_progress_def)
              subgoal
                by (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
                    os_after_label_input0_def os_after_label_read_input0_def
                    os_after_input_output_def os_input_after_output_def os_after_input_stream_def
                    os_input_after_stream_def os_first_propa_def os_progress_def
                    loop_res_def op_state_base_def operator_state.defs obtain_progress_def
                    drop_caps_def produces_def input_CONSUMES os_inv(1,2))
              subgoal
                by (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
                    os_after_label_input0_def os_after_label_read_input0_def
                    os_after_input_output_def os_input_after_output_def os_after_input_stream_def
                    os_input_after_stream_def os_first_propa_def os_progress_def
                    loop_res_def op_state_base_def operator_state.defs obtain_progress_def
                    drop_caps_def produces_def input_CONSUMES os_inv(1,3,9))
              subgoal
                apply (rule exI[of _ \<open>timestamps (os_label_after_final_output n)\<close>])
                apply (rule exI[of _ \<open>graph (os_label_after_final_output n)\<close>])
                apply (rule exI[of _ \<open>vertices (os_label_after_final_output n)\<close>])
                apply (rule exI[of _ \<open>label (os_label_after_final_output n)\<close>])
                apply (simp add: os_after_final_output_def)
                apply (subst label_propagation_state_extend_decompose)
                apply (subgoal_tac \<open>en1 (os_label_after_loop_updates n) = Inl \<and>
                    de1 (os_label_after_loop_updates n) = projl \<and>
                    is_en1 (os_label_after_loop_updates n) = isl \<and>
                    en2 (os_label_after_loop_updates n) = Inr \<and>
                    de2 (os_label_after_loop_updates n) = projr \<and>
                    is_en2 (os_label_after_loop_updates n) = isr\<close>)
  apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def
                    operator_state.defs
                    del: label_propagation_op_logic_front_initia
                    ooo_input_op_logic_front_initia increment_op_logic_front_initia
                    operator_state_front_initia_upd_collapse)
                apply (subgoal_tac \<open>os_label_after_loop_updates n =
                    operator_state.extend (op_state_base (os_label_after_loop_updates n))
                      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
                        en2 = Inr, de2 = projr, is_en2 = isr,
                        timestamps = timestamps (os_label_after_input0 n),
                        graph = graph (os_label_after_input0 n),
                        vertices = vertices (os_label_after_input0 n),
                        label = label (os_label_after_loop_updates n)\<rparr>\<close>)
                apply (simp add: op_state_base_def operator_state.defs)
                apply (erule ssubst)
                apply simp
                apply (rule loop_updates_extension[OF step_loop[of n],
                      where L=\<open>label (os_label_after_input0 n)\<close>])
                apply (simp add: os_label_after_input0_def os_label_after_read_input0_def
                    os_label_after_first_propa_def op_state_base_def operator_state.defs os_inv(4)
                    input_CONSUMES en1_fst_label_prop_input0_batched de1_fst_label_prop_input0_batched
                    is_en1_fst_label_prop_input0_batched en2_fst_label_prop_input0_batched
                    de2_fst_label_prop_input0_batched is_en2_fst_label_prop_input0_batched)
                done
              subgoal
                using os_inv(1,2,5) buffers_inv(2)
                apply (simp add: ty1_check_def os_after_final_output_def
                    os_after_label_produces_def os_after_second_propa_def
                    os_after_increment_progress_def os_after_label_progress_def
                    os_after_ooo_input_progress_def os_after_loop_progress_def
                    os_after_drop_caps_def os_after_loop_updates_def loop_res_def
                    os_after_label_input0_def os_after_label_read_input0_def
                    os_after_input_output_def os_input_after_output_def
                    os_after_input_stream_def os_input_after_stream_def
                    os_first_propa_def os_progress_def input_events_def
                    input0_msgs_def op_state_base_def operator_state.defs
                    obtain_progress_def fun_upd_def)
                done
              subgoal
                apply (subgoal_tac \<open>\<forall>p. input (os_label_after_loop_updates n) p = []\<close>)
                apply (auto simp add: label_prob_ty2_check_def os_label_after_final_output_def
                    os_label_after_produces_def os_label_after_second_propa_def
                    os_label_after_label_progress_def os_label_after_drop_caps_def
                    drop_caps_def produces_def obtain_progress_def op_state_base_def
                    operator_state.defs outpu_1_after_loop_updates_empty(1)[of n]
                    label_produces_batch_def label_prop_output_batch_def num2_neq)
                subgoal for p
                  by (cases p rule: num2_cases)
                    (simp_all add: input_0_after_loop_updates_empty input_1_after_loop_updates_empty)
                done
              subgoal
                apply (rule allI)
                subgoal for na
                  using Intsum_loop[of n, rule_format, of na]
                    Intsum_loop[of n, rule_format, of \<open>1 :: 3\<close>]
                  by (cases na rule: num3_cases)
                    (auto simp add: os_after_final_output_def os_after_label_produces_def
                      os_after_second_propa_def os_after_increment_progress_def
                      os_after_label_progress_def os_after_ooo_input_progress_def
                      os_after_loop_progress_def os_after_drop_caps_def
                      os_label_after_final_output_def os_label_after_produces_def
                      os_label_after_second_propa_def os_label_after_label_progress_def
                      os_label_after_drop_caps_def op_state_base_def operator_state.defs
                      obtain_progress_def drop_caps_def produces_def)
                done
              subgoal
                using outpu_1_after_loop_updates_empty(4)[of n]
                by (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def
                    input_ocaps_inv_def input_ocaps_inv_op_state_base
                    op_state_base_def operator_state.defs obtain_progress_def)
              subgoal
                by (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
                    os_after_label_input0_def os_after_label_read_input0_def
                    os_after_input_output_def os_input_after_output_def os_after_input_stream_def
                    os_input_after_stream_def os_first_propa_def os_progress_def
                    loop_res_def op_state_base_def operator_state.defs obtain_progress_def
                    drop_caps_def produces_def input_CONSUMES os_inv(9))
              subgoal
                by (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def
                    op_state_base_def operator_state.defs obtain_progress_def
                    outpu_1_after_loop_updates_empty(2)[of n]
                    outpu_1_after_loop_updates_empty(3)[of n]
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((2 :: 3), (1 :: 2))\<close>])
              subgoal
                using buffers_inv by simp

              subgoal (* Use the sequence of have STEPS to prove this one *)
                apply (subgoal_tac \<open>cbufs_after_loop_updates n =
                    cbufs((1, 0) := [], (1, 1) := [], (2, 1) := [])\<close>)
                using dataplane_after_final_output[of n] apply simp
                apply (rule ext)
                apply (simp add: cbufs_after_loop_updates_def loop_res_def
                    cbufs_after_label_read_input0_def cbufs_after_input_output_def
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((1 :: 3), (1 :: 2))\<close>]
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((2 :: 3), (1 :: 2))\<close>])
                done
              subgoal
                apply (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
                    os_after_label_input0_def os_after_label_read_input0_def
                    os_after_input_output_def os_input_after_output_def os_after_input_stream_def
                    os_input_after_stream_def os_first_propa_def os_progress_def input_events_def
                    loop_res_def op_state_base_def operator_state.defs obtain_progress_def os_inv(1,4))
                apply (subst mset_ocaps_updates[of "ltaken n lxs" "ldropn n lxs"
                      "ocaps (os (0 :: 3)) (0 :: 2)"])
                apply (simp add: input_stream_inv)
                apply (rule timely_input_stream_ldrop[OF stream_move(1) input_stream_inv])
                done
              subgoal (* Use the sequence of have STEPS to prove this one *)
                by (rule labels_after_final_output)
              subgoal (* Use the sorried stability fact after second propa. *)
                apply (rule ballI)
                apply (rule impI)
                using labels_stable_after_second_propa_closed[of _ n]
                apply (simp add: timestamps_after_final_output_eq timestamps_after_second_propa_eq
                    os_after_final_output_def os_label_after_final_output_def
                    os_after_label_produces_def os_label_after_produces_def
                    os_after_second_propa_def os_label_after_second_propa_def
                    op_state_base_def operator_state.defs drop_caps_def produces_def)
                done
              subgoal
                by (simp add: os_after_final_output_def os_label_after_final_output_def
                    os_label_after_produces_def os_label_after_second_propa_def
                    os_label_after_label_progress_def os_label_after_drop_caps_def
                    op_state_base_def operator_state.defs drop_caps_def produces_def obtain_progress_def
                    input_0_after_loop_updates_empty input_1_after_loop_updates_empty)
              subgoal
                apply (rule ballI)
                apply (erule UnE)
                subgoal
                  apply (erule UnE)
                  subgoal
                    using label_prop_inv(4)
                    by (metis (mono_tags, lifting) UnCI image_iff in_lset_ltaken_ldropn)
                  subgoal
                    using outpu_0_after_final_output_empty[of n]
                    by (simp add: outputs_at_target_raw_summary inputs_at_target_def BULK_BENQ_def
                        subgraph_inv(1) sg_after_second_propa_def sg_after_increment_progress_def
                        sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def
                        sg_progress_def os_after_final_output_def os_label_after_final_output_def
                        os_after_label_produces_def os_label_after_produces_def
                        os_after_second_propa_def os_label_after_second_propa_def
                        os_label_after_label_progress_def os_label_after_drop_caps_def
                        op_state_base_def operator_state.defs drop_caps_def produces_def obtain_progress_def
                        input_0_after_loop_updates_empty)
                  done
                subgoal
                  using ocaps0_after_final_output_mysnd[of n]
                  by simp
                done
              subgoal
                by (rule label_prop_upd_inv_after_final_output)

              subgoal
                apply (simp add: os_after_final_output_def input_ocaps_inv_op_state_base)
                apply (rule input_ocaps_inv_empty_inputsI)
                apply (rule allI)
                subgoal for p
                  apply (cases \<open>p = (0 :: 2)\<close>)
                  apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                      os_label_after_second_propa_def os_label_after_label_progress_def
                      os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def
                      input_0_after_loop_updates_empty)
                  apply (subgoal_tac \<open>p = (1 :: 2)\<close>)
                  apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                      os_label_after_second_propa_def os_label_after_label_progress_def
                      os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def
                      input_1_after_loop_updates_empty)
                  by (rule num2_neq(1))
                done
              subgoal
                apply (subst wf_label_prop_updates_cong[
                      where os' = \<open>os_label_after_loop_updates n\<close>
                        and S' = \<open>set (input (os_label_after_loop_updates n) (1 :: 2)) \<union>
                        set (cbufs_after_loop_updates n ((1 :: 3), (1 :: 2)) @
                          outpu ((os_after_loop_updates n) (2 :: 3)) (1 :: 2) @
                          map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                            (input ((os_after_loop_updates n) (2 :: 3)) (1 :: 2) @
                             cbufs_after_loop_updates n ((2 :: 3), (1 :: 2)) @
                             outpu (os_label_after_loop_updates n) (1 :: 2)))\<close>])
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (simp add: outputs_at_target_raw_summary subgraph_inv(1)
                    inputs_at_target_def BULK_BENQ_def
                    sg_after_second_propa_def sg_after_increment_progress_def
                    sg_after_label_progress_def sg_after_ooo_input_progress_def
                    sg_first_propa_def sg_progress_def
                    os_after_final_output_def os_label_after_final_output_def
                    os_after_label_produces_def os_label_after_produces_def
                    os_after_second_propa_def os_label_after_second_propa_def
                    os_after_increment_progress_def os_after_label_progress_def
                    os_label_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def os_label_after_drop_caps_def
                    label_produces_batch_def label_prop_output_batch_def drop_caps_def produces_def
                    op_state_base_def operator_state.defs obtain_progress_def
                    input_1_after_loop_updates_empty outpu_1_after_loop_updates_empty
                    ocaps_1_os2_after_loop_updates_empty
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((1 :: 3), (1 :: 2))\<close>]
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((2 :: 3), (1 :: 2))\<close>])
                subgoal
                  by (auto simp add: image_Un image_iff)
                apply (rule wf_after_loop_updates_pending)
                done
              subgoal
                apply (rule label_prop_covered_inv_transportI[OF covered_after_loop_updates[of n]])
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (simp add: outpu_1_after_loop_updates_empty
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((1 :: 3), (1 :: 2))\<close>]
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((2 :: 3), (1 :: 2))\<close>])
                done
              done
            done
          done
        done
      done
  qed
qed

section \<open>Correctness\<close>

abbreviation my_lp_sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close> where
  \<open>my_lp_sg \<equiv> init_subgraph (antichain_from_list \<circ>\<circ> raw_summary)\<close>

abbreviation init_lp_states :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close> where
  \<open>init_lp_states \<equiv> (\<lambda> n. init_op_state
     (if n = 0 then default_internal_summary
      else if n = 1 then (\<lambda> p1 p2. if p1 = 0 then [0] else if p2 = 1 then [0] else [])
      else increment_summary (MyPair 0 1))
     (n \<noteq> 1))\<close>

lemma dataplane_tracker_inv_init_op_state_pernode:
  fixes su :: "('nid :: {enum,linorder, one,zero}, _) location \<Rightarrow> (_, _) location \<Rightarrow> ('t :: {canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,order_ccompare,bots}) antichain"
  assumes D: "dataflow_topology su (-+-)"
    and SU: "\<forall> loc. su loc loc = {}\<^sub>A"
    and R: "reachable_locations su = UNIV"
  shows  "dataplane_tracker_inv (\<lambda> x. init_op_state (isu x) (i x)) (\<lambda>_. []) \<lparr>pt_tr =the (propagate_all su initial_conf), nxt = graph_to_nxt su, summ = su\<rparr>"
  unfolding dataplane_tracker_inv_def
  apply clarsimp
  apply (rule exI[of _ "\<lambda> l. case l of Loc nid (Trg p) \<Rightarrow> {#}\<^sub>z | Loc nid (Src p) \<Rightarrow> to_zmset bots"])
  apply (cases "propagate_all su initial_conf")
  subgoal
    apply (rule FalseE)
    using propagate_all_terminates propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] assms(1,2,3) by fastforce
  subgoal for c
    apply (intro conjI)
    subgoal
      unfolding Src_caps_inv_def by auto
    subgoal
      unfolding Trg_caps_inv_def outputs_at_target_def by auto
    subgoal
      apply simp
      unfolding c_pts_inv_def
      apply (auto simp add: extract_prog_def obtain_progress_def c_pts_change_multiplicities comp_def split: location.splits port.splits)
      subgoal
        apply (subst filter_False)
        subgoal
          unfolding extract_progress_def
          apply auto
          done
        subgoal
          apply simp
          apply (drule propagate_all_preserves_c_pts)
          apply (auto simp add: extract_prog_def obtain_progress_def c_pts_change_multiplicities comp_def split: location.splits port.splits)
          done
        done
      subgoal for nid p
        apply (subst filter_False)
        subgoal
          unfolding extract_progress_def
          apply auto
          done
        subgoal
          apply simp
          apply (drule propagate_all_preserves_c_pts)
          apply (auto simp add: extract_prog_def obtain_progress_def c_pts_change_multiplicities comp_def split: location.splits port.splits)
          done
        done
      done
    subgoal
      unfolding front_inv_def
      apply safe
      subgoal for nid p
        apply (drule propagate_all_frontier_c_imp_correctness[OF _ D R, where loc="Loc nid (Trg p)"])
        using propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] apply simp
        using propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] apply simp
        using propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] apply simp
        apply simp
        done
      done
    subgoal
      unfolding imp_front_inv_def
      apply safe
      subgoal for l
        apply (subgoal_tac \<open>dataflow_topology.inv_imps_work_sum su (-+-) (initial_conf :: (('nid, 'd) location, 't) configuration) \<and> dataflow_topology_from_tree.inv_implications_nonneg (initial_conf :: (('nid, 'd) location, 't) configuration) \<and> dataflow_topology_from_tree.inv_imp_plus_work_nonneg (initial_conf :: (('nid, 'd) location, 't) configuration)\<close>)
        subgoal
          apply clarsimp
          apply (frule propagate_all_frontier_c_imp_correctness[OF _ D R, where loc=l])
          apply (simp_all add: assms(1) propagate_all_preserves_ifrontier)
          done
        subgoal
          using propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] by simp
        done
      done
    subgoal
      unfolding chnls_imp_front_inv_def outputs_at_target_def
      by clarsimp
    subgoal
      unfolding change_deltas_inv_def
      by clarsimp
    subgoal
      using propagation_inv_initial_conf[OF D]
      by (simp add: D propagate_all_preserves_inv propagation_inv_def)
    subgoal
      unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def obtain_progress_def extract_prog_def extract_progress_def
      by auto
    subgoal
      unfolding produ_consu_inter_supported_def
      by auto
    done
  done

lemma dataflow_topology_raw_summary:
  \<open>dataflow_topology (antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list)) (-+-)\<close>
  by (rule dataflow_topology_from_tree.dataflow_topology_axioms[of
        \<open>G (initial_state_input LNil) initial_state_label_prop (initial_state_increment (MyPair 0 1))\<close>,
        unfolded dataflow_tree_to_graph_raw_summary])

lemma raw_summary_diag_empty:
  \<open>\<forall> loc :: (3, 2) location. (antichain_from_list \<circ>\<circ> raw_summary) loc loc = {}\<^sub>A\<close>
  apply (rule allI)
  subgoal for loc
    using loc_3_2_cases[of loc]
    apply (elim disjE; hypsubst_thin)
    apply (simp_all add: raw_summary_def)
    done
  done

lemma intsum_init_lp_states:
  \<open>\<forall> n. intsum (init_lp_states n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
  apply (rule allI)
  subgoal for n
    apply (rule ext)+
    subgoal for p1 p2
      apply (rule num3_cases[of n]; rule num2_cases[of p1]; rule num2_cases[of p2]; hypsubst_thin)
      apply (simp_all add: raw_summary_def default_internal_summary_def zero_myprod_def)
      done
    done
  done

lemma correctness_aux:
  fixes lxs :: \<open>((nat, nat) myprod, nat \<times> nat) event llist\<close>
  assumes T: \<open>timely_input_stream lxs (mset bots)\<close>
    and TS: \<open>\<forall> t \<in> event.time ` lset lxs. mysnd t = 0\<close>
  shows \<open>set_op {||} {||}
    (dataflow_op my_lp_sg
      (G_op (initial_state_input lxs) initial_state_label_prop (init_lp_states 2) (\<lambda>_. [])))
    \<approx> set_spec_op
      (cUn (cUn {||} {||})
        (cimage (\<lambda>t. ((1, 0), (Inr (ccs
             (set (icoll (map (\<lambda>(x, t'). Data t' (projl x))
                 ((outputs_at_target (summ my_lp_sg) init_lp_states >> (\<lambda>_. []) >> inputs_at_target init_lp_states) (1, 0)) @@- lxs) t)
             \<union> all_edges initial_state_label_prop (myfst t))), t)))
          (cUn (cUn (ts lxs) (cset_from_list (map snd ((outputs_at_target (summ my_lp_sg) init_lp_states >> (\<lambda>_. []) >> inputs_at_target init_lp_states) (1, 0)))))
            ((\<lambda> t. MyPair t 0) |`| (cfilter (\<lambda> t. t \<in> myfst ` set (ocaps (init_lp_states 1) 0)) (cset_from_list (timestamps initial_state_label_prop)))))))
      {||}\<close>
  apply (rule label_propagation_correctness[where S=\<open>{||}\<close> and SO=\<open>{||}\<close> and D=\<open>{||}\<close>
        and lxs=lxs and os=init_lp_states and os_input=\<open>initial_state_input lxs\<close>
        and os_label_prop=initial_state_label_prop and cbufs=\<open>\<lambda>_. []\<close>
        and chns=\<open>outputs_at_target (summ my_lp_sg) init_lp_states >> (\<lambda>_. []) >> inputs_at_target init_lp_states\<close>
        and sg=my_lp_sg and T=\<open>[]\<close> and G=\<open>\<lambda>_ _. []\<close> and V=\<open>\<lambda>_. []\<close> and L=\<open>\<lambda>_. id\<close>])
  apply (simp add: init_subgraph_def)
  apply (simp add: init_subgraph_def)
  apply (simp add: operator_state.defs)
  apply simp
  apply simp
  apply (simp add: operator_state.defs)
  apply (simp add: ty1_check_def)
  apply (simp add: label_prob_ty2_check_def)
  apply (rule intsum_init_lp_states)
  apply (simp add: input_ocaps_inv_def)
  apply simp
  apply simp
  apply (rule refl)
  apply (rule refl)
  apply (simp only: init_subgraph_def)
  apply (rule dataplane_tracker_inv_init_op_state_pernode)
  apply (rule dataflow_topology_raw_summary)
  apply (rule raw_summary_diag_empty)
  apply simp
  apply (rule refl)
  apply simp
  apply (simp add: T)
  apply (simp add: labels_inv_def all_edges_def neighbors_def edge_vertices_def)
  apply simp
  apply simp
  apply (simp add: init_subgraph_def outputs_at_target_raw_summary inputs_at_target_def
      BULK_BENQ_def ball_Un TS bots_myprod_def bots_nat_def)
  apply (simp add: label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def
      edge_vertices_def sym_def)
  apply (simp add: input_ocaps_inv_def)
  apply (simp add: wf_label_prop_updates_def init_subgraph_def outputs_at_target_raw_summary
      inputs_at_target_def BULK_BENQ_def)
  apply (simp add: label_prop_covered_inv_def)
  done

lemma correctness:
  fixes lxs :: \<open>((nat, nat) myprod, nat \<times> nat) event llist\<close>
  assumes T: \<open>timely_input_stream lxs (mset bots)\<close>
    and TS: \<open>\<forall> t \<in> event.time ` lset lxs. mysnd t = 0\<close>
  shows \<open>set_op {||} {||} (compile_dataflow (\<lambda> _. [])
      (G (initial_state_input lxs) initial_state_label_prop
        (initial_state_increment (MyPair 0 1)))) \<approx>
    set_spec_op (cimage (\<lambda>t. ((1, 0), (Inr (ccs (set (icoll lxs t)))), t)) (ts lxs)) {||}\<close>
  using correctness_aux[OF T TS] apply -
  unfolding compile_dataflow_def Let_def
  apply (simp only: dataflow_tree_to_graph_raw_summary)
  apply (simp add: init_subgraph_def outputs_at_target_raw_summary inputs_at_target_def
      BULK_BENQ_def all_edges_def neighbors_def)
  done

end
