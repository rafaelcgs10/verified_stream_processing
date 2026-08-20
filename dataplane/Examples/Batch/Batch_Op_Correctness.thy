theory Batch_Op_Correctness

imports
  Batch_Op
  "../../Correctness/Consumes"
  "../../Correctness/Progress"
  "../../Correctness/Produces"
  "../../Correctness/Outputs"
  "../../Correctness/Timely_Collections"
  "../../Correctness/OCapsReorder"
  "../../Correctness/Init"
  "../../Common_Operators/Set_Op"
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

subsection \<open>The Wired Operators\<close>

text \<open>The input, transform, and graph operators of the batch pipeline.\<close>

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_op os f)"

abbreviation "G_op f ip_state os2 chns \<equiv>
   dataflow_tree_to_operator chns (G f (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state) (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2))"


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

lemma correctness_gen:
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
    and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
    and ip_state :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
    and bt_state :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
    and os :: \<open>2 \<Rightarrow> (1, 'd1 + 'd2, 't) operator_state\<close>
    and chns :: \<open>2 \<times> 1 \<Rightarrow> (('d1 + 'd2) \<times> 't) list\<close>
    and sg :: \<open>(2, 1, 't) subgraph\<close>
  assumes
    SUBGRAPH_INV:
    \<open>raw_s = dataflow_tree_to_graph (G f ip_state bt_state)\<close>
    \<open>summ sg = antichain_from_list oo raw_s\<close>
    \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and
    OP_STATE_INV: 
    \<open>ip_state = operator_state.extend (os 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, es = inps\<rparr>\<close>
    \<open>bt_state = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr\<rparr>\<close>
    \<open>ty1_check ip_state (curry cbufs 0)\<close>
    \<open>ty2_check bt_state (curry cbufs 1)\<close>
    \<open>\<forall> n. intsum (os n) = (\<lambda> p1 p2. raw_s (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and
    BUFS_INV: 
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    and
    DT_INV:
    \<open>dataplane_tracker_inv os cbufs sg\<close>
    and S_INV:
    \<open>SP = cUnion (cimage 
      (\<lambda> t. cset_from_list (map (\<lambda> x. ((1, 1), (Inr x, t))) (f (coll ((map (\<lambda> (x, t). Data t (projl x)) (chns (1, 1))) @@- (inps 1)) t))))
      (cUn (ts (inps 1)) (cset_from_list (map snd (chns (1, 1))))))\<close>
    \<open>SO = cset_from_list (map (\<lambda> x. ((1, 1), x)) (outpu (os 1) 1))\<close>
    and
    INP_STREAM_INV:
    \<open>timely_input_stream (inps 1) (mset (ocaps (os 0) 1))\<close>
    and
    OP_EXTRA_INVS:
    \<open>input (os 0) = (\<lambda> _. [])\<close>
    \<open>initia (os 0)\<close>
    \<open>input_ocaps_inv (os 1)\<close>
    \<open>cbufs (0, 0) = []\<close>
  shows 
    \<open>set_op S D (dataflow_op sg (G_op f ip_state bt_state cbufs)) \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms apply -
  (* Rewrite the notation wire once, so the proof body sees the literal. *)
  unfolding tscomp_op_wire_eq
proof (coinduction arbitrary: os sg ip_state bt_state chns cbufs inps SP SO S D raw_s rule: weakBisimWeakUptoBisimCong)
  case SIM1
  show ?case (is "wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2")
  proof -
    define R where "R = ?R"
    show ?thesis 
      apply -
      unfolding R_def[symmetric]
      subgoal premises prems2
        unfolding wsim_def dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def
        apply simp
        apply (intro allI conjI impI)
        apply (elim step_builder_op_elim step_set_op_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim conjE ; 
            clarsimp simp only: IO.simps ; hypsubst_thin ? ; clarsimp simp flip: cin.rep_eq split: event.splits llist.splits option.splits sum.splits prod.splits if_splits ; hypsubst_thin?)
        subgoal 
          apply -
          apply (intro exI conjI relcomppI)
             apply (rule step_set_spec_op_intro_Out)
                apply (rule refl)
               apply simp
              apply simp
             apply (rule refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (intro exI conjI)
          unfolding wsim_def dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def
                      apply simp
                      apply (simp add: SIM1)
                     apply (simp add: SIM1)
                    apply (simp add: SIM1(1))
                    apply (simp add: SIM1)
          subgoal premises
            using SIM1
            unfolding ty1_check_def
            by (fastforce simp add:  my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1
            unfolding ty2_check_def
            by (fastforce simp add:  my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          using SIM1 apply fastforce+
          done
                defer
        subgoal for d t
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ "os(1 := consumes (os 1) 1 t d)"])
          apply (rule exI[of _ sg])
          apply (rule exI[of _ "BTL (1, 1) cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
          unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def
          subgoal
            by (simp add: map_tl SIM1(3-) comp_op_def if_distrib  consumes_def add_caps_def BTL_def enum_num1_def operator_state.defs fun_upd_def)
          subgoal
            by (simp add: BHD_map cUn_assoc SIM1  flip:BULK_BENQ_assoc cinsert_code)
                    apply (simp_all add: SIM1)
          subgoal
            using SIM1
            unfolding ty1_check_def
            by (auto simp add: BTL_def BHD_def  my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(5,6,7)
            unfolding ty2_check_def
            apply (auto simp add:  operator_state.defs comp_def fun_upd_def BTL_def BHD_def consumes_def add_caps_def BENQ_def my_summ_def BULK_BENQ_def outputs_at_target_def split: option.splits if_splits prod.splits)
            apply (meson UnCI img_fst in_set_tlD)
            done
          subgoal premises temp
            using SIM1(10) apply -
            apply (rule dataplane_tracker_inv_consumes[where xs="tl (cbufs (1, 1))"])
               apply assumption
            using temp(2,3) apply (simp add: BHD_def list.map_sel(1))
            subgoal
              using SIM1(1,2) 
              using  dataflow_topology_from_tree.dataflow_topology_axioms
              by metis
            subgoal              
              apply (rule graph_summar_nt)
                 apply (rule refl)+
                apply (rule SIM1(2)[unfolded SIM1(1)])
               apply (auto simp add: SIM1 comp_def)
              done
            done
          subgoal
            using SIM1(16) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def
            apply clarsimp
            apply (metis (no_types, lifting) UNIV_I UN_iff capability.sel(1) imageI snd_conv)
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
            done
          done
               defer
        subgoal 
          (* batch_op logic  *)
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ "os( 1 := (os 1)\<lparr> 
            outpu := \<lambda>p. outpu (os 1) 1 @
                   map (\<lambda>x. (Inr (fst x), capability.time (snd x)))
                    (concat
                      (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (map (\<lambda>x. projl (fst x)) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))
                        (remdups (map snd (filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))),
             ocaps := \<lambda>p. list_diff (ocaps (os 1) 1) (filter (\<lambda>t. \<not> frontier_less_equal (front (os 1) 1) t) (ocaps (os 1) 1)),
             input := \<lambda>p. filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<longrightarrow> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1),
             produ := produ (os 1) @
                map (\<lambda>x. (1, capability.time (snd x), 1))
                 (concat
                   (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (map (\<lambda>x. projl (fst x)) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))
                     (remdups (map snd (filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))),
             inter := operator_state.inter (os 1) @ map (\<lambda>x. (1, x, - 1)) (filter (\<lambda>t. \<not> frontier_less_equal (front (os 1) 1) t) (ocaps (os 1) 1)) \<rparr>)"])
          apply (rule exI[of _ sg])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
          unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def
                      apply (simp add: filter_True filter_False list_emb_Nil2 BULK_BENQ_right_empty BULK_BENQ_left_empty map_tl SIM1(3-) drop_caps_def produces_def comp_def split_beta comp_op_def if_distrib  consumes_def add_caps_def BTL_def enum_num1_def operator_state.defs fun_upd_def)
                     apply (rule arg_cong2[where f=set_spec_op])
          subgoal premises temp
            apply (simp add: SIM1(11,12,9))
            apply (subst (1 2) cUn_assoc)
            apply (rule arg_cong2[where f=cUn])
             apply simp
            apply (subgoal_tac "\<forall>x. x \<in> lset (inps 1) \<longrightarrow> is_Data x \<longrightarrow> frontier_less_equal (front (os 1) 1) (event.time x)")
             defer
            subgoal
              apply safe       
              subgoal for x
                using timely_input_stream_frontier_less_equal[OF SIM1(13), rule_format, of x] apply simp
                apply (cases x; clarsimp; hypsubst_thin?)
                subgoal for t d
                  using SIM1(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
                  apply safe
                  unfolding front_inv_def imp_front_inv_def
                  apply (drule spec[of _ 1])
                  apply (drule spec[of _ 1])
                  apply (drule spec[of _ "Loc 1 (Trg 1)"])
                  apply (rule frontier_less_equal_le_trans[rotated])
                   apply (rule order.trans)
                    apply assumption
                   apply assumption
                  subgoal for caps
                    unfolding Src_caps_inv_def
                    apply (drule spec[of _ 0])
                    apply (drule spec[of _ 1])
                    unfolding c_pts_inv_def
                    apply (drule spec[of _ "Loc 0 (Src 1)"])
                    apply simp
                    apply (rule frontier_less_equal_ifrontier_from_Src[where s=0 and nid=0 and os=os and nt="subgraph.nxt sg", simplified])
                    subgoal
                      using SIM1(1,2) 
                      using  dataflow_topology_from_tree.dataflow_topology_axioms
                      by metis
                      apply (drule sym[of _ "to_zmset (ocaps (os 0) 1)"])
                      back
                      apply (simp add: c_pts_change_multiplicities SIM1(1,2) comp_def  zmset_filter_extract_progress_Src_consumes_diff)
                    subgoal 
                      using graph_summar_nt[unfolded graph_summar_nt_def , OF _  SIM1(2)[unfolded SIM1(1)] , simplified, OF dataflow_tree_to_graph_to_my_summ[symmetric], where os=os] apply -
                      apply (drule meta_mp)
                      using SIM1(1,2,8) dataflow_tree_to_graph_to_my_summ apply fastforce 
                      apply (drule meta_mp)
                       apply (clarsimp simp add: SIM1(1,2,3) comp_def)
                      apply (elim conjE)
                      apply (clarsimp simp add: SIM1(1,2,3) comp_def)
                      apply (drule spec2[of _ 1 0], drule mp)
                       back
                       apply (simp_all add: bi_unique_def)
                      subgoal premises
                        unfolding graph_to_nxt_def
                        apply auto
                        subgoal
                          unfolding my_summ_def inj_on_def
                          apply (auto simp add: antichain_from_list_singleton is_empty_antichain_iff split: prod.splits if_splits intro!: find_Some_singleton)
                          done
                        done
                      subgoal
                        apply (rule path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF]])
                         defer
                         apply assumption
                        apply (subgoal_tac " dataflow_topology (summ sg) (-+-)")
                        using SIM1(1,2) [unfolded comp_def]
                        using  dataflow_topology_from_tree.dataflow_topology_axioms[unfolded comp_def]
                         apply simp
                        subgoal
                          using SIM1(1,2) 
                          using  dataflow_topology_from_tree.dataflow_topology_axioms
                          by metis
                        done
                      done
                    apply assumption
                    done
                  done
                done
              done
            apply (subgoal_tac "\<forall> t \<in> snd ` set ((outputs_at_target (summ sg) os >> cbufs) (1, 1)). frontier_less_equal (front (os 1) 1) t")
             defer
            subgoal
              apply safe
              subgoal for _ a t
                apply simp
                using SIM1(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
                apply safe
                unfolding front_inv_def imp_front_inv_def
                apply (drule spec[of _ 1])
                apply (drule spec[of _ 1])
                apply (drule spec[of _ "Loc 1 (Trg 1)"])
                unfolding chnls_imp_front_inv_def
                apply (drule spec[of _ 1])
                apply (drule spec[of _ 1])
                apply (drule bspec[of _ _ t])
                subgoal 
                  by blast
                apply (drule frontier_less_equal_le_trans)
                 apply (rule order.trans[rotated])
                  apply assumption+
                done
              done
            apply (simp add: cimage_cUn if_distrib[where f=input] SIM1(1,2) outputs_at_target_my_summ inputs_at_target_def)
            apply (subst (1) cUn_assoc)
            apply (rule arg_cong2[where f=cUn])
             apply simp
            apply (subst coll_lshift)
            subgoal using timely_input_stream_expires[OF SIM1(13)] by auto
            apply (subst coll_lshift)
            subgoal using timely_input_stream_expires[OF SIM1(13)] by auto
            apply (subst coll_lshift)
            subgoal using timely_input_stream_expires[OF SIM1(13)] by auto
            apply (subst coll_lshift)
            subgoal using timely_input_stream_expires[OF SIM1(13)] by auto
            unfolding BULK_BENQ_def
            apply simp
            apply (simp add: split_beta cimage_cUn)
            apply (subst (1) cimage_cfilter_clean; simp)
            apply (subst (4) cUn_left_commute)
            apply (subst (1) cUn_left_commute)
            apply (simp flip: cUn_assoc)
            apply (simp add:  cimage_cUnion comp_def Countable_Set_Type.cset.map_comp)
            apply (rule arg_cong2[where f=cUn])
            subgoal
              apply (rule arg_cong2[where f=cUn])
              subgoal
                apply (rule arg_cong2[where f=cUn])
                subgoal
                  apply (subst (1) cset_cfilter_split[where P="\<lambda>(_, t). \<not> (t \<in> set (ocaps (os 1) 1) \<longrightarrow> frontier_less_equal (front (os 1) 1) t)"])
                  apply (simp add: comp_def split_beta)
                  apply (rule arg_cong2[where f=cUn])
                  subgoal
                    apply (auto 0 0 simp add: image_iff split_beta simp flip: cin.rep_eq)
                    subgoal for dd t d
                      apply (rule cBexI[of _ t])
                       apply auto
                      apply (subst (asm) (2 3) filter_False)
                      subgoal
                        by force
                      subgoal
                        by force
                      apply simp
                      unfolding coll_def
                      apply (subst (asm) lfilter_False)
                      subgoal
                        by (auto split: event.splits)
                      apply auto
                      done
                    subgoal for dd d t'
                      apply (rule cBexI[of _ "(d, t')"])
                       apply simp_all
                      apply (subst (2 3) filter_False)
                      subgoal
                        by force
                      subgoal
                        by force
                      unfolding coll_def
                      apply (subst lfilter_False)
                      subgoal
                        by (auto split: event.splits)
                      apply auto
                      done
                    done
                  subgoal
                    apply (auto 0 0 simp add: image_iff split_beta simp flip: cin.rep_eq)
                    subgoal for dd t d
                      apply (rule cBexI[of _ t])
                       apply auto
                      apply (smt (verit, best) filter_cong split_def)
                      done
                    subgoal for dd t d
                      apply (rule cBexI[of _ t])
                       apply auto                   
                      apply (smt (verit, best) filter_cong split_def)
                      done
                    subgoal for dd d t
                      apply (rule cBexI[of _ "(d, t)"])
                       apply auto                   
                      apply (smt (verit, best) filter_cong split_def)
                      done
                    subgoal for dd d t
                      apply (rule cBexI[of _ "(d, t)"])
                       apply auto                   
                      apply (smt (verit, best) filter_cong split_def)
                      done
                    done
                  done
                subgoal
                  apply (auto 0 0 simp add: image_iff split_beta simp flip: cin.rep_eq)
                  subgoal for  t d
                    apply (rule cBexI[of _ t])
                     apply auto         
                    apply (smt (verit, best) filter_cong split_def)
                    done
                  subgoal for  t d
                    apply (rule cBexI[of _ t])
                     apply auto         
                    apply (smt (verit, best) filter_cong split_def)
                    done
                  done
                done
              subgoal
                apply (auto 0 0 simp add: image_iff split_beta simp flip: cin.rep_eq)
                subgoal for x  t d
                  apply (rule cBexI[of _ "(x, t)"])
                   apply auto         
                  using filter_cong split_def apply (smt (verit, best) Un_iff snd_conv)
                  done
                subgoal for x  t d
                  apply (rule cBexI[of _ "(x, t)"])
                   apply auto         
                  using filter_cong split_def apply (smt (verit, best) Un_iff snd_conv)
                  done
                done
              done
            subgoal
              apply (auto 0 0 simp add: image_iff split_beta simp flip: cin.rep_eq)
              subgoal for x  t d
                apply (rule cBexI[of _ "(x, t)"])
                 apply auto         
                using filter_cong split_def apply (smt (verit, best) Un_iff snd_conv)
                done
              subgoal for x  t d
                apply (rule cBexI[of _ "(x, t)"])
                 apply auto         
                using filter_cong split_def apply (smt (verit, best) Un_iff snd_conv)
                done
              done
            done
                     apply (simp_all add: SIM1(1,2,3))

          subgoal
            using SIM1
            unfolding ty1_check_def
            by (auto simp add: BTL_def BHD_def   my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(5,6,7)
            unfolding ty2_check_def
            apply (auto simp add: operator_state.defs comp_def fun_upd_def BTL_def BHD_def  consumes_def add_caps_def BENQ_def my_summ_def BULK_BENQ_def outputs_at_target_def split: option.splits if_splits prod.splits)
             apply (meson UnCI img_fst in_set_tlD)+
            done
          subgoal
            by (simp add: SIM1(1,2,3,8))
          subgoal premises temp            
            apply (rule dataplane_tracker_inv_produces_drops[])
                        apply simp_all
                     defer
            subgoal
              by (auto simp add: comp_def enum_num1_def)
            subgoal
              by (auto simp add: comp_def enum_num1_def)
            subgoal
              by (auto simp add: comp_def enum_num1_def)
            subgoal
              by (auto simp add: comp_def enum_num1_def)
            subgoal
              by (auto simp add: comp_def enum_num1_def)
            subgoal 
              by (auto simp add: comp_def filter_True filter_False list_emb_Nil2 BULK_BENQ_right_empty BULK_BENQ_left_empty)
            subgoal
              apply (rule graph_summar_nt)
                 apply (rule refl)+
                apply (rule SIM1(2)[unfolded SIM1(1)])
               apply (auto simp add: SIM1 comp_def)
              done
            subgoal
              using SIM1(3) by auto
            subgoal
              using SIM1(10) by auto
            subgoal 
              apply (simp add: SIM1(1,2) )
              using dataflow_topology_from_tree.dataflow_topology_axioms
              apply (metis dataflow_tree_to_graph_to_my_summ)
              done
            done
          subgoal
            using SIM1(13) by auto
          subgoal
            using SIM1(14) by auto
          subgoal
            using SIM1(15) by auto
          subgoal
            using SIM1(16) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def
            apply clarsimp
            apply (metis (mono_tags, lifting)
                \<open>initia bt_state \<Longrightarrow> filter (\<lambda>t. \<not> frontier_less_equal (front bt_state 1) t) (ocaps bt_state 1) \<noteq> [] \<Longrightarrow> \<forall>n. (n = 1 \<longrightarrow> intsum (os 1) = (\<lambda>p1 p2. my_summ (Loc 1 (Trg 1)) (Loc 1 (Src 1)))) \<and> (n \<noteq> 1 \<longrightarrow> intsum (os n) = (\<lambda>p1 p2. my_summ (Loc n (Trg 1)) (Loc n (Src 1))))\<close>
                group_cancel.rule0 in_set_simps(2) my_summ_def prod.sel(2) zero_one)
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
            done
          done
              prefer 3
        subgoal  
          apply (rule FalseE)
          apply (drule propagate_all_terminates[unfolded not_def, rule_format, rotated 5])
          subgoal 
            apply (simp add: SIM1(1,2) )
            using dataflow_topology_from_tree.dataflow_topology_axioms
            apply (metis dataflow_tree_to_graph_to_my_summ)
            done
              apply simp_all
          subgoal
            using SIM1(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
            unfolding propagation_inv_def
            apply clarsimp
            done
          subgoal
            using SIM1(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
            unfolding propagation_inv_def
            apply clarsimp
            done
          subgoal for loc
            apply (subgoal_tac "graph_summar_nt (summ sg) (subgraph.nxt sg) os")
             defer
            subgoal
              apply (rule graph_summar_nt)
                 apply (rule refl)+
                apply (rule SIM1(2)[unfolded SIM1(1)])
               apply (auto simp add: SIM1 comp_def)
              done
            subgoal
              apply (cases loc; simp)
              subgoal for nid lp
                apply (cases lp; simp)
                unfolding graph_summar_nt_def
                 apply auto
                done
              done
            done
          subgoal
            using SIM1(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
            unfolding propagation_inv_def
            apply clarsimp
            done
          done
        subgoal for st os'
          using SIM1(5) apply simp
          apply hypsubst_thin
          apply (intro exI conjI relcomppI impI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ "os(1 := fst (obtain_progress (os 1)))"])
          apply (rule exI[of _ "sg\<lparr>pt_tr := change_multiplicities (summ sg) (extract_progress 1 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
          subgoal premises prems
            using prems(1) apply -
            apply (simp add:  SIM1 dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            unfolding ooo_input_op_logic_def
            apply (simp add: operator_state.defs comp_def notifier_op_def SIM1(3-) dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            done
          subgoal
            by (simp add: SIM1)
          subgoal premises temp
            using SIM1(1,2,3)
            unfolding graph_summar_nt_def consumes_def add_caps_def
            by auto
          subgoal
            using SIM1
            unfolding ty1_check_def
            by (auto simp add: BTL_def BHD_def   my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(4,6)
            apply (auto simp add: operator_state.defs comp_def fun_upd_def BTL_def BHD_def  consumes_def add_caps_def BENQ_def my_summ_def BULK_BENQ_def outputs_at_target_def split: option.splits if_splits prod.splits)
            done
          subgoal
            using SIM1(5,7)
            apply (auto simp add: ty2_check_def operator_state.defs comp_def fun_upd_def BTL_def BHD_def  obtain_progress_def split: option.splits if_splits prod.splits)
            done
          subgoal
            by (simp add: SIM1 obtain_progress_def)
          subgoal
            apply (subst dataplane_tracker_inv_clean)
              defer
              apply (rule dataplane_tracker_inv_progress)
            using SIM1(10) apply assumption
                apply simp_all
            using SIM1(1,2) apply simp
            subgoal
              using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
              by metis
            subgoal              
              apply (rule graph_summar_nt)
                 apply (rule refl)+
                apply (rule SIM1(2)[unfolded SIM1(1)])
               apply (auto simp add: SIM1 comp_def)
              done
            unfolding obtain_progress_def
             apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(13)
            apply simp
            done
          subgoal
            using SIM1(14) by auto
          subgoal
            using SIM1(15) by auto
          subgoal
            using SIM1(16) apply -
            unfolding obtain_progress_def input_ocaps_inv_def
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
            done
          done
        subgoal for st os'
          (* report progress *)
          using SIM1(4) apply simp
          apply hypsubst_thin
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ "os(0 := fst (obtain_progress (os 0)))"])
          apply (rule exI[of _ "sg\<lparr>pt_tr := change_multiplicities (summ sg) (extract_progress 0 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
          subgoal premises prems
            using prems(1) apply -
            apply (simp add:  SIM1 dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            unfolding ooo_input_op_logic_def
            apply (simp add: operator_state.defs comp_def notifier_op_def SIM1(2-) dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            done
          subgoal
            by (simp add: SIM1)
          subgoal premises temp
            using SIM1(1,2,3)
            unfolding graph_summar_nt_def consumes_def add_caps_def
            by auto
          subgoal
            using SIM1
            unfolding ty1_check_def
            by (auto simp add: BTL_def BHD_def   my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(4,6)
            unfolding ty1_check_def
            by (auto simp add: operator_state.defs BTL_def BHD_def obtain_progress_def  my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(5,7)
            apply (auto simp add: ty2_check_def operator_state.defs comp_def fun_upd_def BTL_def BHD_def  obtain_progress_def split: option.splits if_splits prod.splits)
            done
          subgoal
            by (simp add: SIM1 obtain_progress_def)
          subgoal
            apply (subst dataplane_tracker_inv_clean)
              defer
              apply (rule dataplane_tracker_inv_progress)
            using SIM1(10) apply assumption
                apply simp_all
            using SIM1(1,2) apply simp
            subgoal
              using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
              by metis
            subgoal              
              apply (rule graph_summar_nt)
                 apply (rule refl)+
                apply (rule SIM1(2)[unfolded SIM1(1)])
               apply (auto simp add: SIM1 comp_def)
              done
            unfolding obtain_progress_def
             apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(13) apply -
            unfolding obtain_progress_def
            apply simp
            done
          subgoal
            unfolding obtain_progress_def
            using SIM1(14) by auto
          subgoal
            unfolding obtain_progress_def
            using SIM1(15) by auto
          subgoal
            using SIM1(16) apply -
            unfolding obtain_progress_def input_ocaps_inv_def
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
            done
          done
        subgoal for c
          (* propagate_all *)
          using SIM1(5) apply simp
          apply hypsubst_thin
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ "os(1 := (os 1)\<lparr> front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))), initia := True \<rparr> )"])
          apply (rule exI[of _ "sg\<lparr>pt_tr := c\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
                      apply (simp_all add: SIM1)
          subgoal premises temp
            apply (simp add: dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            unfolding ooo_input_op_logic_def
            apply (simp add: operator_state.defs comp_def notifier_op_def SIM1(2-) dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            done
          subgoal
            unfolding inputs_at_target_def
            by (clarsimp simp add: BULK_BENQ_def  if_distrib[of input])
          subgoal
            using SIM1(6,4) apply -
            unfolding ty1_check_def operator_state.defs
            apply (auto simp add: SIM1 BTL_def BHD_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
            done
          subgoal
            using SIM1(5,7)
            apply (auto simp add: ty2_check_def operator_state.defs comp_def fun_upd_def BTL_def BHD_def  obtain_progress_def split: option.splits if_splits prod.splits)
            done
          subgoal
            apply (subst dataplane_tracker_inv_clean[where os'="os(1:= (os 1)\<lparr> front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))) \<rparr> )"])
              apply simp_all
            apply (subgoal_tac "propagate_all (antichain_from_list \<circ>\<circ> my_summ) (pt_tr sg) = Some c \<Longrightarrow> dataplane_tracker_inv (map_entry 1 (front_update (\<lambda>_. frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg p))))) os) cbufs (sg\<lparr>pt_tr := c\<rparr>)")
            subgoal
              by simp
            subgoal
              apply (rule dataplane_tracker_inv_front_update)
              subgoal
                apply (simp add: SIM1)
                using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                apply metis
                done
              subgoal
                apply (simp add: SIM1)
                unfolding reachable_locations_def
                apply (auto simp add: split_beta)
                   apply (metis (no_types, lifting) loc_2_1_cases rangeI range_fst surjD)
                  apply (metis (no_types, lifting) loc_2_1_cases rangeI range_fst surjD)
                 apply (smt (verit, ccfv_threshold) is_empty_antichain_not_empty_list loc_2_1_cases my_summ_def zero_one)
                apply (smt (verit, ccfv_threshold) is_empty_antichain_not_empty_list loc_2_1_cases my_summ_def zero_one)
                done
                apply (simp add: SIM1)
              subgoal              
                apply (rule graph_summar_nt)
                   apply (rule refl)+
                  apply (rule SIM1(2)[unfolded SIM1(1)])
                 apply (auto simp add: SIM1 comp_def)
                done
              apply (simp add: SIM1)
              done
            done
          subgoal
            using SIM1(16,17) apply -
            apply (frule propagate_all_frontier_c_imp_correctness[where loc="Loc 1 (Trg 1)"]; (clarsimp simp add: SIM1)?)
            subgoal
              using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
              apply metis
              done
            subgoal
              unfolding reachable_locations_def
              apply (auto simp add: image_iff split_beta )
              using loc_2_1_cases apply blast
              using loc_2_1_cases apply blast
               apply (smt (verit, del_insts) is_empty_antichain_not_empty_list loc_2_1_cases my_summ_def zero_one)+
              done
            subgoal
              using SIM1(10)[unfolded dataplane_tracker_inv_def propagation_inv_def SIM1(1,2)] by auto
            subgoal
              using SIM1(10)[unfolded dataplane_tracker_inv_def propagation_inv_def SIM1(1,2)] by auto
            subgoal
              using SIM1(10)[unfolded dataplane_tracker_inv_def propagation_inv_def SIM1(1,2)] by auto
            subgoal
              using SIM1(16) apply -
              unfolding obtain_progress_def input_ocaps_inv_def
              apply (auto simp add: operator_state.defs)
              done
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
            done
          done
        subgoal for x t xs
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ "os(1 := (os 1)\<lparr> outpu := (\<lambda> _. xs) \<rparr> )"])
          apply (rule exI[of _ "sg"])
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ "cinsert ((1, 1), x, t) S"])
          apply (rule exI[of _ D])
          apply (intro conjI)
                      apply (simp_all add: SIM1)
          subgoal
            unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def
            apply (simp add: map_tl SIM1(3-) comp_def split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs fun_upd_def)
            done
          subgoal
            apply (simp add: map_tl SIM1(2-) split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs)
            done
          subgoal
            using SIM1(6,4)
            by (auto simp add: ty1_check_def  operator_state.defs split: sum.splits)
          subgoal
            using SIM1(7,5)
            by (auto simp add: ty2_check_def  operator_state.defs split: sum.splits)
          subgoal premises
            using SIM1(10) apply -
            apply (rule dataplane_tracker_inv_update_outputs_outside)
               apply assumption
              apply simp_all
            subgoal
              by (simp add: my_summ_def SIM1)
            subgoal
              apply (rule graph_summar_nt)
                 apply (rule refl)+
                apply (rule SIM1(2)[unfolded SIM1(1)])
               apply (auto simp add: SIM1 comp_def)
              done
            done
          subgoal
            using SIM1(16) apply -
            unfolding obtain_progress_def input_ocaps_inv_def
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
            done
          done
        subgoal for x t xs
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ "os(0 := (os 0)\<lparr> outpu := (\<lambda> _. xs) \<rparr>)"])
          apply (rule exI[of _ "sg"])
          apply (rule exI[of _ "BENQ (1, 1) (x, t) cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ "S"])
          apply (rule exI[of _ D])
          apply (intro conjI)
                      apply (simp_all add: SIM1)
          subgoal
            unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def
            by (simp add: BENQ_def map_tl SIM1(2-) comp_def split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs fun_upd_def)
          subgoal
            apply (simp add: map_tl SIM1(2-) split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs)
            apply (rule arg_cong2[where f=set_spec_op])
             apply simp_all
            apply (rule arg_cong2[where f=cUn])
             apply simp_all
            apply (cases "{(nid', p'). antichain_from_list (if nid' = (0 :: 2) then [0 :: 't] else []) \<noteq> {}\<^sub>A} = {}")
            subgoal 
              apply (rule FalseE)
              apply (clarsimp simp add: if_distrib[of antichain_from_list])
              apply (drule spec[of _ 2])
              apply simp               
              apply (auto 0 0 simp add:  my_summ_def antichain_from_list_singleton split: prod.splits)
              done
            subgoal
              unfolding BENQ_def BULK_BENQ_def inputs_at_target_def outputs_at_target_def
              apply (clarsimp simp add:  my_summ_def antichain_from_list_singleton split: prod.splits)
              done
            done
          subgoal
            using SIM1(6,4)
            by (auto simp add: ty1_check_def BENQ_def operator_state.defs split: sum.splits)
          subgoal
            using SIM1(6,7,5,4) apply -
            apply (auto simp add: ty1_check_def ty2_check_def BENQ_def operator_state.defs split: sum.splits)
            done
          subgoal premises temp
            using SIM1(10) apply -
            apply (rule dataplane_tracker_inv_update_outputs[where nid=0 and xs="[(x, t)]" and ys=xs and p=1])
                 apply assumption
            using temp apply (simp add: operator_state.defs)
            using temp apply simp
            unfolding BENQ_def
              apply simp
             apply (simp add: SIM1 my_summ_def)
            using mem_antichain_nonempty in_antichain_singleton apply force
            subgoal
              apply (rule graph_summar_nt)
                 apply (rule refl)+
                apply (rule SIM1(2)[unfolded SIM1(1)])
               apply (auto simp add: SIM1 comp_def)
              done
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
            done
          done
        defer
        subgoal
          (* input_op logic *)
          apply (intro conjI impI allI)
          subgoal
            (* LNIl *)
            apply (intro exI conjI relcomppI)
               apply (rule rtranclp.intros(1))
              apply (rule bisim_refl)
             defer
             apply (rule wbisim_refl)
            apply (rule wb_upto_b_base)
            unfolding R_def[simplified]
            apply (rule exI[of _ "os(0 := (os 0)\<lparr> ocaps := (\<lambda> _. []), inter := inter (os 0) @ map (\<lambda> t. (1, t, -1)) (ocaps (os 0) 0) \<rparr>)"])
            apply (rule exI[of _ "sg"])
            apply (rule exI[of _ cbufs])
            apply (rule exI[of _ "inps"])
            apply (rule exI[of _ "S"])
            apply (rule exI[of _ D])
            apply (intro conjI)
                        apply (simp_all add: SIM1)
            subgoal
              unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def drop_caps_def add_caps_singleton BTL_def BHD_def produces_def
              by (simp add: map_tl SIM1(2-) comp_def split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs fun_upd_def filter_True filter_False list_emb_Nil2 BULK_BENQ_right_empty BULK_BENQ_left_empty)
            subgoal
              unfolding inputs_at_target_def
              by (clarsimp simp add: BULK_BENQ_def  )
            subgoal
              using SIM1(6,4) apply -
              unfolding ty1_check_def operator_state.defs
              apply (auto simp add: SIM1 BTL_def BHD_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
              done
            subgoal     
              using SIM1(5,7)
              apply (auto simp add: ty2_check_def operator_state.defs comp_def fun_upd_def BTL_def BHD_def  obtain_progress_def split: option.splits if_splits prod.splits)
              done
            subgoal premises temp
              using SIM1(10) apply -
              apply (rule dataplane_tracker_inv_produces_drops[where os=os and cbufs=cbufs and sg=sg and
                    nid=0 and nocaps="(\<lambda> _. [])" and ninput="input (os 0)" and noutput="(outpu (os 0))(1 := outpu (os 0) 1)" and
                    nprodu="produ (os 0)" and ninter="inter (os 0) @ map (\<lambda> t. (1, t, -1)) (ocaps (os 0) 0)" and drops ="ocaps (os 0)", simplified])
              subgoal
                apply (simp add: SIM1)
                using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                apply metis
                done
                       apply fastforce
              subgoal
                using SIM1(14) by auto
                     apply (rule refl)+
              subgoal
                by (auto simp add: comp_def enum_num1_def)
                   apply simp_all
              subgoal             
                apply (simp flip: SIM1(3))
                apply (rule graph_summar_nt)
                   apply (rule refl)+
                  apply (rule SIM1(2)[unfolded SIM1(1)])
                 apply (auto simp add: SIM1 comp_def)
                done
              subgoal
                apply (simp add: SIM1)
                done
              done
            subgoal
              unfolding timely_input_stream_def
              apply (auto simp add: operator_state.defs zero_enat_def timely_progress_def vacant_def)
              using timely_monotone.intros(1) apply blast+
              done
            subgoal
              using SIM1(17) apply -
              unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
              apply clarsimp
              done
            done
          subgoal for A lxs t d
            (* Data *)
            apply (intro exI conjI relcomppI)
               apply (rule rtranclp.intros(1))
              apply (rule bisim_refl)
             defer
             apply (rule wbisim_refl)
            apply (rule wb_upto_b_base)
            unfolding R_def[simplified]
            apply (rule exI[of _ "os(0 := (os 0)\<lparr> outpu := (outpu (os 0))(1 := outpu (os 0) 1 @ [(Inl d, t)]), produ := produ (os 0) @ [(1, t, 1)] \<rparr>)"])
            apply (rule exI[of _ "sg"])
            apply (rule exI[of _ cbufs])
            apply (rule exI[of _ "\<lambda> _. lxs"])
            apply (rule exI[of _ "S"])
            apply (rule exI[of _ D])
            apply (intro conjI)
                        apply (simp_all add: SIM1)
            subgoal
              unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def add_caps_singleton BTL_def BHD_def produces_def
              by (simp add: map_tl SIM1(2-) comp_def split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs fun_upd_def )
            subgoal
              unfolding inputs_at_target_def produces_def
              apply (clarsimp simp add: BULK_BENQ_def  produces_def)
              apply (rule arg_cong2[where f=set_spec_op])
               apply simp_all
              apply (rule arg_cong2[where f=cUn])
               apply simp_all
              unfolding operator_state.defs
              apply simp
              apply (subst (1 2 3 4 5 6) coll_lshift)
                  apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
                 apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
                apply simp
                apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
               apply (metis SIM1(13) timely_input_stream_expires)
              apply simp
              apply (subst (1 2 3 4 5 6) coll_LCons_Data; simp?)
                apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
               apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
              apply (auto 0 0 simp add: image_iff split_beta cimage_cUn split_def cong: filter_cong split: if_splits)
              subgoal
                using empty_append_eq_id
                by (smt (verit) filter_cong split_def)
                    apply (metis snd_conv)
                   apply (metis snd_conv)
                  apply (metis snd_conv)
                 apply blast+
                apply (metis snd_conv)
               apply (metis snd_conv)
              apply (metis snd_conv)
              done
            subgoal
              using SIM1(6,4) apply -
              unfolding ty1_check_def operator_state.defs
              apply (auto simp add: SIM1 BTL_def BHD_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
              done
            subgoal     
              using SIM1(5,7)
              apply (auto simp add: ty2_check_def operator_state.defs comp_def fun_upd_def BTL_def BHD_def  obtain_progress_def split: option.splits if_splits prod.splits)
              done
            subgoal premises temp
              apply (subgoal_tac "dataplane_tracker_inv (os(0 := os 0\<lparr>outpu := (outpu (os 0))(1 := outpu (os 0) 1 @ [(Inl d, t)]), produ := produ (os 0) @ [(1, t, 1)]\<rparr>)) cbufs sg")
              subgoal
                by fast
              subgoal
                apply (rule dataplane_tracker_inv_produces_drops[where os=os and cbufs=cbufs and sg=sg and
                      nid=0 and nocaps="ocaps (os 0)" and ninput="input (os 0)" and noutput="(outpu (os 0))(1 := outpu (os 0) 1 @ [(Inl d, t)])" and
                      nprodu="produ (os 0) @ [(1, t, 1)]" and ninter="inter (os 0)" and drops ="\<lambda> _. []", simplified])
                subgoal
                  apply (simp add: SIM1)
                  using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                  apply metis
                  done
                         apply fastforce
                        apply fastforce
                       apply (fastforce simp add: filter_True filter_False list_emb_Nil2 BULK_BENQ_right_empty BULK_BENQ_left_empty)
                      apply (rule refl)
                     apply (simp add: SIM1)
                subgoal
                  using SIM1(13) temp(4) apply -
                  apply (clarsimp simp add: operator_state.defs)
                  unfolding timely_input_stream_def
                  apply auto
                  done
                subgoal
                  using SIM1(13) temp(4) apply -
                  apply (clarsimp simp add: operator_state.defs)
                  unfolding timely_input_stream_def
                  apply auto
                  done
                subgoal
                  by (simp add: update_zmultiset_singleton(2))
                subgoal             
                  apply (simp flip: SIM1(3))
                  apply (rule graph_summar_nt)
                     apply (rule refl)+
                    apply (rule SIM1(2)[unfolded SIM1(1)])
                   apply (auto simp add: SIM1 comp_def)
                  done
                subgoal
                  by (simp add: SIM1)
                subgoal
                  by (simp add: SIM1)
                done
              done
            subgoal premises temp
              using SIM1(13) temp(4) apply -
              apply (clarsimp simp add: operator_state.defs)
              unfolding timely_input_stream_def
              apply (auto simp add: operator_state.defs zero_enat_def)
              done
            subgoal
              using SIM1(17) apply -
              unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
              apply clarsimp
              done
            done
          subgoal for a lxs t
            (* Drop *)

            apply (intro exI conjI relcomppI)
               apply (rule rtranclp.intros(1))
              apply (rule bisim_refl)
             defer
             apply (rule wbisim_refl)
            apply (rule wb_upto_b_base)
            unfolding R_def[simplified]
            apply (rule exI[of _ "os(0 := (os 0)\<lparr> ocaps := (\<lambda> _. remove_last t (ocaps (os 0) 1)) , inter := inter (os 0) @ [(1, t, -1)] \<rparr>)"])
            apply (rule exI[of _ "sg"])
            apply (rule exI[of _ cbufs])
            apply (rule exI[of _ "(\<lambda>x. lxs)"])
            apply (rule exI[of _ "S"])
            apply (rule exI[of _ D])
            apply (intro conjI)
                        apply (simp_all add: SIM1)
            subgoal
              unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def drop_caps_def drop_caps_singleton BTL_def BHD_def produces_def
              by (simp add: map_tl SIM1(2-) comp_def split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs fun_upd_def )
            subgoal
              unfolding inputs_at_target_def
              apply (clarsimp simp add: BULK_BENQ_def  )
              apply (rule arg_cong2[where f=set_spec_op])
               apply simp_all
              apply (rule arg_cong2[where f=cUn])
               apply simp_all
              unfolding operator_state.defs
              apply simp
              apply (subst (1 2 3 4) coll_lshift)
                apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
               apply simp
               apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
              apply simp
              done
            subgoal
              using SIM1(6,4) apply -
              unfolding ty1_check_def operator_state.defs
              apply (auto simp add: SIM1 BTL_def BHD_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
              done
            subgoal     
              using SIM1(5,7)
              apply (auto simp add: ty2_check_def operator_state.defs comp_def fun_upd_def BTL_def BHD_def  obtain_progress_def split: option.splits if_splits prod.splits)
              done
            subgoal premises temp
              using SIM1(10) apply -
              apply (rule dataplane_tracker_inv_produces_drops[where os=os and cbufs=cbufs and sg=sg and
                    nid=0 and nocaps="(\<lambda>_. remove_last t (ocaps (os 0) 1))" and ninput="input (os 0)" and noutput="(outpu (os 0))(1 := outpu (os 0) 1)" and
                    nprodu="produ (os 0)" and ninter="operator_state.inter (os 0) @ [(1, t, - 1)]" and drops ="(\<lambda> _. [t])", unfolded enum_num1_def, simplified])
              subgoal
                apply (simp add: SIM1)
                using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                apply metis
                done
                       apply fastforce
              subgoal
                using SIM1(14) by auto
                     apply fastforce
                    apply (simp add: SIM1)
              subgoal
                using SIM1(13) temp(4) apply -
                apply (clarsimp simp add: operator_state.defs)
                unfolding timely_input_stream_def
                apply auto
                done
              subgoal
                by auto
              subgoal
                by (simp add: update_zmultiset_singleton(2))
                 apply simp_all
              subgoal             
                apply (simp flip: SIM1(3))
                apply (rule graph_summar_nt)
                   apply (rule refl)+
                  apply (rule SIM1(2)[unfolded SIM1(1)])
                 apply (auto simp add: SIM1 comp_def)
                done
              subgoal
                by (simp add: SIM1)
              done
            subgoal premises temp
              using SIM1(13) temp(4) apply -
              apply (clarsimp simp add: operator_state.defs)
              unfolding timely_input_stream_def
              unfolding timely_input_stream_def
              apply (auto simp add: operator_state.defs zero_enat_def vacant_def)
              done
            subgoal
              using SIM1(17) apply -
              unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
              apply clarsimp
              done
            done
          subgoal for M lxs t
            apply (intro exI conjI relcomppI)
               apply (rule rtranclp.intros(1))
              apply (rule bisim_refl)
             defer
             apply (rule wbisim_refl)
            apply (rule wb_upto_b_base)
            unfolding R_def[simplified]
            apply (rule exI[of _ "os(0 := (os 0)\<lparr> ocaps := (\<lambda> _. ocaps (os 0) 1 @ [t]), inter := inter (os 0) @ [(1, t, 1)] \<rparr> )"])
            apply (rule exI[of _ "sg"])
            apply (rule exI[of _ cbufs])
            apply (rule exI[of _ "\<lambda> _. lxs"])
            apply (rule exI[of _ "S"])
            apply (rule exI[of _ D])
            apply (intro conjI)
                        apply (simp_all add: SIM1)
            subgoal
              unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def add_caps_singleton BTL_def BHD_def
              by (simp add: map_tl SIM1(2-) comp_def split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs fun_upd_def)

            subgoal
              unfolding inputs_at_target_def
              apply (clarsimp simp add: BULK_BENQ_def  )
              apply (rule arg_cong2[where f=set_spec_op])
               apply simp_all
              apply (rule arg_cong2[where f=cUn])
               apply simp_all
              unfolding operator_state.defs
              apply simp
              apply (subst (1 2 3 4) coll_lshift)
                apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
               apply simp
               apply (metis SIM1(13) lfilter_LCons_found lfilter_LCons_seek lfinite_code(2) timely_input_stream_expires)
              apply simp
              done
            subgoal
              using SIM1(6,4) apply -
              unfolding ty1_check_def operator_state.defs
              apply (auto simp add: SIM1 BTL_def BHD_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
              done
            subgoal     
              using SIM1(5,7)
              apply (auto simp add: ty2_check_def operator_state.defs comp_def fun_upd_def BTL_def BHD_def  obtain_progress_def split: option.splits if_splits prod.splits)
              done
            subgoal premises temp
              using SIM1(10) apply -
              apply (subgoal_tac "(\<lambda>_. ocaps (os 0) 1 @ [t]) = (ocaps (os 0))(1 := ocaps (os 0) 1 @ [t])")
              subgoal
                apply simp
                apply (rule dataplane_tracker_inv_mints[where sg=sg and os=os and cbufs=cbufs and nid=0 and p=1 and m=1 and t=t, simplified])
                subgoal
                  apply (simp add: SIM1)
                  using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                  apply metis
                  done
                  apply assumption+
                subgoal              
                  apply (rule graph_summar_nt)
                     apply (rule refl)+
                    apply (rule SIM1(2)[unfolded SIM1(1)])
                   apply (auto simp add: SIM1 comp_def)
                  done
                subgoal
                  using SIM1(13) temp(4) apply -
                  apply (clarsimp simp add: operator_state.defs)
                  unfolding timely_input_stream_def
                  apply auto
                  done
                done
              subgoal
                by auto
              done
            subgoal
              using SIM1(13) apply -
              apply (auto simp add:  operator_state.defs)
              done
            subgoal
              using SIM1(17) apply -
              unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
              apply clarsimp
              done
            done
          done
        done
      done
  qed
next
  case SIM2
  show ?case (is "wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2")
  proof -
    define R where "R = ?R"
    show ?thesis 
      apply -
      unfolding R_def[symmetric]
      subgoal premises prems2
        unfolding wsim_def 
        apply (intro allI conjI impI)
        apply (elim step_set_spec_op_elim  conjE ; 
            clarsimp del: disjCI simp only: IO.simps ; hypsubst_thin ?;
            clarsimp del: disjCI simp flip: cin.rep_eq split: event.splits llist.splits option.splits sum.splits prod.splits if_splits
            ; hypsubst_thin?)
        subgoal for nid d t
          apply (clarsimp simp flip: cin.rep_eq simp add: image_iff SIM2(9,11,12))
          subgoal
            apply (subst (asm) disj_assoc[symmetric])
            apply (erule disjE)
            subgoal
              apply (intro exI conjI)
               apply (rule wstep_trans(1))
                apply simp
                apply (rule relpowp_imp_rtranclp[
                    where n="length (outpu (os 1) 1)"]) 
                apply (rule step_set_op_steps_Out_intro[where xs="outpu (os 1) 1"])
                  apply (rule steps_Tau_dataflow_op_steps_Out_intro[where xs="outpu (os 1) 1"])
                   apply (subst dataflow_tree_to_operator_def)
                   apply simp
                   apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Inr _) (_ x)) (outpu (os 1) 1)"])
                     apply (rule refl)+
                    apply force
                   apply (rule steps_comp_op_R_Out[where xs="map Inr (outpu (os 1) 1)"])
                      apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 1) (_ x)) (outpu (os 1) 1)"])
                        apply (rule refl)+
                       apply force
                      apply (subst batch_op_def)
                      apply (subst batch_op_logic_def)
                      apply (subst notifier_op_def)
                      apply simp
                      apply (rule steps_builder_op_Write_Some[where ys=Nil and p=1])
                         apply simp
                        apply simp
                       apply (rule refl)+
                      apply (simp add: SIM2(5) operator_state.defs)
                     apply (rule refl)+
                   apply force
                  apply force
                 apply (rule refl)+
               apply (rule step_set_op_intro_Out)
                  apply (rule refl)+
                 apply (simp add: image_iff)
                 apply force
                apply simp
               apply (rule refl)+
              apply (intro relcomppI)
                apply (rule bisim_refl)
               defer
               apply (rule wbisim_refl)
              apply (rule wb_upto_b_sym)
              apply (rule wb_upto_b_base)
              unfolding R_def[simplified]
              apply (rule exI[of _ "os(1 := (os 1)\<lparr> outpu := (outpu (os 1))(1 := []) \<rparr>)"])
              apply (rule exI[of _ "sg"])
              apply (rule exI[of _ cbufs])
              apply (rule exI[of _ inps])
              apply (rule exI[of _ "cUn (Pair (1, 1) |`| cset_from_list (outpu (os 1) 1)) S"])
              apply (rule exI[of _ "cinsert ((nid, 1), d, t) D"])
              apply (intro conjI)
                          apply (simp_all add: operator_state.defs SIM2(1,2,3,4,5))
              subgoal
                using SIM2(6)
                unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def notifier_op_def
                by (simp add: operator_state.defs SIM2(1,2,3,4,5))
              subgoal
                using SIM2(7)  apply -
                apply (simp add: operator_state.defs SIM2(1,2,3,4,5))
                subgoal premises temp
                  apply (rule arg_cong2[where f=set_spec_op])
                   apply simp_all
                  apply (subst (1) cUn_commute)
                  apply (rule arg_cong2[where f=cUn])
                   apply simp_all
                  done
                done
              subgoal
                using SIM2(6)
                unfolding ty1_check_def
                by (simp add: operator_state.defs SIM2(1,2,3,4,5))
              subgoal
                using SIM2(7)
                unfolding ty2_check_def
                by (simp add: operator_state.defs SIM2(1,2,3,4,5))
              subgoal
                using SIM2(8)
                by (simp add: operator_state.defs SIM2(1,2,3,4,5))
              subgoal
                using SIM2(10) apply -
                apply (rule dataplane_tracker_inv_update_outputs_outside[where nid=1 and p=1 and os=os and xs=Nil])
                   apply assumption+
                  apply simp_all
                subgoal
                  apply (intro ext)
                  apply (clarsimp simp add:)
                  apply (metis (full_types) array_rules(2) num1_eq1)
                  done
                subgoal
                  by (simp add: operator_state.defs SIM2(1,2,3,4,5) my_summ_def)
                subgoal
                  apply (rule graph_summar_nt)
                     apply (rule refl)+
                    apply (rule SIM2(2)[unfolded SIM2(1)])
                   apply (auto simp add: SIM2 comp_def)
                  done
                done
              subgoal
                using SIM2(13)
                by (simp add: operator_state.defs SIM2(1,2,3,4,5))
              subgoal
                using SIM2(14)
                by (simp add: operator_state.defs SIM2(1,2,3,4,5))
              subgoal
                using SIM2(15)
                by (simp add: operator_state.defs SIM2(1,2,3,4,5))
              subgoal premises temp
                using SIM2(16)
                unfolding input_ocaps_inv_def by auto
              subgoal
                using SIM2(17)
                by (simp add: operator_state.defs SIM2(1,2,3,4,5))
              done
            subgoal
              using timely_input_stream_advances_frontier[OF SIM2(13), of t] apply -
              apply (clarsimp simp flip: cin.rep_eq )
              subgoal premises N_inv for n
                using N_inv(1,2,3,4) apply -
                apply (subgoal_tac "dataflow_topology (summ sg) (-+-)")
                 defer
                subgoal premises temp
                  apply (simp add: SIM2(1,2) )
                  using dataflow_topology_from_tree.dataflow_topology_axioms
                  apply (metis (lifting) ext dataflow_tree_to_graph_to_my_summ)        
                  done
                subgoal

                  subgoal
                    using SIM2(10)[unfolded dataplane_tracker_inv_def , simplified] apply -
                    apply clarsimp
                    unfolding propagation_inv_def change_deltas_inv_def
                    subgoal for caps
                      apply clarsimp
                      apply (frule change_multiplicities_preserves_inv[where xs="extract_progress 1 (subgraph.nxt sg)
         \<lparr>cons =
            consu
             (fold (\<lambda>(d, t) os. consumes os 1 t d) (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))
               (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu (os 0) 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (1, 1)) bt_state))),
            inte =
              operator_state.inter
               (fold (\<lambda>(d, t) os. consumes os 1 t d) (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))
                 (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu (os 0) 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (1, 1)) bt_state))),
            prod =
              produ
               (fold (\<lambda>(d, t) os. consumes os 1 t d) (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))
                 (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu (os 0) 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (1, 1)) bt_state)))\<rparr> @ extract_progress 0 (subgraph.nxt sg)
           \<lparr>cons = consu ip_state, inte = operator_state.inter ip_state @ map (case_event (\<lambda>a aa. undefined) (\<lambda>t. (1, t, - 1)) (\<lambda>t. (1, t, 1))) (filter (Not \<circ> is_Data) (ltaken n (es ip_state 1))),
              prod = produ ip_state @ map (case_event (\<lambda>t d. (1, t, 1)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (es ip_state 1)))\<rparr>"])
                            apply assumption+
                      subgoal premises temp3
                        unfolding extract_progress_def
                        apply (auto simp add: set_map_filter operator_state.defs produ_consumes_fold consu_consumes_fold inter_consumes_fold SIM2(4,5) split: event.splits option.splits prod.splits)
                        using temp3 apply blast+
                        done
                      subgoal premises temp2
                        apply (subst frontier_less_equal_iff2[symmetric])
                        apply (clarsimp simp add: SIM2(1,2,3,4,5) split_beta image_iff set_map_filter operator_state.defs intsum_consumes_fold inter_consumes_fold consu_consumes_fold produ_consumes_fold split: event.splits option.splits prod.splits)
                        subgoal for l t' m
                          apply (elim disjE)
                          subgoal
                            apply (drule set_extract_progressD[where os="os 1" and st="\<lparr> cons = [], inte = [], prod = [] \<rparr>"])
                             apply simp
                            apply (elim disjE)
                            subgoal
                              using SIM2(10)[unfolded dataplane_tracker_inv_def , simplified] apply -
                              apply (elim exE conjE)
                              subgoal premises temp3 for caps
                                apply (rule frontier_less_equal_le_trans[rotated])
                                 apply (rule temp3(6)[unfolded imp_front_inv_def, rule_format])
                                apply (rule temp3(10)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m)", simplified])
                                apply (simp add: SIM2(1,2,3))
                                using temp3(1) apply auto
                                done
                              done
                            subgoal
                              apply (elim conjE exE)
                              subgoal for m' p'
                                apply (clarsimp simp add: image_iff split: prod.splits event.splits)
                                subgoal
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                  apply (rule temp2(11)[unfolded chnls_imp_front_inv_def, rule_format])
                                  unfolding outputs_at_target_def BULK_BENQ_def
                                  apply auto
                                  done
                                subgoal
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                  apply (rule temp2(11)[unfolded chnls_imp_front_inv_def, rule_format])
                                  unfolding outputs_at_target_def BULK_BENQ_def
                                  apply (auto simp add: SIM2(1,2) my_summ_def antichain_from_list_singleton)
                                  done
                                subgoal for dd
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule frontier_less_equal_change_multiplicities[where A="extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress (os 0))) @ extract_progress 1 (subgraph.nxt sg) (snd (obtain_progress (os 1)))"])
                                  subgoal 
                                    using temp2 by simp
                                  subgoal
                                    apply clarsimp
                                    subgoal for l' t'' m'
                                      apply (elim disjE)
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      done
                                    done
                                  subgoal
                                    apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc 0 (Src 1)", simplified])
                                    subgoal 
                                      using temp2 by simp
                                    subgoal 
                                      apply (rule path_weight_direct_0path)
                                      subgoal
                                        by (rule dataflow_topology.axioms(1)[OF temp2(5)])
                                      subgoal
                                        apply (simp add: SIM2(1,2,3) my_summ_def)
                                        apply auto
                                        done
                                      done
                                    subgoal
                                      apply (subst temp2(8)[unfolded c_pts_inv_def, rule_format, of "Loc 0 (Src 1)"])
                                      apply (subst temp2(6)[unfolded Src_caps_inv_def, rule_format, of 0 1])
                                      apply (drule setltakenD)
                                      using SIM2(13)[unfolded timely_input_stream_def] apply -
                                      apply (elim conjE)
                                      apply (drule Data_in_Stream_le_Data_in_C)
                                       apply assumption
                                      apply (metis frontier_less_equal_trans frontier_less_equal_zcount_pos set_mset_mset zcount_to_zmset_gt_0)
                                      done
                                    done
                                  done
                                done
                              done
                            subgoal
                              apply (elim conjE exE)
                              subgoal for m' p' s
                                apply (clarsimp simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified] image_iff split: prod.splits event.splits)
                                subgoal
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                  apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc 1 (Trg 1)", simplified])
                                  subgoal 
                                    using temp2 by simp
                                  subgoal 
                                    apply (rule path_weight_direct_0path)
                                    subgoal
                                      by (rule dataflow_topology.axioms(1)[OF temp2(5)])
                                    subgoal
                                      apply (simp add: SIM2(1,2,3) my_summ_def)
                                      apply auto
                                      done
                                    done
                                  apply (rule temp2(11)[unfolded chnls_imp_front_inv_def, rule_format])
                                  unfolding outputs_at_target_def BULK_BENQ_def
                                  apply auto
                                  done
                                subgoal
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                  apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc 1 (Trg 1)", simplified])
                                  subgoal 
                                    using temp2 by simp
                                  subgoal 
                                    apply (rule path_weight_direct_0path)
                                    subgoal
                                      by (rule dataflow_topology.axioms(1)[OF temp2(5)])
                                    subgoal
                                      apply (simp add: SIM2(1,2,3) my_summ_def)
                                      apply auto
                                      done
                                    done
                                  apply (rule temp2(11)[unfolded chnls_imp_front_inv_def, rule_format])
                                  unfolding outputs_at_target_def BULK_BENQ_def
                                  apply (auto simp add: SIM2(1,2) my_summ_def antichain_from_list_singleton)
                                  done


                                subgoal for dd
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                  apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc 1 (Trg 1)", simplified])
                                  subgoal 
                                    using temp2 by simp
                                  subgoal 
                                    apply (rule path_weight_direct_0path)
                                    subgoal
                                      by (rule dataflow_topology.axioms(1)[OF temp2(5)])
                                    subgoal
                                      apply (simp add: SIM2(1,2,3) my_summ_def)
                                      apply auto
                                      done
                                    done
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule frontier_less_equal_change_multiplicities[where A="extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress (os 0))) @ extract_progress 1 (subgraph.nxt sg) (snd (obtain_progress (os 1)))"])
                                  subgoal 
                                    using temp2 by simp
                                  subgoal
                                    apply clarsimp
                                    subgoal for l' t'' m'
                                      apply (elim disjE)
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      done
                                    done
                                  subgoal
                                    apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc 0 (Src 1)", simplified])
                                    subgoal 
                                      using temp2 by simp
                                    subgoal 
                                      apply (rule path_weight_direct_0path)
                                      subgoal
                                        by (rule dataflow_topology.axioms(1)[OF temp2(5)])
                                      subgoal
                                        apply (simp add: SIM2(1,2,3) my_summ_def)
                                        apply auto
                                        done
                                      done
                                    subgoal
                                      apply (subst temp2(8)[unfolded c_pts_inv_def, rule_format, of "Loc 0 (Src 1)"])
                                      apply (subst temp2(6)[unfolded Src_caps_inv_def, rule_format, of 0 1])
                                      apply (cases dd; simp)
                                      apply (drule setltakenD)
                                      using SIM2(13)[unfolded timely_input_stream_def] apply -
                                      apply (elim conjE)
                                      apply (drule Data_in_Stream_le_Data_in_C)
                                       apply assumption
                                      apply (metis frontier_less_equal_trans frontier_less_equal_zcount_pos set_mset_mset zcount_to_zmset_gt_0)
                                      done
                                    done
                                  done
                                done
                              done
                            subgoal
                              by simp
                            done

                          subgoal
                            apply (drule set_extract_progressD[where os="os 0" and st="\<lparr> cons = [], inte = [], prod = [] \<rparr>"])
                             apply simp
                            apply (elim disjE)
                            subgoal
                              using SIM2(10)[unfolded dataplane_tracker_inv_def , simplified] apply -
                              apply (elim exE conjE)
                              subgoal premises temp3 for caps
                                apply (rule frontier_less_equal_le_trans[rotated])
                                 apply (rule temp3(6)[unfolded imp_front_inv_def, rule_format])
                                apply (rule temp3(10)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m)", simplified])
                                apply (simp add: SIM2(1,2,3))
                                using temp3(1) apply auto
                                done
                              done
                            subgoal
                              apply (elim conjE exE)
                              subgoal for m' p'
                                by (clarsimp simp add: image_iff split: prod.splits event.splits)
                              done
                            subgoal
                              apply (clarsimp simp add: image_iff split: prod.splits event.splits)
                              subgoal for x
                                apply (cases x; clarsimp)
                                subgoal
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule frontier_less_equal_change_multiplicities[where A="extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress (os 0))) @ extract_progress 1 (subgraph.nxt sg) (snd (obtain_progress (os 1)))"])
                                  subgoal 
                                    using temp2 by simp
                                  subgoal 
                                    apply clarsimp
                                    subgoal for l' t'' m'
                                      apply (elim disjE)
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      done
                                    done
                                  subgoal
                                    apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc 0 (Src 1)", simplified])
                                    subgoal 
                                      using temp2 by simp
                                    subgoal 
                                      apply (rule graph.path_weight_refl)
                                      subgoal
                                        by (rule dataflow_topology.axioms(1)[OF temp2(5)])
                                      done
                                    subgoal
                                      apply (subst temp2(8)[unfolded c_pts_inv_def, rule_format, of "Loc 0 (Src 1)"])
                                      apply (subst temp2(6)[unfolded Src_caps_inv_def, rule_format, of 0 1]) 
                                      apply (drule setltakenD)
                                      using SIM2(13)[unfolded timely_input_stream_def] apply -
                                      apply (elim conjE)
                                      apply (drule Drop_in_Stream_le_Drop_in_C)
                                       apply assumption
                                      apply (metis frontier_less_equal_trans frontier_less_equal_zcount_pos set_mset_mset zcount_to_zmset_gt_0)
                                      done
                                    done
                                  done
                                subgoal
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule frontier_less_equal_change_multiplicities[where A="extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress (os 0))) @ extract_progress 1 (subgraph.nxt sg) (snd (obtain_progress (os 1)))"])
                                  subgoal 
                                    using temp2 by simp
                                  subgoal 
                                    apply clarsimp
                                    subgoal for l' t'' m'
                                      apply (elim disjE)
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      subgoal
                                        apply hypsubst_thin
                                        apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m')", simplified])
                                        apply auto
                                        done
                                      done
                                    done
                                  subgoal
                                    apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc 0 (Src 1)", simplified])
                                    subgoal 
                                      using temp2 by simp
                                    subgoal 
                                      apply (rule graph.path_weight_refl)
                                      subgoal
                                        by (rule dataflow_topology.axioms(1)[OF temp2(5)])
                                      done
                                    subgoal
                                      apply (subst temp2(8)[unfolded c_pts_inv_def, rule_format, of "Loc 0 (Src 1)"])
                                      apply (subst temp2(6)[unfolded Src_caps_inv_def, rule_format, of 0 1]) 
                                      apply (drule setltakenD)
                                      using SIM2(13)[unfolded timely_input_stream_def] apply -
                                      apply (elim conjE)
                                      apply (drule Mint_in_Stream_le_Mint_in_C)
                                       apply assumption
                                      apply (metis frontier_less_equal_trans frontier_less_equal_zcount_pos set_mset_mset zcount_to_zmset_gt_0)
                                      done
                                    done
                                  done
                                done
                              done
                            subgoal
                              apply (clarsimp simp add: image_iff split: prod.splits event.splits)
                              subgoal for nid' x
                                apply (cases x; clarsimp)
                                unfolding my_summ_def comp_def graph_to_nxt_def
                                apply clarsimp
                                apply (drule find_SomeD')
                                apply (clarsimp split: if_splits)
                                apply hypsubst_thin
                                apply (rule frontier_less_equal_le_trans[rotated])
                                 apply (rule temp2(10)[unfolded imp_front_inv_def, rule_format])
                                apply (rule frontier_less_equal_le_trans[rotated])
                                 apply (rule frontier_less_equal_change_multiplicities[where A="extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress (os 0))) @ extract_progress 1 (subgraph.nxt sg) (snd (obtain_progress (os 1)))"])
                                subgoal 
                                  using temp2 by simp
                                subgoal 
                                  apply clarsimp
                                  subgoal for l' t'' m'
                                    apply (elim disjE)
                                    subgoal
                                      apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=0 and x="(_, _, m')", simplified])
                                      apply auto
                                      done
                                    subgoal
                                      apply (drule temp2(13)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format,  simplified, where xs=Nil and nid=1 and x="(_, _, m')", simplified])
                                      apply auto
                                      done
                                    done
                                  done
                                subgoal for dd
                                  apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc 0 (Src 1)", simplified])
                                  subgoal 
                                    using temp2 by simp
                                  subgoal 
                                    apply (rule path_weight_direct_0path)
                                    subgoal
                                      by (rule dataflow_topology.axioms(1)[OF temp2(5)])
                                    subgoal
                                      apply (simp add: SIM2(1,2,3) my_summ_def)
                                      apply auto
                                      done
                                    done
                                  subgoal
                                    apply (subst temp2(8)[unfolded c_pts_inv_def, rule_format, of "Loc 0 (Src 1)"])
                                    apply (subst temp2(6)[unfolded Src_caps_inv_def, rule_format, of 0 1])
                                    apply (drule setltakenD)
                                    using SIM2(13)[unfolded timely_input_stream_def] apply -
                                    apply clarsimp
                                    apply (drule Data_in_Stream_le_Data_in_C)
                                     apply assumption
                                    apply (metis frontier_less_equal_trans frontier_less_equal_zcount_pos set_mset_mset zcount_to_zmset_gt_0)
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                       apply (rule refl)+
                      apply (elim conjE)
                      subgoal premises N_INV
                        using N_INV (1-17) apply -
                        subgoal
                          apply (cases "propagate_all (summ sg)
     (change_multiplicities (summ sg)
       (extract_progress 1 (subgraph.nxt sg)
         \<lparr>cons =
            consu
             (fold (\<lambda>(d, t) os. consumes os 1 t d) (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))
               (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu (os 0) 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (1, 1)) bt_state))),
            inte =
              operator_state.inter
               (fold (\<lambda>(d, t) os. consumes os 1 t d) (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))
                 (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu (os 0) 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (1, 1)) bt_state))),
            prod =
              produ
               (fold (\<lambda>(d, t) os. consumes os 1 t d) (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))
                 (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu (os 0) 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (1, 1)) bt_state)))\<rparr>)
       (change_multiplicities (summ sg)
         (extract_progress 0 (subgraph.nxt sg)
           \<lparr>cons = consu ip_state,
              inte = operator_state.inter ip_state @ map (case_event (\<lambda>a aa. undefined) (\<lambda>t. (1, t, - 1)) (\<lambda>t. (1, t, 1))) (filter (Not \<circ> is_Data) (ltaken n (es ip_state 1))),
              prod = produ ip_state @ map (case_event (\<lambda>t d. (1, t, 1)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (es ip_state 1)))\<rparr>)
         (pt_tr sg)))")
                          subgoal
                            apply (rule FalseE)
                            subgoal
                              apply (drule propagate_all_terminates[unfolded not_def, rule_format, rotated 6])              
                                   apply simp_all
                              subgoal premises temp3
                                using N_INV(17-) apply -
                                by (metis (no_types, lifting) change_multiplicities_append_alt change_multiplicities_comm)
                              subgoal premises temp3
                                using N_INV(17-) apply -
                                by (metis (no_types, lifting) change_multiplicities_append_alt change_multiplicities_comm)
                              subgoal for loc
                                apply (subgoal_tac "graph_summar_nt (summ sg) (subgraph.nxt sg) os")
                                 defer
                                subgoal
                                  apply (rule graph_summar_nt)
                                     apply (rule refl)+
                                    apply (rule SIM2(2)[unfolded SIM2(1)])
                                   apply (auto simp add: SIM2 comp_def)
                                  done
                                subgoal
                                  apply (cases loc; simp)
                                  subgoal for nid lp
                                    apply (cases lp; simp)
                                    unfolding graph_summar_nt_def
                                     apply auto
                                    done
                                  done
                                done
                              subgoal premises temp3
                                using N_INV(17-) apply -
                                by (metis (no_types, lifting) change_multiplicities_append_alt change_multiplicities_comm)
                              done
                            done
                          subgoal for c
                            apply (subgoal_tac "frontier (c_imp c (Loc 1 (Trg 1))) = frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1)))))")
                             defer 
                            subgoal
                              apply (drule propagate_all_frontier_c_imp_correctness[where loc="Loc 1 (Trg 1)"])
                              subgoal 
                                by assumption
                              subgoal premises aux
                                unfolding reachable_locations_def
                                using loc_2_1_cases by (auto simp add: image_iff SIM2(1,2,3) split_beta my_summ_def split: prod.splits event.splits)
                              subgoal
                                using N_INV(17-)
                                by (metis (no_types, lifting) change_multiplicities_append_alt change_multiplicities_comm)
                              subgoal
                                using N_INV(17-)
                                by (metis (no_types, lifting) change_multiplicities_append_alt change_multiplicities_comm)
                              subgoal
                                using N_INV(17-)
                                by (metis (no_types, lifting) change_multiplicities_append_alt change_multiplicities_comm)
                              subgoal
                                apply simp
                                subgoal premises temp4
                                  apply (subst dataflow_topology.implied_frontier_alt_def[OF temp4(5)])
                                  apply (subst comm_monoid_add_class.sum.subset_diff[where B="{Loc 0 (Src 1)}"])
                                    apply simp
                                    apply fast
                                   apply simp
                                  apply (subst comm_monoid_add_class.sum.neutral)
                                  subgoal
                                    apply (intro ballI)
                                    apply simp
                                    apply (subst comm_monoid_add_class.sum.neutral)
                                     apply (intro ballI)
                                     apply (simp_all add: )
                                    apply (rule image_zmset_empty_if)
                                    apply (rule zmset_of_empty_if)
                                    apply (rule mset_set_empty_if)
                                    apply (rule set_antichain_empty_if)
                                    apply (rule frontier_empty_if)
                                    apply (simp add:  operator_state.defs SIM2(4,5) intsum_consumes_fold produ_consumes_fold consu_consumes_fold inter_consumes_fold  map_concat filter_map split_beta comp_def split: option.splits)
                                    apply (simp add: SIM2(8)[rule_format, unfolded SIM2(1)])
                                    apply (subst change_multiplicities_extract_progress_append[of _ _ _ _ _ _ _ _ Nil, simplified])
                                    apply (subst change_multiplicities_extract_progress_append[of _ _ _ _ Nil, simplified])
                                    apply (simp add: c_pts_change_multiplicities_append flip: change_multiplicities_append_alt)
                                    subgoal for l t''
                                      apply (subgoal_tac "subgraph.nxt sg (0, 1) = Some (1, 1) \<and> subgraph.nxt sg (1, 1) = None")
                                      subgoal
                                        apply (subgoal_tac "outputs_at_target (summ sg) os (1, 1) = outpu (os 0) 1")
                                        subgoal                            
                                          unfolding extract_progress_def comp_def
                                          apply (clarsimp simp add: comp_def)
                                          apply (cases l)
                                          subgoal for nid2 pp
                                            apply (cases pp; simp; hypsubst_thin)
                                            subgoal 
                                              apply (cases "nid2 = 1")
                                              subgoal
                                                apply (simp add: split_beta enum_num1_def)
                                                apply hypsubst_thin
                                                using N_INV(8)[unfolded c_pts_inv_def c_pts_change_multiplicities_append, 
                                                    simplified, rule_format, of "Loc 1 (Trg 1)", unfolded  extract_progress_def obtain_progress_def,
                                                    simplified, unfolded BULK_BENQ_def  N_INV(7)[unfolded Trg_caps_inv_def, rule_format, of 1 1]] apply -
                                                apply (simp add: filter_True filter_False list_emb_Nil2 BULK_BENQ_right_empty BULK_BENQ_left_empty c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
                                                apply (subst zmset_Data_to_zmset)
                                                subgoal
                                                  by auto
                                                subgoal 
                                                  apply (subst group_add_class.diff_add_eq_diff_diff_swap)
                                                  apply (subst (2) group_add_class.add_diff_eq)
                                                  apply (simp add: group_add_class.add_diff_eq)
                                                  apply (subst (2) add.commute)
                                                  apply (simp add: add.assoc)
                                                  apply (subst (5) add.commute)
                                                  apply (simp add: group_add_class.diff_eq_eq  flip: add.assoc)
                                                  apply (rule arg_cong[where f=to_zmset])
                                                  apply (rule map_cong)
                                                   apply (rule filter_cong)
                                                    apply simp_all
                                                  apply (auto split: event.splits)
                                                  done
                                                done
                                              subgoal
                                                apply (subgoal_tac "nid2 = 0")
                                                subgoal
                                                  apply simp
                                                  apply hypsubst_thin
                                                  apply (simp add: split_beta enum_num1_def)
                                                  apply (simp add: c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
                                                  using N_INV(8)[unfolded c_pts_inv_def c_pts_change_multiplicities_append, 
                                                      simplified, rule_format, of "Loc 0 (Trg 1)", unfolded  extract_progress_def obtain_progress_def,
                                                      simplified, unfolded BULK_BENQ_def  N_INV(7)[unfolded Trg_caps_inv_def, rule_format, of 0 1]] apply -
                                                  apply (subgoal_tac "to_zmset (map snd (outputs_at_target (summ sg) os (0, 1))) = {#}\<^sub>z")
                                                  subgoal
                                                    by (simp add:SIM2(17)[simplified] filter_True filter_False list_emb_Nil2 BULK_BENQ_right_empty BULK_BENQ_left_empty c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
                                                  subgoal
                                                    unfolding outputs_at_target_def
                                                    by (clarsimp simp add: my_summ_def SIM2(1,2,3,4,5) split: option.splits prod.splits)
                                                  done
                                                subgoal
                                                  using loc_2_1_cases by blast
                                                done
                                              done
                                            subgoal 
                                              apply (subgoal_tac "nid2 = 1")
                                              subgoal
                                                apply simp
                                                apply hypsubst_thin
                                                apply (rule FalseE)
                                                apply (subgoal_tac "Graph.graph (summ sg)")
                                                subgoal premises temp3
                                                  using temp3(1) apply -
                                                  apply (simp flip: member_antichain.rep_eq)
                                                  apply (drule path_weight_end_of_road[OF temp3(6)])
                                                    apply (auto simp add: SIM2(1,2) my_summ_def)
                                                  done
                                                subgoal
                                                  by (rule dataflow_topology.axioms(1)[OF N_INV(5)])
                                                done
                                              subgoal
                                                using loc_2_1_cases by blast
                                              done
                                            done
                                          done
                                        subgoal premises premss
                                          unfolding outputs_at_target_def
                                          by (auto simp add: SIM2(1,2) my_summ_def antichain_from_list_singleton)
                                        done
                                      subgoal premises premss
                                        by (auto simp add: is_empty_antichain_iff  enum_prod_def enum_location_def SIM2(1,2,3) graph_to_nxt_def my_summ_def antichain_from_list_singleton intro!: find_None_if find_Some_singleton)
                                      done
                                    done
                                  subgoal
                                    apply (subgoal_tac "set_antichain (graph.path_weight (summ sg) (Loc 0 (Src 1)) (Loc 1 (Trg 1))) = {0}")
                                    subgoal
                                      apply (simp add: SIM2(4,5) operator_state.defs consu_consumes_fold inter_consumes_fold produ_consumes_fold comp_def)
                                      apply (subst change_multiplicities_extract_progress_append[of _ _ _ _ Nil, simplified])
                                      apply (subst change_multiplicities_extract_progress_append[of _ _ _ _ _ _ _ _ Nil, simplified])
                                      apply (simp add: c_pts_change_multiplicities_append split_beta SIM2(4,5) operator_state.defs  comp_def consu_consumes_fold inter_consumes_fold produ_consumes_fold flip:  member_antichain.rep_eq change_multiplicities_append_alt)
                                      apply (subst (2) add.commute)
                                      apply (simp add: add.assoc)
                                      apply (subgoal_tac "c_pts (change_multiplicities (summ sg) (extract_progress 1 (subgraph.nxt sg) \<lparr>cons = consu (os 1), inte = operator_state.inter (os 1), prod = produ (os 1)\<rparr>) (pt_tr sg)) (Loc 0 (Src 1)) = c_pts (pt_tr sg) (Loc 0 (Src 1))")
                                       defer
                                      subgoal
                                        apply (subgoal_tac "subgraph.nxt sg (1, 1) = None")
                                        subgoal
                                          by (simp add: filter_True filter_False list_emb_Nil2 BULK_BENQ_right_empty BULK_BENQ_left_empty extract_progress_def c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
                                        subgoal
                                          by (simp add: SIM2(1,2,3) my_summ_def)
                                        done
                                      subgoal
                                        apply simp
                                        apply (subgoal_tac "c_pts (change_multiplicities (summ sg) (extract_progress 0 (subgraph.nxt sg) \<lparr>cons = consu (os 0), inte = operator_state.inter (os 0), prod = produ (os 0)\<rparr>) (pt_tr sg)) (Loc 0 (Src 1)) = caps (Loc 0 (Src 1))")
                                         defer
                                        subgoal
                                          using N_INV(8)[unfolded c_pts_inv_def, unfolded obtain_progress_def, simplified, rule_format, of "Loc 0 (Src 1)"]
                                          by (smt (verit, best) c_pts_change_multiplicities_cong change_multiplicities_append change_multiplicities_comm)
                                        subgoal
                                          apply (subgoal_tac "subgraph.nxt sg (0, 1) = Some (1, 1)")
                                          subgoal
                                            apply (simp add: N_INV(6)[unfolded Src_caps_inv_def, rule_format, of 0 1])
                                            apply (clarsimp simp add: filter_True filter_False list_emb_Nil2 BULK_BENQ_right_empty BULK_BENQ_left_empty frontier_zmset_of_add_minus zmset_of_plus extract_progress_def c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
                                            subgoal premises aux
                                              apply (subst zmset_map_Drop_Mint)
                                              subgoal
                                                by auto
                                              subgoal
                                                apply simp
                                                apply (subst Groups.group_add_class.add_diff_eq[symmetric])
                                                apply (rule arg_cong[where f=frontier])
                                                apply (auto simp add: filter_filter_mset)
                                                apply (metis (mono_tags, lifting) event.distinct_disc(2,4) filter_cong mset_filter)
                                                done
                                              done
                                            done
                                          subgoal
                                            by (auto simp add: is_empty_antichain_iff  enum_prod_def enum_location_def SIM2(1,2,3) graph_to_nxt_def my_summ_def antichain_from_list_singleton intro!: find_None_if find_Some_singleton)
                                          done
                                        done
                                      done
                                    subgoal
                                      apply (subst path_weight_antichain0[])
                                      subgoal
                                        by (rule dataflow_topology.axioms(1)[OF N_INV(5)])
                                       apply (auto simp add: SIM2(1,2,3) my_summ_def)
                                      done
                                    done
                                  done
                                done
                              done
                            subgoal

                              apply (intro exI conjI[rotated])
                               apply (intro relcomppI)
                                 apply (rule bisim_refl)
                                defer
                                apply (rule wbisim_refl)
                               apply (rule wstep_trans(1))
                                apply (rule relpowp_imp_rtranclp[
                                    where n="n + 
                             (length (outpu (os 0) 0)) + length (filter is_Data (ltaken n (inps 1))) + 
                             (length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n (inps 1)))) +
                             1 +
                             1 +  
                             1 +
                             1 +
                             (let batches = map (\<lambda> (d, t). (projl d, t)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1)@ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (d, t)) (filter is_Data (ltaken n (inps 1)))) in
                              let F = frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1))))) in
                              length (outpu (os 1) 1) + length (output_batches f F batches))"]) 
                                apply (simp only: relpowp_add)
                                apply (intro relcomppI)
                                          apply (rule step_n_Taus_set_op)
                                           apply (rule step_tau_pow_dataflow_op)
                                           apply (subst dataflow_tree_to_operator_def)
                                           apply simp
                                           apply (rule step_tau_pow_map_op)
                                           apply (rule step_taus_L_pow_comp_op_steps_intro)
                                            apply (rule step_tau_pow_map_op)
                                            apply (subst ooo_input_op_def)
                                            apply (rule step_builder_op_n_Silents_collapse[where n=n])
                                              apply (rule ooo_input_op_logic_collapse, assumption)
                                             apply (rule ooo_input_op_logic_iterates_n[where OS="{| ip_state |}" and os=ip_state and p=1])
                              subgoal
                                by (simp add: SIM2(4,13) operator_state.defs)
                                                 apply simp
                                                apply simp
                              subgoal
                                using SIM2(4,15) by (simp add: operator_state.defs)
                              subgoal
                                using SIM2(4) by (simp add: operator_state.defs)
                                             apply (rule refl)+

                                         apply (rule step_n_Taus_set_op)
                                          apply (rule step_tau_pow_dataflow_op)
                                          apply simp
                                          apply (rule step_tau_pow_map_op)
                                          apply (rule step_tau_Out_pow_comp_op_steps_intro[where xs="map (\<lambda> (t, d). Inr (t, d)) (outpu (os 0) 1)"])
                                             apply (rule steps_map_op)
                                               apply (rule refl)+
                                              prefer 2
                                              apply (rule steps_builder_op_Write_Some[where ys="map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n (inps 1)))" and xs="outpu (os 0) 1"])
                                                 apply (simp add: SIM2(4))
                                                apply (simp add: SIM2(4) operator_state.defs)
                                               apply (rule refl)+
                                             apply simp
                                             apply blast
                                            apply simp
                                           apply simp
                                          apply (rule refl)+


                                        apply (rule step_n_Taus_set_op)
                                         apply (rule step_tau_pow_dataflow_op)
                                         apply simp
                                         apply (rule step_tau_pow_map_op)
                                         apply (rule step_tau_Out_pow_comp_op_steps_intro[where p="Inr (0, 1)" and xs="map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n (inps 1)))"])
                                            apply (rule steps_map_op)
                                              apply (rule refl)+
                                             prefer 2
                                             apply (rule steps_builder_op_Write_Some[where p=1 and xs="map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n (inps 1)))" and ys=Nil])
                                                apply (simp add: SIM2(4))
                                               apply (simp add: SIM2(4) operator_state.defs)
                                              apply (rule refl)+
                                            apply (simp split: event.splits)
                                           apply simp
                                          apply simp
                                         apply (rule refl)+

                                       apply (rule step_n_Taus_set_op)
                                        apply (rule step_tau_pow_dataflow_op)
                                        apply simp
                                        apply (rule step_tau_pow_map_op)
                                        apply (rule step_tau_Inp_pow_comp_op_steps_intro[where n="length (cbufs (1, 1))" and p="Inr (1, 1)" and xs="map _ (cbufs (1, 1))"])
                                             apply (rule steps_map_op)
                                               apply (rule refl)+
                                              prefer 2

                                              apply (subst batch_op_def)
                                              apply (subst batch_op_logic_def)
                                              apply (subst notifier_op_def)
                                              apply simp
                                              apply (rule steps_builder_op_Read_Some[where xs="cbufs (1, 1)" and p=1])
                                               apply simp
                                              apply (rule refl)+
                                             apply fastforce
                                            apply simp
                              subgoal
                                apply (clarsimp simp add: comp_def split: prod.splits sum.splits option.splits if_splits)
                                apply (smt (verit, ccfv_threshold) case_prod_conv old.sum.simps(6) option.case(2) ranI verit_sum_simplify)
                                done
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
                                       apply (rule step_tau_Inp_pow_comp_op_steps_intro[where n="length (outpu (os 0) 1)" and p="Inr (1, 1)" and xs="map _ (outpu (os 0) 0)"])
                                            apply (rule steps_map_op)
                                              apply (rule refl)+
                                             prefer 2

                                             apply (rule steps_builder_op_Read_Some[where xs="outpu (os 0) 1" and p=1])
                                              apply simp
                                             apply (rule refl)+
                                            apply fastforce
                                           apply simp
                              subgoal
                                apply (clarsimp simp add: comp_def split: prod.splits sum.splits option.splits if_splits)
                                apply (smt (verit, ccfv_threshold) case_prod_conv old.sum.simps(6) option.case(2) ranI verit_sum_simplify)
                                done
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
                                      apply (rule step_tau_Inp_pow_comp_op_steps_intro[where n="length (filter is_Data (ltaken n (inps 1)))" and p="Inr (1, 1)" and xs="map _ (filter is_Data (ltaken n (inps 1)))"])
                                           apply (rule steps_map_op)
                                             apply (rule refl)+
                                            prefer 2
                                            apply (rule steps_builder_op_Read_Some[where xs="map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n (inps 1)))" and p=1])
                                             apply simp
                                            apply (rule refl)+
                                           apply fastforce
                                          apply simp
                              subgoal
                                apply (clarsimp simp add: comp_def split: prod.splits sum.splits option.splits if_splits)
                                apply (smt (verit, ccfv_threshold) case_prod_conv old.sum.simps(6) option.case(2) ranI verit_sum_simplify)
                                done
                              subgoal
                                unfolding BULK_BENQ_def
                                by simp
                              subgoal
                                unfolding BULK_BENQ_def
                                by (simp split: event.splits)
                                      apply (rule refl)+


                                    apply (rule step_n_Taus_set_op)
                                     apply (simp only: relpowp_1)
                                     apply (rule step_Tau_dataflow_op_Out_Inl_intro)
                                      apply (rule step_map_op)
                                       apply (rule step_comp_op_L_Out)
                                          apply (rule step_map_op)
                                           apply (rule step_builder_op_Write_None)
                                             apply (rule refl)+
                                            apply (simp add: obtain_progress_def)
                                           apply (rule refl)+
                                          apply simp
                              subgoal
                                by auto
                                        apply (rule refl)+
                                      apply simp
                                     apply (rule refl)+

                                   apply (rule step_n_Taus_set_op)
                                    apply (simp only: relpowp_1)
                                    apply (rule step_Tau_dataflow_op_Out_Inl_intro)
                                     apply (rule step_map_op)
                                      apply (rule step_comp_op_R_Out)
                                        apply (rule step_map_op)
                                         apply (rule step_builder_op_Write_None)
                                           apply (rule refl)+
                                          apply (simp add: obtain_progress_def)
                                         apply (rule refl)+
                                        apply simp
                                       apply (simp add: BULK_BENQ_def)
                                      apply (rule refl)+
                                     apply simp
                                    apply (rule refl)+



                                  apply (rule step_n_Taus_set_op)
                                   apply (simp only: relpowp_1)
                                   apply simp
                                   apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
                                      apply (rule step_map_op)
                                       apply (rule step_comp_op_R_Inp)     
                                          apply (rule step_map_op)
                                           apply (rule step_builder_op_Read_None)
                                             apply (rule refl)+
                                            apply simp
                                           apply (rule refl)+
                                          apply simp
                              subgoal premises temp
                                by (clarsimp simp add: ran_def comp_def split_beta split: prod.splits sum.splits option.splits if_splits)
                                        apply (rule refl)+
                                      apply simp
                                     apply simp
                                    apply simp
                                   apply (rule refl)+

                                 apply (rule step_n_Taus_set_op)
                                  apply (simp only: relpowp_1)
                                  apply simp
                                  apply (rule step_Tau_dataflow_op_Tau_intro)
                                  apply (rule step_map_op)
                                   apply (rule step_comp_op_R_Tau)
                                     apply (rule step_map_op)
                                      apply (rule step_builder_op_Silent)
                                         apply (rule refl)+
                                        apply simp
                                       apply (simp del: ocaps_consumes_fold)
                                       apply (intro conjI)
                              subgoal premises tempp
                                apply (rule filter_not_emptyI)
                                apply (clarsimp simp add: operator_state.defs image_iff SIM2(4,5))
                                apply (rule bexI[of _ t])
                                using tempp apply simp
                                subgoal
                                  using tempp(2) apply -
                                  apply (elim disjE conjE)
                                  subgoal 
                                    unfolding outputs_at_target_def BULK_BENQ_def inputs_at_target_def
                                    apply simp
                                    apply (auto simp add: SIM2(1,2,3) my_summ_def intsum_consumes_fold del: disjCI split: if_splits)
                                    subgoal for ddd x
                                      apply (cases x; simp)
                                      apply (intro disjI2)
                                      subgoal for t2 d2
                                        apply (rule exI[of _ x])
                                        using N_inv(5) apply (auto simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified])
                                        done
                                      done
                                    subgoal for ddd x
                                      apply (cases x; simp)
                                      apply (intro disjI2)
                                      subgoal for t2 d2
                                        apply (rule exI[of _ x])
                                        using N_inv(5) apply (auto simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified])
                                        done
                                      done
                                    done
                                  subgoal
                                    unfolding outputs_at_target_def BULK_BENQ_def inputs_at_target_def
                                    apply simp
                                    apply (auto simp add: SIM2(1,2,3) my_summ_def intsum_consumes_fold del: disjCI split: if_splits)
                                    subgoal
                                      apply (rule disjI1)
                                      apply (rule SIM2(16)[unfolded input_ocaps_inv_def, rule_format, of t 1 0 1, simplified])
                                       apply (auto simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified])
                                      done
                                    subgoal
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (auto simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified])
                                      done
                                    subgoal
                                      using SIM2(16)[unfolded input_ocaps_inv_def, rule_format, of t 1 0 1, simplified] apply -
                                      apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified] split: event.splits)
                                      apply auto
                                      done
                                    subgoal
                                      using SIM2(16)[unfolded input_ocaps_inv_def, rule_format, of t 1 0 1, simplified] apply -
                                      apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified] split: event.splits)
                                      apply auto
                                      done
                                    subgoal
                                      using SIM2(16)[unfolded input_ocaps_inv_def, rule_format, of t 1 0 1, simplified] apply -
                                      apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified] split: event.splits)
                                      apply auto
                                      done
                                    done
                                  done
                                done
                                       apply (rule refl)+
                                     apply simp
                                    apply (rule refl)+
                                  apply simp
                                 apply (rule refl)+

                                apply (rule step_set_op_steps_Out_intro[where 
                                    xs="let batches = map (\<lambda> (d, t). (projl d, t)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1)@ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (d, t)) (filter is_Data (ltaken n (inps 1)))) in
                          let F = frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1))))) in
                          (outpu (os 1) 1) @ map (\<lambda> (d, t). (Inr d, t)) (output_batches f F batches)" and p="(1,1)"])
                                  apply (rule steps_Tau_dataflow_op_steps_Out_intro[where xs="let batches = map (\<lambda> (d, t). (projl d, t)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1)@ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (d, t)) (filter is_Data (ltaken n (inps 1)))) in
                          let F = frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1))))) in
                          (outpu (os 1) 1) @ map (\<lambda> (d, t). (Inr d, t)) (output_batches f F batches)" and nid = 1 and p=1])
                                   apply (rule steps_map_op)
                                     apply (rule refl)+
                                    apply simp
                                    prefer 2
                                    apply (rule steps_comp_op_R_Out[where xs="let batches = map (\<lambda> (d, t). (projl d, t)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1)@ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (d, t)) (filter is_Data (ltaken n (inps 1)))) in
                          let F = frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1))))) in
                          map Inr (outpu (os 1) 1) @ map (\<lambda> (d, t). Inr (Inr d, t)) (output_batches f F batches)" and p="Inr (1, 1)" ])
                                       apply (rule steps_map_op[where xs="
                       let batches = map (\<lambda> (d, t). (projl d, t)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1)@ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (d, t)) (filter is_Data (ltaken n (inps 1)))) in
                          let F = frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1))))) in
                          map (\<lambda> x. Out (Some 1) (Inr x)) (outpu (os 1) 1) @ map (\<lambda> (d, t). Out (Some 1) (Inr (Inr d, t))) (output_batches f F batches)"])
                                         apply (rule refl)+
                              subgoal premises temp
                                by (auto simp add: comp_def)

                                       apply (rule steps_builder_op_Write_Some[where ys=Nil])
                                          apply simp
                                         apply (simp del: ocaps_consumes_fold)
                                        apply (rule refl)+
                                       apply simp
                              subgoal premises temp
                                supply filter_True[simp] filter_False[simp] list_emb_Nil2[simp] BULK_BENQ_right_empty[simp] BULK_BENQ_left_empty[simp]
                                apply (clarsimp simp del: filter_append map_append simp add: SIM2(9) SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff input_fold_consumes intsum_consumes_fold  SIM2(5) operator_state.defs split_beta comp_def simp flip: filter_filter map_concat split: )
                                apply (subst (2) filter_filter_True1_pair)
                                subgoal
                                  using SIM2(16)[unfolded input_ocaps_inv_def] apply -
                                  apply (auto del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] split: event.splits)
                                  subgoal
                                    by blast
                                  subgoal
                                    by blast
                                  subgoal
                                    by blast
                                  done
                                subgoal
                                  apply (subst filter_filter_pair_alt)
                                  apply (subst filter_filter_True1_pair)
                                  subgoal
                                    using SIM2(16)[unfolded input_ocaps_inv_def] apply -
                                    apply (auto del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] split: event.splits)
                                    subgoal
                                      by blast
                                    subgoal
                                      by blast
                                    subgoal
                                      by blast
                                    done
                                  subgoal
                                    apply (subst map_map[unfolded comp_def, symmetric, of "(\<lambda>(d, t). Out (Some 1) (Inr (Inr d, t)))" "(\<lambda> (d, t). (d, capability.time t))", unfolded snd_conv fst_conv split_beta])
                                    apply (subst map_concat)
                                    apply (rule map_cong)
                                    subgoal
                                      unfolding output_batches_def Let_def outputs_ts_def
                                      apply (rule arg_cong[where f=concat])
                                      apply (clarsimp simp del: filter_append map_append simp add: SIM2(9) SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff input_fold_consumes intsum_consumes_fold  SIM2(5) operator_state.defs split_beta comp_def simp flip: filter_filter map_concat split: )
                                      apply (rule map_cong)
                                      subgoal
                                        apply (rule arg_cong[where f="remdups"])
                                        apply (subst filter_snd_alt)
                                        apply (simp only: flip: filter_map)
                                        apply (rule filter_cong)
                                        subgoal
                                          by (simp add: split_beta split: event.splits)
                                        subgoal
                                          by simp
                                        done
                                      subgoal for t
                                        apply (rule map_cong)
                                        subgoal
                                          apply (subst (3) filter_True)
                                          subgoal
                                            by auto
                                          subgoal
                                            apply (rule arg_cong[where f="f"])
                                            apply (subst projl_fst)
                                            apply (subst map_map[symmetric])
                                            apply (rule map_cong)
                                            subgoal premises temp2
                                              apply (simp only:  flip: filter_append map_append append_assoc)
                                              apply (simp only: append_assoc flip: filter_append map_append )
                                              apply (subst map_fst_filter_snd)
                                              apply (rule filter_cong)
                                               apply (auto split: event.splits)
                                              done
                                            subgoal
                                              by simp
                                            done
                                          done
                                        subgoal
                                          by simp
                                        done
                                      done
                                    subgoal premises temp2
                                      by (clarsimp split: prod.splits)
                                    done
                                  done
                                done
                                      apply (rule refl)+
                              subgoal premises temp
                                by (simp add: comp_def split_beta)
                              subgoal premises temp
                                by (simp add: comp_def split_beta)
                              subgoal premises temp
                                by (simp add: comp_def split_beta)
                                apply (rule refl)+
                               apply (rule step_set_op_intro_Out)
                                  apply (rule refl)+
                              subgoal premises tempp
                                using N_INV(2) apply -
                                apply (elim conjE disjE cBexE bexE)
                                subgoal for x dd
                                  apply (rule cUnI1)
                                  unfolding Let_def
                                  apply (simp add: split_beta image_iff)
                                  apply (subgoal_tac "((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 1) = input (os 1) 1 @ cbufs (1, 1) @ (outpu (os 0) 1)")
                                  subgoal
                                    apply (elim conjE exE)
                                    subgoal for aa
                                      apply (cases aa; simp)
                                      subgoal for t'' d''
                                        apply (rule disjI2)
                                        apply (intro bexI[of _ "(dd, t'')"] conjI)
                                          apply simp
                                         apply simp
                                        apply (rule output_batchesI)
                                        subgoal 
                                          apply (clarsimp simp add: image_iff split_beta split: prod.splits)
                                          apply (rule bexI[of _ "(d'', t'')"])
                                           apply simp_all
                                          apply (clarsimp del: disjCI simp add: image_iff split_beta split: event.splits prod.splits)
                                          apply (intro disjI2)
                                          apply (rule exI[of _ "Data t'' d''"])
                                          apply simp
                                          using N_inv(5) apply auto
                                          done
                                        subgoal 
                                          using N_INV(4) by auto
                                        subgoal
                                          apply simp
                                          using N_inv(6) apply -
                                          apply hypsubst_thin
                                          apply simp
                                          apply (subst (asm) coll_lshift)
                                           apply simp_all
                                          subgoal
                                            by (metis SIM2(13) timely_input_stream_Data_expires)
                                          subgoal
                                            apply (simp add: filter_map comp_def split_beta)
                                            apply (metis (lifting) cond_case_prod_eta sndI)
                                            done
                                          done
                                        done
                                      done
                                    done
                                  subgoal premises temp2
                                    unfolding BULK_BENQ_def outputs_at_target_def SIM2(2,1) 
                                    apply (clarsimp simp add: antichain_from_list_singleton my_summ_def)
                                    unfolding inputs_at_target_def
                                    apply simp
                                    done
                                  done
                                subgoal for x dd
                                  apply (rule cUnI1)
                                  unfolding Let_def
                                  apply (simp add: split_beta image_iff)
                                  apply (subgoal_tac "((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 1) = input (os 1) 1 @ cbufs (1, 1) @ (outpu (os 0) 1)")
                                  subgoal
                                    apply simp
                                    apply (rule disjI2)
                                    apply (intro bexI[of _ "(_, _)"] conjI)
                                      apply simp
                                     apply simp
                                    apply (rule output_batchesI)
                                    subgoal 
                                      apply (clarsimp simp add: image_iff split_beta split: prod.splits)
                                      apply (rule bexI[of _ "(_, t)"])
                                       apply simp_all
                                      apply (clarsimp del: disjCI simp add: image_iff split_beta split: event.splits prod.splits)
                                      apply force
                                      done
                                    subgoal 
                                      using N_INV(4) by auto
                                    subgoal
                                      apply (clarsimp simp add: image_iff split_beta split: prod.splits)
                                      apply (subst (asm) coll_lshift)
                                       apply (simp_all add: comp_def)
                                      using SIM2(13) timely_input_stream_expires apply blast
                                      apply (clarsimp simp add: filter_map split_beta comp_def )
                                      apply (subgoal_tac "map (\<lambda>x. fst (case x of Data t d \<Rightarrow> (d, t))) (filter (\<lambda>x. is_Data x \<and> snd (case x of Data t d \<Rightarrow> (d, t)) = t) (ltaken n (inps 1))) = coll (inps 1) t")
                                       defer
                                      subgoal premises auxx
                                        apply (subst N_inv(6)[symmetric])
                                        apply (simp add: filter_map comp_def split_beta)
                                        done
                                      subgoal
                                        by (simp add: split_def)
                                      done
                                    done
                                  subgoal premises temp2
                                    unfolding BULK_BENQ_def outputs_at_target_def SIM2(2,1) 
                                    apply (clarsimp simp add: antichain_from_list_singleton my_summ_def)
                                    unfolding inputs_at_target_def
                                    apply simp
                                    done
                                  done
                                done
                                apply (simp flip: cin.rep_eq)
                               apply (rule refl)+
                              subgoal premises temp2
                                apply (rule wb_upto_b_sym)
                                apply (rule wb_upto_b_base)
                                unfolding R_def[simplified]
                                apply (rule exI[of _ 
                                      "os(0 := (os 0)\<lparr> ocaps := (ocaps ip_state)(1 := ocaps_updates (ocaps ip_state 1) (ltaken n (es ip_state 1))), outpu := (outpu ip_state)(1 := []), consu := [], inter := [], produ := [] \<rparr>,
                                          1 := (os 1)\<lparr> ocaps := _, input := _, outpu := (outpu (os 1))(1 := []), consu := [], inter := _, produ := _, front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))), initia := True \<rparr>)"])
                                apply (rule exI[of _ "sg\<lparr>pt_tr := c\<rparr>"])
                                apply (rule exI[of _ "cbufs( (1, 1) := [] )"])
                                apply (rule exI[of _ "inps( 1:= ldropn n (inps 1)) "])
                                apply (rule exI[of _ "cUn (Pair (1, 1) |`|
         cUn (cset_from_list (outpu (os 1) 1))
          ((\<lambda>(d, y). (Inr d, y)) |`|
           cset_from_list
            (output_batches f (frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1))))))
              (map (\<lambda>(d, y). (projl d, y)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1) @ map (case_event (\<lambda>t d. (d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1)))))))
     S"])
                                apply (rule exI[of _ "cinsert ((nid, 1), d, t) D"])
                                apply (intro conjI)
                                            apply (simp add: SIM2(1,2,3,4,5)  operator_state.defs flip: filter_append map_append)
                                            apply (simp add: operator_state.defs  drop_caps_def intsum_consumes_fold produ_consumes_fold consu_consumes_fold inter_consumes_fold input_fold_consumes flip: filter_append map_append)
                                            apply (rule arg_cong3[where f=set_op])
                                subgoal
                                  by simp
                                subgoal
                                  by simp
                                            apply (subst dataflow_tree_to_operator_def)
                                            apply simp
                                            apply (rule arg_cong2[where f=dataflow_op])
                                             apply simp
                                            apply (rule arg_cong3[where f=map_op])
                                              apply simp
                                             apply simp
                                            apply (rule arg_cong4[where f=comp_op])
                                               apply simp
                                              apply (intro ext)
                                              apply (auto split: sum.splits)[1]
                                             apply (rule arg_cong3[where f=map_op])
                                               apply simp
                                              apply simp
                                             apply (subst ooo_input_op_def)
                                             apply (rule arg_cong5[where f=builder_op])
                                                 apply simp
                                                apply simp
                                               apply simp
                                              apply auto[1]
                                             apply simp
                                            apply (rule arg_cong3[where f=map_op])
                                              apply simp
                                             apply simp
                                            apply simp
                                            apply (subst batch_op_def)
                                            apply (subst batch_op_logic_def)
                                            apply (subst notifier_op_def)
                                            apply simp
                                            apply (rule arg_cong5[where f=builder_op])
                                                apply simp
                                               apply simp
                                              apply simp
                                             apply (simp add: fold_consumes SIM2(1,2,3,4,5)  operator_state.defs flip: filter_append map_append)
                                             apply (rule operator_state_eqI)
                                subgoal
                                  unfolding produces_def
                                  by (simp only: operator_state.simps)
                                subgoal
                                  unfolding produces_def
                                  by (simp only: operator_state.simps)
                                                    apply (subst produces_def)
                                                    apply (simp only: operator_state.simps)
                                                   apply (subst produces_def)
                                                   apply (simp only: operator_state.simps)
                                                  apply (subst produces_def)
                                                  apply (simp only: operator_state.simps)
                                subgoal
                                  unfolding produces_def
                                  apply (simp only: operator_state.simps)
                                  apply (intro ext)
                                  apply simp
                                  done
                                subgoal
                                  unfolding produces_def
                                  by (simp only: operator_state.simps)
                                               apply (subst produces_def)
                                               apply (simp only: operator_state.simps)
                                subgoal
                                  unfolding produces_def
                                  by (simp only: operator_state.simps)
                                subgoal
                                  unfolding produces_def
                                  by (simp only: operator_state.simps)
                                subgoal
                                  apply (intro ext)
                                  unfolding drop_caps_def
                                  apply simp
                                  done
                                subgoal
                                  apply (rule arg_cong2[where f=set_spec_op])
                                  subgoal
                                    apply (subgoal_tac "\<And> (os :: (2 \<Rightarrow> (1, 'd1 + 'd2, 't) operator_state)). outputs_at_target (summ sg) os (1, 1) = outpu (os 0) 1")
                                    subgoal premises aux
                                      unfolding BULK_BENQ_def inputs_at_target_def
                                      apply (simp add: aux  del: image_eqI flip: list_diff_append map_append filter_append)
                                      subgoal
                                        apply (subst (3) cUn_assoc[symmetric])
                                        apply (subst (7) cUn_commute)
                                        apply (simp only: cUn_assoc)
                                        apply (rule arg_cong2[where f=cUn])
                                         apply simp
                                        apply (simp only: cUn_assoc cimage_cUn)
                                        apply (rule arg_cong2[where f=cUn])
                                         apply simp
                                        apply (simp only:  flip: cimage_cUn)
                                        apply (subst (3) coll_lshift)
                                        subgoal for t'
                                          using timely_input_stream_expires[OF timely_input_stream_ldrop[OF N_INV(3) SIM2(13)]] by blast 
                                        subgoal
                                          apply (simp add:  comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                          apply (subst cset_eq_iff)
                                          apply (intro allI iffI)
                                          subgoal for x
                                            apply (cases x)
                                            subgoal for p d t'
                                              apply (simp only:; hypsubst_thin)
                                              apply (cases "frontier_less_equal (frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1)))))) t'")
                                              subgoal
                                                apply (rule cUnI2)
                                                apply (simp only: cUn_iff cUN_iff cimage_iff)
                                                apply (elim disjE cBexE)
                                                subgoal for t'' aa
                                                  apply (subst (asm) coll_lshift)
                                                  subgoal 
                                                    using SIM2(13) timely_input_stream_expires by blast
                                                  subgoal
                                                    apply (cases "t' |\<in>| ts (ldropn n (inps 1))")
                                                    subgoal
                                                      apply (rule disjI1)
                                                      apply (rule cBexI[rotated])
                                                       apply assumption
                                                      apply (rule cBexI)
                                                       apply fast
                                                      apply (subst filter_filter_commute_pair)
                                                      apply (subst filter_True)
                                                      subgoal
                                                        apply (intro ballI impI conjI)
                                                        apply (auto simp add: split_beta)
                                                        done
                                                      subgoal
                                                        apply simp
                                                        apply (subst map_filter_is_Data_Inl_ltaken_ldropn_coll[OF SIM2(13) N_INV(3)])
                                                        apply (simp add: comp_def)
                                                        done
                                                      done
                                                    subgoal
                                                      apply (rule disjI2)
                                                      apply (rule cBexI[rotated, of t''])
                                                       apply (clarsimp del: disjCI simp add: image_iff split: event.splits; hypsubst_thin)
                                                      subgoal for x
                                                        apply (cases x; simp)
                                                        subgoal for t'' dd
                                                          apply (rule bexI[of _ "(Inl dd, t'')"])
                                                           apply simp_all
                                                          apply (intro disjI2)
                                                          apply (simp add: image_iff)
                                                          apply (rule exI[of _ "Data t'' dd"])
                                                          apply simp
                                                          using in_lset_ltaken_ldropn apply force
                                                          done
                                                        done
                                                      subgoal
                                                        apply (simp add:  comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                                        apply (subst coll_lshift)
                                                        subgoal
                                                          using timely_input_stream_expires[OF timely_input_stream_ldrop[OF N_INV(3) SIM2(13)]] by blast
                                                        subgoal
                                                          apply (simp add:  comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                                          apply (subst filter_filter_commute_pair)
                                                          apply (subst filter_True)
                                                          subgoal
                                                            apply (intro ballI impI conjI)
                                                            apply (auto simp add: split_beta)
                                                            done
                                                          subgoal
                                                            apply simp
                                                            apply (subst map_filter_is_Data_Inl_ltaken_ldropn_coll[OF SIM2(13) N_INV(3)])
                                                            apply (simp add: comp_def)
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                  done
                                                subgoal for t'' x
                                                  apply (simp add:  comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                                  apply (rule disjI2)
                                                  apply (rule cBexI[of _ t''])
                                                  subgoal
                                                    apply (simp add:  comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                                    apply (subst coll_lshift)
                                                    subgoal
                                                      using timely_input_stream_expires[OF timely_input_stream_ldrop[OF N_INV(3) SIM2(13)]] by blast
                                                    apply (subst (asm) coll_lshift)
                                                    subgoal 
                                                      using SIM2(13) timely_input_stream_expires by blast
                                                    subgoal
                                                      apply (simp add:  comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                                      apply (subst filter_filter_commute_pair)
                                                      apply (subst filter_True)
                                                      subgoal
                                                        apply (intro ballI impI conjI)
                                                        apply (auto simp add: split_beta)
                                                        done
                                                      subgoal
                                                        apply simp
                                                        apply (subst map_filter_is_Data_Inl_ltaken_ldropn_coll[OF SIM2(13) N_INV(3)])
                                                        apply (clarsimp simp add: comp_def)
                                                        done
                                                      done
                                                    done
                                                  subgoal
                                                    apply (simp add:  comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                                    apply auto
                                                    done
                                                  done
                                                done
                                              subgoal
                                                apply (rule cUnI1)
                                                apply (simp only: cUn_iff cUN_iff cimage_iff)
                                                apply (elim disjE cBexE)
                                                subgoal for t'' dd
                                                  apply (rule cBexI[of _ "(Inr dd, t')"])
                                                   apply simp
                                                  apply (simp add: image_iff comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                                  apply (rule bexI[of _ "(dd, t')"])
                                                   apply simp
                                                  apply (clarsimp simp add: image_iff comp_def split_beta  del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                  subgoal for x
                                                    apply (cases x; simp)
                                                    apply (clarsimp simp add: image_iff comp_def split_beta  del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                    apply (rule output_batchesI)
                                                      apply (simp_all add: split_beta image_iff)
                                                    subgoal for ddd
                                                      apply hypsubst_thin
                                                      apply (rule bexI[of _ "(ddd, t')"])
                                                       apply (simp_all add: split_beta image_iff)
                                                      apply (intro disjI2)
                                                      apply (rule exI[of _ "Data t' ddd"])
                                                      apply simp
                                                      apply (subgoal_tac "Data t' ddd \<notin> lset (ldropn n (inps 1))")
                                                      subgoal
                                                        by (meson in_lset_ltaken_ldropn)
                                                      subgoal
                                                        apply (drule not_frontier_less_equal_vacant)
                                                        apply (rule timely_input_stream_vacant_Data_not_in[rotated])
                                                         apply assumption
                                                        using timely_input_stream_ldrop[OF N_INV(3) SIM2(13)] apply simp
                                                        done
                                                      done
                                                    subgoal for ddd
                                                      apply (subst (asm) coll_lshift)
                                                      subgoal 
                                                        using SIM2(13) timely_input_stream_expires by blast
                                                      subgoal
                                                        apply simp
                                                        apply (clarsimp simp add: comp_def)
                                                        apply (drule not_frontier_less_equal_vacant)
                                                        apply (drule timely_input_stream_vacant_coll[rotated 2])
                                                        using SIM2(13) apply simp
                                                        using N_INV(3) apply simp
                                                        apply (simp add: filter_map split_beta comp_def cong: filter_cong)
                                                        done
                                                      done
                                                    done
                                                  done
                                                subgoal for t'' dd
                                                  apply (rule cBexI[of _ "(Inr dd, t')"])
                                                   apply simp
                                                  apply (simp add: image_iff comp_def split_beta  del: image_eqI flip: filter_filter list_diff_append map_append filter_append)
                                                  apply (rule bexI[of _ "(dd, t')"])
                                                   apply simp
                                                  apply (clarsimp simp add: image_iff comp_def split_beta  del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                  apply (rule output_batchesI)
                                                    apply (simp_all add: split_beta image_iff)
                                                  subgoal for ddd
                                                    apply hypsubst_thin
                                                    apply (cases ddd; simp)
                                                    subgoal for d'
                                                      apply (rule bexI[of _ "(d', t'')"])
                                                       apply (simp_all add: split_beta image_iff)
                                                      apply (metis fst_conv snd_conv sum.sel(1))
                                                      done
                                                    subgoal
                                                      by force
                                                    done
                                                  subgoal for ddd
                                                    apply (subst (asm) coll_lshift)
                                                    subgoal 
                                                      using SIM2(13) timely_input_stream_expires by blast
                                                    subgoal
                                                      apply simp
                                                      apply (clarsimp simp add: comp_def)
                                                      apply (drule not_frontier_less_equal_vacant)
                                                      apply (drule timely_input_stream_vacant_coll[rotated 2])
                                                      using SIM2(13) apply simp
                                                      using N_INV(3) apply simp
                                                      apply (simp add: filter_map split_beta comp_def cong: filter_cong)
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                          subgoal for x
                                            apply (cases x)
                                            subgoal for p d t'
                                              apply (simp only:; hypsubst_thin)
                                              apply (simp only: outputs_ts_def cset_from_list_concat output_batches_def Let_def cUn_iff cUN_iff cimage_iff)
                                              apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                              apply (elim conjE bexE disjE cBexE)
                                              subgoal for pp dd
                                                apply (cases pp)
                                                apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                apply (elim conjE bexE disjE cBexE)
                                                subgoal for a b
                                                  apply (cases b)
                                                  apply (simp only:; hypsubst_thin)
                                                  apply (rule disjI2)
                                                  subgoal for A t'''
                                                    apply (rule cBexI[of _ "(A, t''')"])
                                                     apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                    subgoal
                                                      apply (subst coll_lshift)
                                                      subgoal 
                                                        using SIM2(13) timely_input_stream_expires by blast
                                                      subgoal
                                                        apply simp
                                                        apply (drule not_frontier_less_equal_vacant)
                                                        apply (subst (asm) timely_input_stream_vacant_coll[rotated 2])
                                                           apply assumption
                                                        using SIM2(13) apply simp
                                                        using N_INV(3) apply simp
                                                        apply (simp add: filter_map split_beta comp_def cong: filter_cong)
                                                        done
                                                      done
                                                    subgoal
                                                      by simp
                                                    done
                                                  done
                                                subgoal for ddd
                                                  apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append split: event.splits)
                                                  subgoal for e
                                                    apply (cases e; simp)
                                                    apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append split: event.splits)
                                                    apply hypsubst_thin
                                                    apply (rule disjI1)
                                                    apply (rule cBexI[of _ t', rotated])
                                                     defer
                                                    subgoal
                                                      apply simp
                                                      apply (subst coll_lshift)
                                                      subgoal 
                                                        using SIM2(13) timely_input_stream_expires by blast
                                                      apply (simp add: comp_def)
                                                      apply (drule not_frontier_less_equal_vacant)
                                                      apply (subst (asm) timely_input_stream_vacant_coll[rotated 2])
                                                         apply assumption
                                                      using SIM2(13) apply simp
                                                      using N_INV(3) apply simp
                                                      apply (simp add: filter_map split_beta comp_def cong: filter_cong)
                                                      done
                                                    subgoal
                                                      unfolding ts_def
                                                      apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append split: event.splits)
                                                      apply (rule exI[of _ "Data t' ddd"])
                                                      apply (simp add: cset_of_llist.rep_eq)
                                                      apply (meson setltakenD)
                                                      done
                                                    done
                                                  done
                                                done
                                              subgoal for t'' ddd
                                                apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append split: event.splits)
                                                apply hypsubst_thin
                                                subgoal for e
                                                  apply (cases e; simp del: filter_filter list_diff_append map_append filter_append)
                                                  subgoal for tt dddd
                                                    apply (cases "frontier_less_equal (frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1)))))) tt")
                                                    subgoal
                                                      apply (subst (asm) filter_filter_commute_pair)
                                                      apply (subst (asm) filter_True)
                                                      subgoal
                                                        apply (intro ballI impI conjI)
                                                        apply (auto simp add: split_beta)
                                                        done
                                                      subgoal
                                                        apply (rule disjI1)
                                                        apply (rule cBexI[of _ ])
                                                         apply simp
                                                         apply (subst (asm) map_filter_is_Data_Inl_ltaken_ldropn_coll[OF SIM2(13) N_INV(3)])
                                                         apply (subst coll_lshift)
                                                        subgoal 
                                                          using SIM2(13) timely_input_stream_expires by blast
                                                         apply (simp add: comp_def)
                                                        apply simp
                                                        apply (metis (no_types, lifting) event.disc(1) event.sel(1) imageI in_lset_ltaken_ldropn mem_Collect_eq)
                                                        done
                                                      done
                                                    subgoal premises auxx
                                                      using auxx(2-) apply -
                                                      apply (rule FalseE)
                                                      apply (drule not_frontier_less_equal_vacant)
                                                      using timely_input_stream_ldrop[OF N_INV(3) SIM2(13)] apply -
                                                      apply (meson timely_input_stream_vacant_Data_not_in)
                                                      done
                                                    done
                                                  done
                                                done
                                              subgoal for t'' ddd
                                                apply hypsubst_thin
                                                apply (subst (asm) coll_lshift)
                                                subgoal 
                                                  using timely_input_stream_expires[OF timely_input_stream_ldrop[OF N_INV(3) SIM2(13)]] by blast
                                                apply (subst (1 2) coll_lshift)
                                                subgoal 
                                                  using SIM2(13) timely_input_stream_expires by blast
                                                subgoal 
                                                  using SIM2(13) timely_input_stream_expires by blast
                                                apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                apply (subst (asm) filter_filter_commute_pair)
                                                apply (subst (asm) filter_True)
                                                subgoal
                                                  apply (intro ballI impI conjI)
                                                  apply (auto simp add: split_beta)
                                                  done
                                                subgoal for d
                                                  apply (elim disjE)
                                                  subgoal
                                                    apply (rule disjI2)
                                                    apply (rule cBexI[of _ "(d, t'')"])
                                                    subgoal
                                                      apply simp
                                                      apply (subst (asm) map_filter_is_Data_Inl_ltaken_ldropn_coll[OF SIM2(13) N_INV(3)])
                                                      apply simp
                                                      done
                                                    subgoal
                                                      by simp
                                                    done
                                                  subgoal
                                                    apply (rule disjI2)
                                                    apply (rule cBexI[of _ "(d, t'')"])
                                                    subgoal
                                                      apply simp
                                                      apply (subst (asm) map_filter_is_Data_Inl_ltaken_ldropn_coll[OF SIM2(13) N_INV(3)])
                                                      apply simp
                                                      done
                                                    subgoal
                                                      by simp
                                                    done
                                                  subgoal
                                                    apply (rule disjI2)
                                                    apply (rule cBexI[of _ "(d, t'')"])
                                                    subgoal
                                                      apply simp
                                                      apply (subst (asm) map_filter_is_Data_Inl_ltaken_ldropn_coll[OF SIM2(13) N_INV(3)])
                                                      apply simp
                                                      done
                                                    subgoal
                                                      by simp
                                                    done
                                                  subgoal
                                                    apply (rule disjI1)
                                                    apply clarsimp
                                                    subgoal for e
                                                      apply (cases e; simp)
                                                      subgoal for d'
                                                        apply (rule cBexI[of _ t''])
                                                        subgoal
                                                          apply simp
                                                          apply (subst (asm) map_filter_is_Data_Inl_ltaken_ldropn_coll[OF SIM2(13) N_INV(3)])
                                                          apply simp
                                                          done
                                                        subgoal
                                                          apply simp
                                                          apply (metis (no_types, lifting) event.disc(1) event.sel(1) imageI in_lset_ltaken_ldropn mem_Collect_eq)
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
                                      done
                                    subgoal
                                      by (simp add: SIM2(1,2))
                                    done
                                  subgoal
                                    by (simp add: SIM2(1,2,3))
                                  done
                                subgoal
                                  subgoal
                                    by (simp add: SIM2(1,2))
                                  done
                                subgoal
                                  by (simp add: SIM2(1,2,3))
                                subgoal
                                  using SIM2(6)
                                  unfolding ty1_check_def
                                  by (clarsimp simp add: operator_state.defs SIM2(4,5))
                                subgoal premises
                                  using SIM2(7) apply -
                                  unfolding ty2_check_def
                                  apply (simp only: fun_upd_def fst_conv snd_conv operator_state_ty2.simps operator_state_ty.simps operator_state.simps split_beta operator_state.defs SIM2(4,5) split: if_splits)
                                  apply safe
                                  subgoal
                                    by (simp del: list.simps append.simps filter.simps concat.simps filter_filter)
                                  subgoal
                                    by (simp del: list.simps append.simps filter.simps concat.simps filter_filter)
                                  subgoal
                                    by (simp del: list.simps append.simps filter.simps concat.simps filter_filter)
                                  subgoal for p x a b
                                    apply (clarsimp simp del: list.simps append.simps filter.simps concat.simps filter_filter split: event.splits sum.splits)
                                    subgoal
                                      by (auto split: event.splits sum.splits)
                                    subgoal
                                      by (auto split: event.splits sum.splits)
                                    subgoal premises auxx
                                      using auxx(2,3,4) SIM2(6)
                                      unfolding ty1_check_def
                                      by (auto simp add: operator_state.defs SIM2(4,5) simp del: mset_filter to_zmset_correct mset.simps update_zmultiset_simps_more split: event.splits sum.splits)
                                    done
                                  subgoal
                                    by (auto split: event.splits sum.splits)
                                  subgoal
                                    apply (clarsimp simp del: list.simps append.simps filter.simps concat.simps filter_filter split: event.splits sum.splits)
                                    subgoal
                                      by (auto split: event.splits sum.splits)
                                    done
                                  done
                                subgoal
                                  apply (intro allI impI conjI)
                                  subgoal premises auxx for P
                                    apply (intro ext)
                                    apply (auto simp only: fun_upd_def fst_conv snd_conv operator_state_ty2.simps operator_state_ty.simps operator_state.simps operator_state.defs SIM2(1,2,4,5) split: if_splits)
                                    subgoal
                                      apply (rule FalseE)
                                      apply auto
                                      done
                                    subgoal
                                      by (simp add: SIM2(8)[rule_format, of 0] SIM2(1))
                                    subgoal
                                      by (simp add: SIM2(8)[rule_format, of 1] SIM2(1))
                                    subgoal
                                      using not_01 by auto
                                    done
                                  done
                                subgoal
                                  apply (rule dataplane_tracker_inv_replace_ocaps[where  nid=0 and p=1 and C="list_diff (ocaps (os 0) 1 @ map event.time (filter is_Mint (ltaken n (inps 1)))) (map event.time (filter is_Drop (ltaken n (inps 1))))", simplified]; (rule refl)?)
                                   apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)

                                   apply (rule dataplane_tracker_inv_update_outputs_outside[where nid=1 and xs=Nil]; (rule refl)?)
                                      apply (rule dataplane_tracker_inv_produces_drops[rotated 12, where nid=1 and oputs="\<lambda> _.
(let batches = map (\<lambda> (d, t). (projl d, t)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1) @ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (d, t)) (filter is_Data (ltaken n (inps 1)))) in
                              let F = frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1))))) in
                              map (\<lambda> (d, t). (Inr d, t)) (output_batches f F batches))" and
                                        drops="(\<lambda> _. filter (\<lambda> t. \<not> frontier_less_equal (frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1)))))) t) (ocaps (os 1) 1 @ map snd (cbufs (1, 1) @ outpu (os 0) 1 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))))"
                                        and  produs="(let batches = map (\<lambda> (d, t). (projl d, t)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1) @ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (d, t)) (filter is_Data (ltaken n (inps 1)))) in
                              let F = frontier (zmset_of (mset (ocaps (os 0) 1) + event.time `# filter_mset is_Mint (mset (ltaken n (inps 1))) - event.time `# filter_mset is_Drop (mset (ltaken n (inps 1))))) in
                              map (\<lambda> (d, t). (1, t, 1)) (output_batches f F batches))" 
                                        and os="os(0 := (os 0)\<lparr> ocaps := (ocaps ip_state)(1 := list_diff (ocaps (os 0) 1 @ map event.time (filter is_Mint (ltaken n (inps 1)))) (map event.time (filter is_Drop (ltaken n (inps 1))))), outpu := (outpu ip_state)(1 := []), consu := [], inter := [], produ := [] \<rparr>,
                                          1 := (os 1)\<lparr> ocaps := _, input := (\<lambda> _. input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1)))), outpu := _, consu := [], inter := [], produ := [], front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))), initia := True \<rparr>)"]; (rule refl)?)
                                             apply (subst dataplane_tracker_inv_clean2)
                                               defer
                                               defer
                                               apply (rule dataplane_tracker_inv_front_update[where nid=1 and c=c, rotated 4]; (rule refl)?)
                                                   apply (rule dataplane_tracker_inv_progress[where nid=1]; (rule refl)?)
                                                     apply (rule dataplane_tracker_inv_progress[where nid=0]; (rule refl)?)
                                                      apply (rule dataplane_tracker_inv_fold_consumes[where cbufs="(\<lambda> (nid, p). (if nid = 1 \<and> p =1 then cbufs (1, 0) @ outpu (os 0) 0  @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))) else []))" and nid=1 and p=1 and n="length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n (inps 1)))"]; (rule refl)?)
                                                      apply (rule dataplane_tracker_inv_update_outputs[where cbufs=cbufs and nid'=1 and p'=1 and p=1 and nid=0 and ys=Nil and xs="outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1)))"]; (rule refl)?)
                                                      apply (rule dataplane_tracker_inv_produces_drops[rotated 12, where oputs="\<lambda> _. map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1)))" and produs="map (\<lambda> e. (1, event.time e, 1)) (filter is_Data (ltaken n (inps 1)))" and drops="(\<lambda> _. map event.time (filter is_Drop (ltaken n (inps 1))))" and nid=0 and noutput="(outpu (os 1))( 0 := outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))"]; (rule refl)?)
                                                      apply (rule dataplane_tracker_inv_mints_many[where os=os and cbufs=cbufs and sg=sg and nid=0 and p=1 and xs="(map event.time (filter is_Mint (ltaken n (inps 1))))"])
                                  using N_INV(5) apply assumption
                                  using SIM2(10) apply assumption
                                  subgoal 
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: SIM2 comp_def)
                                    done
                                  subgoal 
                                    apply clarsimp
                                    subgoal for e
                                      apply (cases e; simp)
                                      apply (drule setltakenD)
                                      apply (drule Mint_in_Stream_le_Mint_in_C[rotated])
                                      using SIM2(13)[unfolded timely_input_stream_def] apply blast
                                      apply auto
                                      done
                                    done
                                  using N_INV(5) apply assumption
                                  subgoal
                                    apply (intro ext)
                                    apply simp
                                    done
                                  subgoal
                                    using SIM2(13) timely_input_stream_drops_subseteq_C_mints by auto
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: image_iff)
                                    subgoal for e
                                      apply (cases e; clarsimp del: disjCI simp add: image_iff)
                                      subgoal for t d
                                        using SIM2(13) timely_input_stream_Data_in_C_in by force
                                      done
                                    done
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: image_iff split: event.splits)
                                    subgoal for t d
                                      using SIM2(13) timely_input_stream_Data_in_C_in by force
                                    done
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: comp_def image_iff split: event.splits)
                                    apply (subst (2) filter_True)
                                     apply (simp_all add: comp_def)
                                    apply (rule arg_cong[where f=to_zmset])
                                    apply (rule map_cong)
                                     apply (auto split: event.splits)
                                    done
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: comp_def image_iff split: event.splits)
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: SIM2 comp_def)
                                    done
                                  using SIM2(3) apply assumption
                                  subgoal
                                    by (clarsimp del: disjCI simp add: comp_def image_iff split: event.splits)
                                  subgoal
                                    apply (intro ext)
                                    apply (clarsimp del: disjCI simp add: SIM2(17) comp_def image_iff split: if_splits event.splits)
                                    using SIM2(17) apply (metis not_01 zero_one)
                                    done
                                  subgoal
                                    by (simp add: antichain_from_list_singleton SIM2(1,2) my_summ_def)
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: comp_def image_iff split: event.splits)
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: SIM2 comp_def)
                                    done
                                  using N_INV(5) apply assumption
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: comp_def image_iff split: event.splits)
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: SIM2 comp_def)
                                    done
                                  subgoal
                                    by (clarsimp del: disjCI simp add: comp_def image_iff split: event.splits)
                                  subgoal
                                    apply (intro ext)
                                    apply (clarsimp del: disjCI simp add: SIM2(17) comp_def image_iff split: if_splits event.splits)
                                    apply (rule ccontr)
                                    using SIM2(17) apply (metis not_01 zero_one)
                                    done
                                  using N_INV(5) apply assumption
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: comp_def image_iff split: event.splits)
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: obtain_progress_def fold_consumes SIM2 comp_def)
                                    done
                                  subgoal
                                    by (clarsimp del: disjCI simp add: N_INV(5) comp_def image_iff split: event.splits)
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: SIM2(17) comp_def image_iff split: if_splits event.splits)
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: obtain_progress_def fold_consumes SIM2 comp_def)
                                    done
                                  subgoal
                                    by (clarsimp del: disjCI simp add: N_INV(5) comp_def image_iff split: event.splits)
                                  subgoal
                                    unfolding reachable_locations_def
                                    using loc_2_1_cases by (auto simp add: image_iff SIM2(1,2,3) split_beta my_summ_def split: prod.splits event.splits)
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                    apply (subst temp2(18)[symmetric])
                                    apply (clarsimp del: disjCI simp add: enum_num1_def obtain_progress_def fold_consumes operator_state.defs SIM2(1,2,4,5) image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                    apply (rule arg_cong2[where f="propagate_all"])
                                     apply simp_all
                                    apply (rule arg_cong3[where f="change_multiplicities"])
                                      apply simp_all
                                    unfolding extract_progress_def
                                    apply (simp add: comp_def split_beta change_multiplicities_append_alt)
                                    apply (rule arg_cong3[where f="change_multiplicities"])
                                      apply simp_all
                                    subgoal
                                      unfolding List.map_filter_def
                                      apply (simp add: comp_def split_beta)
                                      apply (rule map_cong)
                                       apply (rule filter_cong)
                                        apply (rule map_cong)
                                         apply (auto split: event.splits)
                                      done
                                    apply (rule arg_cong3[where f="change_multiplicities"])
                                      apply simp_all
                                    apply (simp flip: split_beta change_multiplicities_append_alt)
                                    apply (subst (1 2) change_multiplicities_comm)
                                    apply (simp add: comp_def split_beta change_multiplicities_append_alt)
                                    apply (rule arg_cong3[where f="change_multiplicities"])
                                      apply simp_all
                                    apply (simp flip: split_beta change_multiplicities_append_alt)
                                    apply (subst (1 2) change_multiplicities_comm)
                                    apply (simp add: comp_def split_beta change_multiplicities_append_alt)
                                    apply (rule arg_cong3[where f="change_multiplicities"])
                                      apply simp_all
                                    apply (simp flip: split_beta change_multiplicities_append_alt split: event.splits)
                                    using change_multiplicities_map_append_event apply fast
                                    done
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: SIM2(17) comp_def image_iff split: if_splits event.splits)
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: obtain_progress_def fold_consumes SIM2 comp_def)
                                    done
                                  subgoal
                                    by (clarsimp del: disjCI simp add: N_INV(5) comp_def image_iff split: event.splits)
                                             prefer 7
                                             apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                             apply (intro ext)
                                             apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                             apply (rule operator_state_eqI)
                                                      apply (clarsimp del: disjCI simp add: enum_num1_def image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                     apply (clarsimp del: disjCI simp add: enum_num1_def image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                    apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                    apply (clarsimp del: disjCI simp add: enum_num1_def image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                    apply (rule map_cong)
                                                     apply (rule filter_cong)
                                                      apply (simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def, simplified] comp_def map_concat)
                                  subgoal
                                    using concat_map_singleton[where f=snd] by (metis (no_types, lifting) cond_case_prod_eta snd_eqD)
                                  subgoal for t
                                    by auto
                                                    apply simp
                                                   apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                  subgoal
                                    unfolding output_batches_def outputs_ts_def Let_def
                                    apply (clarsimp del: disjCI simp add: map_concat image_iff comp_def split_beta  simp del: image_eqI simp flip: rmdups_append concat_append filter_filter list_diff_append map_append filter_append)
                                    apply (rule arg_cong[where f=concat])
                                    apply (rule map_cong)
                                    subgoal
                                      apply (rule arg_cong[where f=remdups])
                                      apply (simp add: comp_def flip: remdups_append2)
                                      apply (rule arg_cong2[where f=append])
                                       apply simp
                                       apply (simp add: split_beta filter_map)
                                       apply (rule map_cong)
                                      subgoal
                                        apply (rule filter_cong)
                                         apply (auto del: disjCI)
                                        subgoal for a b
                                          using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of b 1 0 1, simplified, unfolded my_summ_def, simplified]
                                          by auto
                                        done
                                       apply simp
                                      apply (rule arg_cong2[where f=append])
                                      subgoal
                                        apply (simp add: image_iff split_beta filter_map)
                                        apply (rule map_cong)
                                        subgoal
                                          apply (rule filter_cong)
                                           apply (auto simp add: SIM2(1,2) my_summ_def SIM2(8)[rule_format, of 1]   del: disjCI)
                                          subgoal for a b
                                            by blast
                                          done
                                        apply simp
                                        done
                                      apply (rule arg_cong2[where f=append])
                                      subgoal
                                        apply (simp add: image_iff split_beta filter_map)
                                        apply (rule map_cong)
                                        subgoal
                                          apply (rule filter_cong)
                                           apply (auto simp add: SIM2(1,2) my_summ_def SIM2(8)[rule_format, of 1]   del: disjCI)
                                          subgoal for a b
                                            by blast
                                          done
                                        apply simp
                                        done
                                      subgoal
                                        apply (simp add: image_iff split_beta filter_map)
                                        apply (rule map_cong)
                                        subgoal
                                          apply (rule filter_cong)
                                           apply (auto simp add: SIM2(1,2) my_summ_def SIM2(8)[rule_format, of 1]   del: disjCI split: event.splits)
                                          using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of _ 1 0 1, simplified, unfolded my_summ_def, simplified]
                                          apply blast
                                          done
                                        subgoal
                                          apply (auto simp add: SIM2(1,2) my_summ_def SIM2(8)[rule_format, of 1]   del: disjCI split: event.splits)
                                          done
                                        done
                                      done
                                    subgoal for t
                                      apply (rule map_cong)
                                      subgoal
                                        apply (rule arg_cong[where f=f])
                                        apply (simp add: filter_filter_pair_alt  comp_def split_beta  del: image_eqI flip: filter_filter  list_diff_append map_append filter_append)
                                        apply (subst (1) filter_True)
                                        subgoal
                                          apply (intro ballI impI conjI)
                                          apply (auto del: disjCI simp add: my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                          using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of _ 1 0 1, simplified, unfolded my_summ_def, simplified]
                                                         apply fast+
                                          done
                                        subgoal
                                          by (simp add: split_beta filter_map comp_def split: event.splits)
                                        done
                                      apply simp
                                      done
                                    done
                                                  apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                  apply (intro ext)
                                                  apply (rule filter_cong)
                                                   apply simp
                                  subgoal for p x
                                    apply (cases x)
                                    apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                    apply hypsubst_thin
                                    apply (intro conjI impI iffI)
                                    subgoal for a b
                                      apply (elim disjE)
                                      subgoal
                                        using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of b 1 0 1, simplified, unfolded my_summ_def, simplified]
                                        by (auto del: disjCI simp add: my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                      subgoal
                                        using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of b 1 0 1, simplified, unfolded my_summ_def, simplified]
                                        by (auto del: disjCI simp add: my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                      subgoal
                                        using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of b 1 0 1, simplified, unfolded my_summ_def, simplified]
                                        by (auto del: disjCI simp add: my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                      subgoal
                                        apply (auto 0 0 del: disjCI simp add: image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                        apply (intro disjI1)
                                        apply auto
                                        done
                                      done
                                    subgoal
                                      by auto
                                    subgoal
                                      apply (elim exE conjE disjE bexE)
                                      subgoal
                                        apply hypsubst_thin
                                        apply (rule FalseE)
                                        apply (auto del: disjCI simp add: image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                        apply force
                                        done
                                            apply auto
                                        apply force+
                                      subgoal
                                        apply (clarsimp simp add: image_iff split: event.splits)
                                        apply (rule FalseE)
                                        apply (auto del: disjCI simp add: image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                        apply force
                                        done
                                      done
                                    subgoal
                                      apply (elim exE conjE disjE bexE)
                                      subgoal
                                        apply hypsubst_thin
                                        apply (rule FalseE)
                                        apply (auto del: disjCI simp add: image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                        apply force
                                        done
                                            apply auto
                                        apply force+
                                      subgoal
                                        apply (clarsimp simp add: image_iff split: event.splits)
                                        apply (rule FalseE)
                                        apply (auto del: disjCI simp add: image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                        apply force
                                        done
                                      done
                                    subgoal
                                      apply (elim exE conjE disjE bexE)
                                      subgoal
                                        apply (clarsimp simp add: image_iff split: event.splits)

                                        apply hypsubst_thin
                                        apply (rule FalseE)
                                        apply (auto del: disjCI simp add: image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                        apply force
                                        done
                                            apply auto
                                        apply force
                                       apply force
                                      subgoal
                                        apply (clarsimp simp add: image_iff split: event.splits)
                                        apply (rule FalseE)
                                        apply (auto del: disjCI simp add: image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                        apply force
                                        done
                                      done
                                    done
                                                 apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                                 apply force
                                                apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                               apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                               apply (intro ext)
                                               apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                               apply (rule arg_cong2[where f=list_diff])
                                                apply simp
                                               apply (subst filter_True)
                                                apply simp
                                               apply (clarsimp del: disjCI simp add: image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                               apply (rule filter_cong)
                                                apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                  subgoal 
                                    apply (simp flip: append_assoc)
                                    apply (rule arg_cong2[where f=append])
                                    using concat_map_singleton[where f=snd] apply (metis (no_types, lifting) cond_case_prod_eta snd_eqD)
                                    using concat_map_singleton[where f=snd] apply (metis (no_types, lifting) cond_case_prod_eta snd_eqD)
                                    done
                                               apply simp
                                              apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                             apply simp
                                  subgoal
                                    apply (simp add: SIM2(1,2,3,4) flip: filter_filter list_diff_append map_append filter_append)
                                    apply (auto del: disjCI simp add: mset_concat comp_def subseteq_mset_def image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                    done
                                  subgoal
                                    unfolding output_batches_def outputs_ts_def
                                    apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                    apply (auto del: disjCI simp add: mset_concat comp_def subseteq_mset_def image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                    using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of _ 1 0 1, simplified, unfolded my_summ_def, simplified]
                                          apply fast
                                    using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of _ 1 0 1, simplified, unfolded my_summ_def, simplified]
                                         apply fastforce
                                    using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of _ 1 0 1, simplified, unfolded my_summ_def, simplified]
                                        apply fastforce
                                    using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of _ 1 0 1, simplified, unfolded my_summ_def, simplified]
                                       apply blast
                                      apply (metis event.simps(7) is_Data_def)
                                     apply (metis event.disc(2))
                                    apply (metis event.simps(5,7) is_Data_def)
                                    done
                                  subgoal
                                    unfolding output_batches_def outputs_ts_def
                                    apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                    apply (auto del: disjCI simp add: mset_concat comp_def subseteq_mset_def image_iff my_summ_def SIM2(8)[rule_format, of 1, unfolded SIM2(1,2), simplified] split_beta split: event.splits)
                                    using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of _ 1 0 1, simplified, unfolded my_summ_def, simplified]
                                        apply fast
                                    subgoal for d ab bb x
                                      apply (cases x; simp)
                                      apply auto
                                      done
                                    subgoal for d ab bb x
                                      apply (cases x; simp)
                                      apply auto
                                      done
                                    subgoal for d ab bb x
                                      apply (cases x; simp)
                                      apply auto
                                      done
                                    subgoal for d ab bb x
                                      apply (cases x; simp)
                                      apply auto
                                      done
                                    done
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                    apply (subst (2) filter_True)
                                     apply (simp_all add: comp_def split_beta)
                                    done
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: obtain_progress_def fold_consumes SIM2 comp_def)
                                    done
                                  subgoal
                                    by (clarsimp del: disjCI simp add: SIM2(3) SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                  subgoal
                                    by (clarsimp del: disjCI simp add: my_summ_def SIM2(1,2,3) SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                  subgoal
                                    apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                    apply (rule graph_summar_nt)
                                       apply (rule refl)+
                                      apply (rule SIM2(2)[unfolded SIM2(1)])
                                     apply (auto simp add: obtain_progress_def fold_consumes SIM2 comp_def)
                                    done
                                    apply (clarsimp del: disjCI simp add: SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                  subgoal
                                    apply (subst mset_ocaps_updates[where lxs="ldropn n (inps 1)"])
                                     apply (simp add: SIM2(4) operator_state.defs)
                                    using SIM2(13) apply simp
                                    using timely_input_stream_ldrop[OF N_INV(3) SIM2(13)] apply (simp add: SIM2(4) operator_state.defs)
                                    done
                                   apply simp
                                  apply (intro allI conjI)
                                         apply (clarsimp del: disjCI simp add: fold_consumes obtain_progress_def SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)
                                  subgoal
                                    apply (auto del: disjCI simp add: operator_state.defs SIM2(4,5) fold_consumes obtain_progress_def SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)[1]
                                    apply (intro ext)
                                    apply simp_all
                                    subgoal
                                      apply (rule arg_cong2[where f=append])
                                      using concat_map_singleton[where f=snd] apply (metis (no_types, lifting) cond_case_prod_eta snd_eqD)
                                      using concat_map_singleton[where f=snd] apply (metis (no_types, lifting) cond_case_prod_eta snd_eqD)
                                      done
                                    done
                                  subgoal
                                    by (auto del: disjCI simp add: operator_state.defs SIM2(4,5) fold_consumes obtain_progress_def SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)[1]
                                  subgoal
                                    by (auto del: disjCI simp add: operator_state.defs SIM2(4,5) fold_consumes obtain_progress_def SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)[1]

                                  subgoal
                                    by (auto del: disjCI simp add: operator_state.defs SIM2(4,5) fold_consumes obtain_progress_def SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)[1]
                                  subgoal
                                    by (auto del: disjCI simp add: SIM2(14) operator_state.defs SIM2(4,5) fold_consumes obtain_progress_def SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)[1]
                                   apply (auto del: disjCI simp add: operator_state.defs SIM2(4,5) fold_consumes obtain_progress_def SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)[1]
                                  subgoal
                                    by (auto del: disjCI simp add: SIM2(14) operator_state.defs SIM2(4,5) fold_consumes obtain_progress_def SIM2(8)[rule_format, of 1, unfolded SIM2(1), simplified, unfolded my_summ_def] image_iff comp_def split_beta  simp del: image_eqI simp flip: filter_filter list_diff_append map_append filter_append)[1]
                                  done
                                subgoal
                                  apply (simp add: operator_state.defs SIM2(4) del: mset_filter to_zmset_correct mset.simps update_zmultiset_simps_more split: event.splits sum.splits)
                                  apply (subst mset_ocaps_updates[where lxs="ldropn n (inps 1)"])
                                  using SIM2(13) apply simp
                                  using timely_input_stream_ldrop[OF N_INV(3) SIM2(13)] apply simp
                                  done
                                subgoal
                                  apply (simp only:  simp_thms diff01 fun_upd_apply fst_conv snd_conv operator_state_ty2.simps operator_state_ty.simps operator_state.simps split_beta operator_state.defs split: if_splits)
                                  apply (intro ext)
                                  apply (simp add: SIM2(14))
                                  done
                                subgoal
                                  apply (simp only:  simp_thms diff01 fun_upd_apply fst_conv snd_conv operator_state_ty2.simps operator_state_ty.simps operator_state.simps split_beta operator_state.defs split: if_splits)
                                  apply (simp add: SIM2(15))
                                  done
                                subgoal
                                  supply filter_True[simp] filter_False[simp] list_emb_Nil2[simp] BULK_BENQ_right_empty[simp] BULK_BENQ_left_empty[simp]
                                  unfolding fun_upd_def
                                  apply (simp add: comp_def  flip: filter_append map_append list_diff_append)
                                  subgoal
                                    unfolding input_ocaps_inv_def
                                    apply (simp add: comp_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def flip: filter_append map_append list_diff_append set_append)
                                    apply (intro ballI allI impI conjI)
                                    subgoal for a b
                                      apply (elim conjE)
                                      apply (subst (asm) set_append)
                                      apply (simp only: Un_iff)
                                      apply (elim disjE)
                                      subgoal
                                        using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of b 1 0 1, simplified, unfolded my_summ_def, simplified]
                                        apply -
                                        apply (drule meta_mp)
                                        subgoal
                                          by blast
                                        subgoal
                                          by auto
                                        done
                                      subgoal
                                        by auto
                                      done
                                    subgoal for a b
                                      apply (elim conjE)
                                      apply (subst (asm) set_append)
                                      apply (simp only: Un_iff)
                                      apply (elim disjE)
                                      subgoal
                                        using SIM2(16)[unfolded input_ocaps_inv_def SIM2(8)[rule_format, of 1] SIM2(1) my_summ_def, rule_format, of b 1 0 1, simplified, unfolded my_summ_def, simplified]
                                        apply -
                                        apply (drule meta_mp)
                                        subgoal
                                          by blast
                                        apply auto
                                        done
                                      subgoal
                                        by auto
                                      done
                                    done
                                  done
                                subgoal
                                  by (simp add: SIM2(17)[simplified])
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
            done
          done
        done
      done
  qed
qed

section \<open>Correctness\<close>


abbreviation "my_sg \<equiv> init_subgraph (antichain_from_list oo my_summ)"

lemma correctness_aux:
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bots}, 'd1) event llist\<close>
  assumes T: "timely_input_stream (inps 1) (mset bots)"
  shows  "set_op {||} {||}
     (dataflow_op my_sg
       (dataflow_tree_to_operator (\<lambda>_. [])        ((input_dt (init_input_state default_internal_summary inps) :: (2, _, _, _, _) dataflow_tree)
          \<sqdot>\<^bsub>1\<^esub> batch_dt (init_operator_state_ty2 default_internal_summary) f))) \<approx>
    set_spec_op
     (cUn (cUn {||} {||})
       (cUnion
         ((\<lambda>t. cset_from_list
                 (map (\<lambda>x. ((1, 1), Inr x, t)) (f (coll (map (\<lambda>(x, t). Data t (projl x)) ((outputs_at_target (summ my_sg) init_op_states >> (\<lambda>_. []) >> inputs_at_target init_op_states) (1, 1)) @@- inps 1) t)))) |`|
          cUn (ts (inps 1)) (cset_from_list (map snd ((outputs_at_target (summ my_sg) init_op_states >> (\<lambda>_. []) >> inputs_at_target init_op_states) (1, 1)))))))
     {||}"
  apply (rule correctness_gen[where S="cempty" and os=init_op_states and SO="cempty" and D="cempty" and sg=my_sg and inps=inps and cbufs="\<lambda> _. []" and ip_state="(init_input_state default_internal_summary inps)" and bt_state="init_operator_state_ty2 default_internal_summary"])
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
  shows "set_op {||} {||} (compiled_batch_op (\<lambda> _. inps) f) \<approx>
         set_spec_op ((cUnion ((\<lambda>t. cset_from_list (map (\<lambda>x. ((1, 1), Inr x, t)) (f (coll inps t)))) |`| (ts inps)))) {||}"
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
  apply (drule set_op_soundness[OF correctness, of inps f ios p "(Inr r, t)", OF T])
    apply assumption+
  apply (clarsimp simp add: image_iff)
  done

lemma completeness:
  fixes inps :: \<open>('t :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bots}, 'd1) event llist\<close>
    and ios :: "(2 \<times> 1, 2 \<times> 1, ('d1 + 'b) \<times> 't) VIO llist"
  assumes T: "timely_input_stream inps (mset bots)"
  shows 
    "Data t d \<in> lset inps \<Longrightarrow> r \<in> set (f (coll inps t)) \<Longrightarrow>
   \<exists>ios. wtraced (compiled_batch_op (\<lambda> _. inps) f) ios \<and> VOut (1, 1) (Inr r, t) \<in> lset ios"
  using set_op_completeness[OF correctness, of inps "(1, 1)" _ f, simplified, unfolded image_iff, simplified, OF T] apply -
  apply (drule meta_spec)+
  apply (drule meta_mp)
   apply force
  apply auto
  done

end
