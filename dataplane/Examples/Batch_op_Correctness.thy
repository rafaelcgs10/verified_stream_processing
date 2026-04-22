theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Ooo_Input_op
  Batch_op
  "../Correctness/General"
  "../Correctness/Consumes"
  "../Correctness/Progress"
  "../Correctness/Produces"
  "../Correctness/Outputs"
  "../Correctness/Propagates"
  "../Correctness/Mints"
  Dataplane.LList_Haskell_Setup
  Source_op
  Set_op
  "HOL-ex.Sketch_and_Explore"
begin
no_notation shiftr  (infixl \<open>>>\<close> 55)

section \<open>Example\<close>

abbreviation "t0 \<equiv> MyPair (0 :: nat) (0 :: nat)"
abbreviation "t_1_0 \<equiv> MyPair (Suc 0) (0 :: nat)"
abbreviation "t_0_1 \<equiv> MyPair (0 :: nat) (Suc 0)"
abbreviation "t_1_1 \<equiv> MyPair (Suc 0) (Suc 0)"

abbreviation "list_inps_test \<equiv> 
 [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"
abbreviation "inps_test \<equiv> llist_of list_inps_test"

abbreviation init_input_state where
  "init_input_state su inps \<equiv> \<lparr> 
   intsum = su,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = undefined,
   ocaps = (\<lambda> _. [0]),
   initia = False,
   nfron = False,
   en1 = Inl,
   de1 = projl,
   is_en1 = \<top>,
   es = inps
   \<rparr>"

abbreviation init_operator_state_ty2 where
  "init_operator_state_ty2 su \<equiv> \<lparr> 
   intsum = su,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = undefined,
   ocaps = (\<lambda> _. []),
   initia = False,
   nfron = False,
   en1 = Inl,
   de1 = projl,
   is_en1 = \<top>,
   en2 = Inr,
   de2 = projr,
   is_en2 = \<top>
   \<rparr>"

abbreviation "l1 ip_state \<equiv> ((Logic (ooo_input_op {|1 :: 1|} ip_state) default_internal_summary) :: ('a, _, (_, 't) shared_state + (1 \<Rightarrow> 't antichain), 'c \<times> 't, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) dataflow_tree)"
abbreviation "l2 os2 f \<equiv> Logic (batch_op os2 f) default_internal_summary"
abbreviation "G f ip_state os2 \<equiv> Comp [(0 :: 2, 1) \<mapsto> (0, 1)] (l1 (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state)) (l2 (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2) f)"

abbreviation "test_op \<equiv> compile_dataflow (\<lambda> _. []) (G (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)]) (init_input_state default_internal_summary (\<lambda> _. inps_test)) (init_operator_state_ty2 default_internal_summary) )"

(* value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op)"
value [GHC] "check_prefix 100 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 100 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] test_op" *)
(* value [GHC] "check_prefix 100 [((1, 1), (Inr 3, MyPair 1 0)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1))] test_op"
 *)
section \<open>Generalized Correctness\<close>

definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then [0]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then [0 :: _ :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}]
   else [])"


lemma antichain_from_list_empty[simp]:
  "antichain_from_list [] = {}\<^sub>A"
  by (simp add: Executable.antichain_from_list_empty empty_antichain_def)


lemma weights_to_graph_fun_to_next[simp]:
  "weights_to_graph_fun
           (\<lambda>l1 l2.
               if 0 \<in>\<^sub>A antichain_from_list
                          (if 0 \<le> node l1 \<and> node l1 < 1 \<and> 0 \<le> node l2 \<and> node l2 < 1
                           then if node l1 = 0 \<and> node l2 = 0 \<and> Locations.is_Trg (port l1) \<and> is_Src (port l2) then [0] else []
                           else if 1 \<le> node l1 \<and> 1 \<le> node l2 then if 1 = node l1 \<and> 1 = node l2 \<and> Locations.is_Trg (port l1) \<and> is_Src (port l2) then [0] else []
                                else if 0 \<le> node l1 \<and> node l1 < 1 \<and> 1 \<le> node l2 \<and> is_Src (port l1) \<and> Locations.is_Trg (port l2)
                                     then case [(0, 1) \<mapsto> (0 :: 2, 1)] (node l1 - 0, idp (port l1)) of None \<Rightarrow> []
                                          | Some (offset, q) \<Rightarrow> if node l2 = 1 + offset \<and> q = idp (port l2) then [0] else []
                                     else [])
               then antichain_from_list [0] else antichain_from_list []) = 
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
       apply auto
      apply code_simp+
    done
  done

lemma dataflow_tree_to_graph_to_my_summ[simp]:
  "dataflow_tree_to_graph (Comp [(0, 1) \<mapsto> (0, 1)] (Logic op1 default_internal_summary) (Logic op2 default_internal_summary)) = (my_summ :: (2, 1) location \<Rightarrow> (2, 1) location \<Rightarrow> _ list)"
  unfolding dataflow_tree_to_graph_def Let_def default_internal_summary_def comp_def                                               
  apply (simp only: split: if_splits prod.splits)
  apply (intro allI impI conjI)
  subgoal
    apply clarsimp
    subgoal premises prems
      apply (rule ext)+
      subgoal for l1 l2
        apply (cases l1; cases l2)
        apply simp
        subgoal for nid1 lp1 nid2 lp2
          apply (cases lp1; cases lp2; simp add: my_summ_def)
           apply code_simp+
          done
        done
      done
    done
  subgoal
    apply (rule FalseE)
    apply (auto; hypsubst_thin)
         apply code_simp
    subgoal
      unfolding no_self_loop_checker_is_graph_checker graph_checker_def
      by (clarsimp simp add: image_iff split_beta split: prod.splits if_splits port.splits)
       apply code_simp
    subgoal
      by eval
    subgoal for l1 l2
      apply (cases l1; cases l2)
      apply simp
      subgoal for nid1 lp1 nid2 lp2
        by (cases lp1; cases lp2; simp add: incomparable_def if_distrib split: if_splits)
      done
    subgoal for nid
      by (clarsimp simp add: image_iff split_beta split: prod.splits if_splits port.splits)
    subgoal 
      unfolding bi_unique_def
      apply (clarsimp simp add: image_iff split_beta split: prod.splits if_splits port.splits)
      done
    done 
  done

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_op os f)"

abbreviation "G_op f ip_state os2 chns \<equiv>
   dataflow_tree_to_operator chns (G f (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state) (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2))"

declare if_cong[cong]


lemma outputs_at_target_my_summ[simp]:
  "outputs_at_target (antichain_from_list oo my_summ) os = (\<lambda> p. if p = (1, 0) then outpu (os 0) 0 else [])"
  unfolding outputs_at_target_def my_summ_def
  apply (rule ext)
  apply (auto simp add: antichain_from_list_singleton split: prod.splits if_splits)
  subgoal for nid
    apply (subgoal_tac "nid = 0")
     apply simp
    apply (subgoal_tac "{(nid' :: 2, p' :: 1). antichain_from_list (if nid' = 0 then [0] else []) \<noteq> {}\<^sub>A} = {(0, 1)}")
    subgoal
      by (smt (verit, ccfv_threshold) Batch_op_Correctness.antichain_from_list_empty Collect_cong Pair_inject Timely_Infrastructure.antichain_from_list_empty antichain_from_list_singleton split_cong
          the_elem_eq)
    subgoal premises
      apply transfer
      apply auto
      done
    done
  done

lemma coll_llist_of_map_Data[simp]:
  "coll (llist_of (map (\<lambda>(d, t). Data t (f d)) xs)) t = map (f o fst) (filter (\<lambda> (x, t'). t' = t) xs)"
  apply (induct xs)
   apply simp
  subgoal for x xs
    apply (cases x)
    apply (auto simp add: coll_LCons_Data)
    done
  done

lemma rcset_ts[simp]:
  "rcset (ts lxs) = event.time ` {x \<in> (lset lxs). is_Data x}"
  unfolding ts_def
  apply (auto simp add:  image_iff cset_of_llist.rep_eq split: event.splits)
   apply force
  apply (metis event.distinct(1,3) event.sel(1) is_Data_def)
  done

lemma snd_cfilter[simp]:
  "snd |`| cfilter (\<lambda>(d, t). P t) S = cfilter P (snd |`| S)"
  by (force simp add: image_iff split_beta simp flip: cin.rep_eq)

lemma cset_from_list_image_filter_cfilter:
  "cset_from_list |`| ((\<lambda>t. map (\<lambda>os. (os, Cap t 1)) (f (map (\<lambda>os. projl (fst os)) (filter (\<lambda>(d, t'). t' = t \<and> P t) xs)))) |`| cfilter P S) =
   (cset_from_list |`| ((\<lambda>t. map (\<lambda>os. (os, Cap t 1)) (f (map (\<lambda>os. projl (fst os)) (filter (\<lambda>(d, t'). t' = t) xs)))) |`| cfilter P S))"
  apply auto
  done

lemma cimage_cfilter_clean:
  "(\<forall> x. x |\<in>| S \<longrightarrow> Q x \<longleftrightarrow> P x) \<Longrightarrow>
   (\<lambda>t. F t (Q t)) |`| cfilter P S =
   ((\<lambda>t. F t True) |`| cfilter P S)"
  apply auto
  done

lemma cset_cfilter_split:
  "S = cUn (cfilter P S) (cfilter (Not o P) S)"
  by auto

(* FIXME: move me*)
lemma image_zmset_id[simp]:
  "image_zmset id M = M"
  apply transfer
  apply (auto simp add: equiv_zmset_def split_beta)
  done
lemma if_same[simp]:
  "(if nid' = nid then f nid else f nid') = f nid'"
  by simp


lemma correctness_gen:
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
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
    TIMESTAMP_COMPARE:
    "ID CCOMPARE('t) = Some compare"
    and
    EMPTY_INPUT:
    "input (os 0) = (\<lambda> _. [])"
  shows 
    \<open>set_op S D (dataflow_op sg (G_op f ip_state bt_state cbufs)) \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms(1-13,15) apply -
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
            by (simp add: cUn_assoc SIM1  flip:BULK_BENQ_assoc cinsert_code)
                 apply (simp_all add: SIM1)
          subgoal
            using SIM1
            unfolding ty1_check_def
            by (auto simp add: BTL_def BHD_def  my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(5,6,7)
            unfolding ty2_check_def
            apply (auto simp add: operator_state.defs comp_def fun_upd_def BTL_def BHD_def consumes_def add_caps_def BENQ_def my_summ_def BULK_BENQ_def outputs_at_target_def split: option.splits if_splits prod.splits)
            apply (meson UnCI img_fst in_set_tlD)
            done
          subgoal premises temp
            using SIM1(10) apply -
            apply (rule dataplane_tracker_inv_consumes[where xs="tl (cbufs (1, 1))"])
               apply assumption
            using temp(2,4) apply (simp add: BHD_def )
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
                        (rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))),
             ocaps := \<lambda>p. list_diff (ocaps (os 1) 1) (filter (\<lambda>t. \<not> frontier_less_equal (front (os 1) 1) t) (ocaps (os 1) 1)),
             input := \<lambda>p. filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<longrightarrow> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1),
             produ := produ (os 1) @
                map (\<lambda>x. (1, capability.time (snd x), 1))
                 (concat
                   (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (map (\<lambda>x. projl (fst x)) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))
                     (rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))),
             inter := operator_state.inter (os 1) @ map (\<lambda>x. (1, x, - 1)) (filter (\<lambda>t. \<not> frontier_less_equal (front (os 1) 1) t) (ocaps (os 1) 1)),
             nfron := False \<rparr>)"])
          apply (rule exI[of _ sg])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
          unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def
                   apply (simp add: map_tl SIM1(3-) drop_caps_def produces_def comp_def split_beta comp_op_def if_distrib  consumes_def add_caps_def BTL_def enum_num1_def operator_state.defs fun_upd_def)
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
                      apply (clarsimp simp add: SIM1(1,2) comp_def)
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
              by (auto simp add: comp_def)
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
          done
                  prefer 3
        subgoal  
          apply (rule FalseE)
          apply (drule propagate_all_terminates[unfolded not_def, rule_format, rotated 6])
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
          subgoal
            using TIMESTAMP_COMPARE by auto
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
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ "os(1 := fst (obtain_progress (os 1)))"])
          apply (rule exI[of _ "sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 1 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
          subgoal premises prems
            using prems(3) apply -
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
            apply (subst dataplane_tracker_inv_clean[where f="\<lambda>_. True"])
              defer
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
          apply (rule exI[of _ "sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 0 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
          subgoal premises prems
            using prems(3) apply -
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
            unfolding ty1_check_def
            by (auto simp add: operator_state.defs BTL_def BHD_def obtain_progress_def  my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(5,7)
            apply (auto simp add: ty2_check_def operator_state.defs comp_def fun_upd_def BTL_def BHD_def  obtain_progress_def split: option.splits if_splits prod.splits)
            done
          subgoal
            by (simp add: SIM1 obtain_progress_def)
          subgoal
            apply (subst dataplane_tracker_inv_clean[where f="\<lambda>_. True"])
              defer
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
          apply (rule exI[of _ "os(0 := (os 0)\<lparr> front := frontier \<circ> (\<lambda>p. c_imp c (Loc 0 (Trg 1))), initia := True, nfron := True \<rparr> )"])
          apply (rule exI[of _ "sg\<lparr>pt_tr := c, upfro := (upfro sg)(0 := False)\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
                   apply (simp_all add: SIM1)
          subgoal premises prems
            apply (simp add:  SIM1 dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            unfolding ooo_input_op_logic_def
            apply (simp add: operator_state.defs comp_def notifier_op_def SIM1(3-) dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
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
            apply (subst dataplane_tracker_inv_clean[where f="(upfro sg)(0 := False)", of _ "sg\<lparr>pt_tr := c\<rparr>" _ "os(0 := (os 0)\<lparr> front := frontier \<circ> (\<lambda>p. c_imp c (Loc 0 (Trg 1))) \<rparr> )"])
              apply simp_all
            apply (subgoal_tac "propagate_all (antichain_from_list \<circ>\<circ> my_summ) (pt_tr sg) = Some c \<Longrightarrow> dataplane_tracker_inv (map_entry 0 (front_update (\<lambda>_. frontier \<circ> (\<lambda>p. c_imp c (Loc 0 (Trg p))))) os) cbufs (sg\<lparr>pt_tr := c\<rparr>)")
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
                using TIMESTAMP_COMPARE by auto
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
          done
        subgoal  
          apply (rule FalseE)
          apply (drule propagate_all_terminates[unfolded not_def, rule_format, rotated 6])
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
          subgoal
            using TIMESTAMP_COMPARE by auto
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
          apply (rule exI[of _ "os(1 := (os 1)\<lparr> front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))), initia := True, nfron := True \<rparr> )"])
          apply (rule exI[of _ "sg\<lparr>pt_tr := c, upfro := (upfro sg)(1 := False)\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
                   apply (simp_all add: SIM1)
          subgoal premises prems
            apply (simp add:  SIM1 dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            unfolding ooo_input_op_logic_def
            apply (simp add: operator_state.defs comp_def notifier_op_def SIM1(3-) dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
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
            apply (subst dataplane_tracker_inv_clean[where f="(upfro sg)(1 := False)", of _ "sg\<lparr>pt_tr := c\<rparr>" _ "os(1:= (os 1)\<lparr> front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))) \<rparr> )"])
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
                using TIMESTAMP_COMPARE by auto
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
          done
        subgoal  
          apply (rule FalseE)
          apply (drule propagate_all_terminates[unfolded not_def, rule_format, rotated 6])
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
          subgoal
            using TIMESTAMP_COMPARE by auto
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
          apply (rule exI[of _ "os(1 := (os 1)\<lparr> front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))), initia := initia (os 1), nfron := frontier (c_imp c (Loc 1 (Trg 1))) \<noteq> front (os 1) 1 \<rparr> )"])
          apply (rule exI[of _ "sg\<lparr>pt_tr := c, upfro := (upfro sg)(1 := False)\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
                   apply (simp_all add: SIM1)
          subgoal premises prems
            apply (simp add:  SIM1 dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
            unfolding ooo_input_op_logic_def
            apply (simp add: operator_state.defs comp_def notifier_op_def SIM1(3-) dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def obtain_progress_def)
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
            apply (subst dataplane_tracker_inv_clean[where f="(upfro sg)(1 := False)", of _ "sg\<lparr>pt_tr := c\<rparr>" _ "os(1:= (os 1)\<lparr> front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))) \<rparr> )"])
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
                using TIMESTAMP_COMPARE by auto
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
            apply (rule arg_cong2[where f=set_spec_op])
             apply simp_all
            apply (rule arg_cong2[where f=cinsert])
             apply simp_all
            apply (rule arg_cong2[where f=cUn])
             apply simp_all
            apply (auto 0 0)
            subgoal for X Y
              apply (clarsimp simp add: image_iff split: event.splits)
              apply (intro exI conjI)
                 apply assumption
                apply auto
              apply (cases Y; simp)
              apply (clarsimp simp add: BULK_BENQ_def SIM1(1) outputs_at_target_my_summ inputs_at_target_def image_iff split: event.splits)
              done
            subgoal for X Y Z
              apply (clarsimp simp add: BULK_BENQ_def SIM1(1) outputs_at_target_my_summ inputs_at_target_def image_iff split: event.splits)
              apply (metis UnCI snd_eqD)
              done
            subgoal for X Y
              by (auto simp add: BULK_BENQ_def SIM1(1) outputs_at_target_my_summ inputs_at_target_def image_iff split: event.splits)
            subgoal for X Y Z
              apply (clarsimp simp add: BULK_BENQ_def SIM1(1) outputs_at_target_my_summ inputs_at_target_def image_iff split: event.splits)
              apply (metis UnCI snd_eqD)
              done
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
          done
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
              unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def drop_caps_def add_cap_def BTL_def BHD_def produce_def
              by (simp add: map_tl SIM1(2-) comp_def split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs fun_upd_def )
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
                    nprodu="produ (os 0)" and ninter="inter (os 0) @ map (\<lambda> t. (1, t, -1)) (ocaps (os 0) 0)" and V="nfron (os 0)" and drops ="ocaps (os 0)", simplified])
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
              apply (auto simp add: operator_state.defs intro: ev_drops.intros timely_productive.intros)
              using timely_monotone.intros(1) apply blast
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
              unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def add_cap_def BTL_def BHD_def produce_def
              by (simp add: map_tl SIM1(2-) comp_def split_beta comp_op_def if_distrib  enum_num1_def operator_state.defs fun_upd_def )
            subgoal
              unfolding inputs_at_target_def produce_def
              apply (clarsimp simp add: BULK_BENQ_def  produce_def)
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
                      nprodu="produ (os 0) @ [(1, t, 1)]" and ninter="inter (os 0)" and V="nfron (os 0)" and drops ="\<lambda> _. []", simplified])
                subgoal
                  apply (simp add: SIM1)
                  using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                  apply metis
                  done
                         apply fastforce
                        apply fastforce
                       apply fastforce
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
              apply (auto intro: ev_drops.intros timely_productive.intros)
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
              unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def drop_caps_def drop_cap_def BTL_def BHD_def produce_def
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
                    nprodu="produ (os 0)" and ninter="operator_state.inter (os 0) @ [(1, t, - 1)]" and V="nfron (os 0)" and drops ="(\<lambda> _. [t])", unfolded enum_num1_def, simplified])
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
              apply (auto intro: ev_drops.intros timely_productive.intros)
               apply (metis (no_types, lifting) count_mset_0_iff count_ne_remove ev_drops.simps ev_drops_LConsE event.distinct(2) event.inject(2) event.simps(9) lfinite_code(2) vacant_def)+
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
              unfolding dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def ooo_input_op_logic_def notifier_op_def add_cap_def BTL_def BHD_def
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
            done
          done
        done
      done
  qed
next
  case SIM2
  then show ?case sorry
qed





section \<open>Correctness\<close>

(* abbreviation "G inps f \<equiv> compile_dataflow (Comp [(0, 1) \<mapsto> (0, 1)] (l1 inps) (l2 f))"

lemma
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
   and f :: \<open>'d1 list \<Rightarrow> 'd2 list\<close>
   and S :: \<open>((2 \<times> 1) \<times> ('d1 + 'd2) \<times> 't) cset\<close>
 assumes \<open>S = cUnion (cimage (\<lambda> t. (cset_of_llist o llist_of) (map (\<lambda> x. ((2, 1), (Inr x, t))) (f (coll (inps 1) t)))) (ts (inps 1)))\<close>
  shows \<open>set_op {||} {||} (G inps f) \<approx> set_spec_op S {||}\<close>
  oops
 *)

end
