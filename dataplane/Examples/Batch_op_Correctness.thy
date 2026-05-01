theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Ooo_Input_op
  Batch_op
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
   front = (\<lambda> _. {}\<^sub>A),
   ocaps = (\<lambda> _. [0]),
   initia = True,
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
   front = (\<lambda> _. {}\<^sub>A),
   ocaps = (\<lambda> _. []),
   initia = False,
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

find_theorems cUn name: code

value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op)"
value [GHC] "check_prefix 11000 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 5000 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] test_op"
  (* too slow, but maybe it returns  
  value [GHC] "check_prefix 100 [((1, 1), (Inr 3, MyPair 1 0)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1))] test_op" *)



end
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

lemma antichain_from_list_pair_set_singleton[simp]:
  "{(nid' :: 2, p' :: 1). antichain_from_list (if nid' = 0 then [0] else []) \<noteq> {}\<^sub>A} = {(0, 0)}"
  apply (auto 10 10 simp add: if_distrib antichain_from_list_singleton)
  apply presburger
  done

(* FIXME: move me *)
lemma filter_not_emptyI:
  "\<exists> x \<in> set xs. P x \<Longrightarrow>
   filter P xs \<noteq> []"
  by (metis List.empty_filter_conv)


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
    \<open>optm sg = False\<close>
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
    OP_EXTRA_INVS:
    \<open>input (os 0) = (\<lambda> _. [])\<close>
    \<open>initia (os 0)\<close>
    \<open>\<not> upfro sg 1 \<longrightarrow> (front (os 1) 1 = ifrontier (summ sg) (-+-) (pt_tr sg) (Loc 1 (Trg 1)) \<and> initia (os 1))\<close>
    \<open>input_ocaps_inv (os 1)\<close>
    \<open>cbufs (0, 0) = []\<close>
  shows 
    \<open>set_op S D (dataflow_op sg (G_op f ip_state bt_state cbufs)) \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms(1-3,5-13,14,16,17,18,19,20,5) apply -
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
            using temp(2,3) apply (simp add: BHD_def )
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
            unfolding consumes_def add_caps_def
            using SIM1(16) apply simp
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def
            apply clarsimp
            apply (metis (no_types, lifting) UNIV_I UN_iff capability.sel(1) imageI snd_conv)
            done
          subgoal
            using SIM1(18) apply -
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
                        (rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))),
             ocaps := \<lambda>p. list_diff (ocaps (os 1) 1) (filter (\<lambda>t. \<not> frontier_less_equal (front (os 1) 1) t) (ocaps (os 1) 1)),
             input := \<lambda>p. filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<longrightarrow> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1),
             produ := produ (os 1) @
                map (\<lambda>x. (1, capability.time (snd x), 1))
                 (concat
                   (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (map (\<lambda>x. projl (fst x)) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))
                     (rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (ocaps (os 1) 1) \<and> \<not> frontier_less_equal (front (os 1) 1) t) (input (os 1) 1)))))),
             inter := operator_state.inter (os 1) @ map (\<lambda>x. (1, x, - 1)) (filter (\<lambda>t. \<not> frontier_less_equal (front (os 1) 1) t) (ocaps (os 1) 1)) \<rparr>)"])
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
          subgoal
            using SIM1(15) by auto
          subgoal
            using SIM1(1,2,5,15,16) apply -
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(17) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def
            apply clarsimp
            apply (metis (mono_tags, lifting)
                \<open>initia bt_state \<Longrightarrow> filter (\<lambda>t. \<not> frontier_less_equal (front bt_state 1) t) (ocaps bt_state 1) \<noteq> [] \<Longrightarrow> \<forall>n. (n = 1 \<longrightarrow> intsum (os 1) = (\<lambda>p1 p2. my_summ (Loc 1 (Trg 1)) (Loc 1 (Src 1)))) \<and> (n \<noteq> 1 \<longrightarrow> intsum (os n) = (\<lambda>p1 p2. my_summ (Loc n (Trg 1)) (Loc n (Src 1))))\<close>
                group_cancel.rule0 in_set_simps(2) my_summ_def prod.sel(2) zero_one)
            done
          subgoal
            using SIM1(18) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
            done
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
            using prems(2) apply -
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
          subgoal
            using SIM1(15) by auto
          subgoal
            using SIM1(16) by auto
          subgoal
            using SIM1(17) apply -
            unfolding obtain_progress_def input_ocaps_inv_def
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(18) apply -
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
          apply (rule exI[of _ "sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 0 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>"])
          apply (rule exI[of _ "cbufs"])
          apply (rule exI[of _ inps])
          apply (rule exI[of _ S])
          apply (rule exI[of _ D])
          apply (intro conjI)
          subgoal premises prems
            using prems(2) apply -
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
          subgoal
            unfolding obtain_progress_def
            using SIM1(15) by auto
          subgoal
            unfolding obtain_progress_def
            using SIM1(15) by auto
          subgoal
            using SIM1(17) apply -
            unfolding obtain_progress_def input_ocaps_inv_def
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(18) apply -
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
          apply (rule exI[of _ "sg\<lparr>pt_tr := c, upfro := (upfro sg)(1 := False)\<rparr>"])
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
                  apply (metis (no_types, lifting) loc_2_1_cases rangeI range_fst surjD)
                  apply (metis (no_types, lifting) loc_2_1_cases rangeI range_fst surjD)
                 apply (smt (verit, ccfv_threshold) is_empty_antichain_not_empty_list loc_2_1_cases my_summ_def zero_one)
                 apply (smt (verit, ccfv_threshold) is_empty_antichain_not_empty_list loc_2_1_cases my_summ_def zero_one)
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
              using assms(15) by force
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
              apply (rule sym)
              apply (rule propagate_all_preserves_ifrontier)
               apply auto       
              subgoal
                using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                apply metis
                done
              subgoal
              using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
              apply metis
              done
              done
            done
          subgoal
            using SIM1(17) apply -
            unfolding obtain_progress_def input_ocaps_inv_def
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(18) apply -
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
          subgoal
            using SIM1(17) apply -
            unfolding obtain_progress_def input_ocaps_inv_def
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using SIM1(18) apply -
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
            using SIM1(18) apply -
            unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
            apply clarsimp
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
              apply (auto simp add: operator_state.defs intro: ev_drops.intros timely_productive.intros)
              using timely_monotone.intros(1) apply blast
              done
            subgoal
              using SIM1(18) apply -
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
                      nprodu="produ (os 0) @ [(1, t, 1)]" and ninter="inter (os 0)" and drops ="\<lambda> _. []", simplified])
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
            subgoal
              using SIM1(18) apply -
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
              apply (auto intro: ev_drops.intros timely_productive.intros)
               apply (metis (no_types, lifting) count_mset_0_iff count_ne_remove ev_drops.simps ev_drops_LConsE event.distinct(2) event.inject(2) event.simps(9) lfinite_code(2) vacant_def)+
              done
            subgoal
              using SIM1(18) apply -
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
            subgoal
              using SIM1(18) apply -
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
            using timely_input_stream_advances_frontier[OF SIM2(13), of t] apply -
            apply (clarsimp simp flip: cin.rep_eq )
            subgoal for n
                apply (cases "n + length (outpu (os 0) 0) + length (cbufs (1, 0))")
                subgoal
                  apply (elim disjE conjE exE)
                  subgoal
                    apply (intro exI conjI[rotated])
                     apply (intro relcomppI)
                       apply (rule bisim_refl)
                      defer
                      apply (rule wbisim_refl)
                     apply (rule step_wstep)
                     apply (rule step_set_op_intro_Out)
                        apply (rule refl)+
                       apply assumption+
                     apply (rule refl)+
                    apply (rule wb_upto_b_sym)
                    apply (rule wb_upto_b_base)
                    unfolding R_def[simplified]
                    apply clarsimp
                    apply (rule exI[of _ "os"])
                    apply (rule exI[of _ "sg"])
                    apply (rule exI[of _ cbufs])
                    apply (rule exI[of _ inps])
                    apply (rule exI[of _ "S"])
                    apply (rule exI[of _ "cinsert ((nid, 1), d, t) D"])
                    apply (intro conjI)
                                 apply (simp_all add: SIM2 )
                    subgoal
                      using SIM2(4,6)
                      by (clarsimp simp add: operator_state.defs)
                    subgoal
                      using SIM2(5,7)
                      by (clarsimp simp add: operator_state.defs)
                    subgoal
                      using SIM2(18) apply -
                      unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
                      apply clarsimp
                      done
                    done
                  subgoal
                    apply (intro exI conjI[rotated])
                     apply (intro relcomppI)
                       apply (rule bisim_refl)
                      defer
                      apply (rule wbisim_refl)
                     apply (rule wstep_trans(1))
                      apply (rule relpowp_imp_rtranclp[where n="length (outpu (os 1) 0)"]) 
                      apply (simp only: relpowp_add)
                      apply (rule step_set_op_steps_Out_intro)
                        apply (rule steps_Tau_dataflow_op_steps_Out_intro[where p=1 and nid=1 and xs="(outpu (os 1) 0)"])
                        apply (subst dataflow_tree_to_operator_def)
                        apply (simp add: Relation.eq_OO)
                        apply (rule steps_map_op[where xs="map (\<lambda> x. Out _ (Inr x)) (outpu (os 1) 1)" ])
                          apply (rule refl)+
                         apply (clarsimp split: sum.splits)
                         apply blast
                        apply (rule steps_comp_op_R_Out[where p="Inr (1,1)" and xs="map _ (outpu (os 1) 1)"])
                           apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 1) (Inr x)) (outpu (os 1) 1)" ])
                             apply (rule refl)+
                            apply (clarsimp simp add: comp_def split: sum.splits)
                            apply fast
                           apply (subst batch_op_def)
                           apply (subst batch_op_logic_def)
                           apply (subst notifier_op_def)
                           apply simp
                           apply (rule steps_builder_op_Write_Some[where xs="outpu (os 1) 1" and ys=Nil and p=1])
                             apply simp
                            apply simp
                            apply (simp add: SIM2(5) operator_state.defs)
                           apply (rule refl)+
                        defer
                        apply (rule refl)+
                      apply (rule step_set_op_intro_Out)
                         apply (rule refl)+
                        apply force
                       apply assumption+
                      apply (rule refl)+
                     apply (rule wb_upto_b_sym)
                     apply (rule wb_upto_b_base)
                    unfolding R_def[simplified]
                     apply clarsimp
                     apply (rule exI[of _ "os(1 := (os 1)\<lparr> outpu := (outpu (os 1))(1 := []) \<rparr> ) "])
                     apply (rule exI[of _ "sg"])
                     apply (rule exI[of _ cbufs])
                     apply (rule exI[of _ inps])
                     apply (rule exI[of _ "cUn (cset_from_list (map (\<lambda> x. ((1, 1) ,x) ) (outpu (os 1) 1))) S"])
                     apply (rule exI[of _ "cinsert ((nid, 1), d, t) D"])
                     apply (intro conjI)
                                  apply (simp_all add: SIM2 )
                    subgoal
                      using SIM2(4) apply -
                      unfolding dataflow_tree_to_operator_def ooo_input_op_def batch_op_def batch_op_logic_def ooo_input_op_logic_def notifier_op_def add_cap_def BTL_def BHD_def
                      apply (clarsimp simp add: operator_state.defs)
                      done
                    subgoal premises temp
                      unfolding dataflow_tree_to_operator_def ooo_input_op_def batch_op_def batch_op_logic_def ooo_input_op_logic_def notifier_op_def add_cap_def BTL_def BHD_def
                      apply (clarsimp simp add: operator_state.defs inputs_at_target_def)
                      using cUn_commute apply metis
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
                    done
                  subgoal 
                    sorry
                  subgoal
                    apply (cases "upfro sg 1")
                    subgoal
                      apply (cases "propagate_all (summ sg) (pt_tr sg)")
                      subgoal
                        apply (rule FalseE)
                        apply (drule propagate_all_terminates[unfolded not_def, rule_format, rotated 6])
                        subgoal 
                          apply (simp add: SIM2 flip: dataflow_tree_to_graph_to_my_summ)
                          using dataflow_topology_from_tree.dataflow_topology_axioms
                            dataflow_tree_to_graph_to_my_summ apply blast
                          done
                             apply simp_all
                        subgoal
                          using SIM2(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
                          unfolding propagation_inv_def
                          apply clarsimp
                          done
                        subgoal
                          using SIM2(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
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
                        subgoal
                          using SIM2(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
                          unfolding propagation_inv_def
                          apply clarsimp
                          done
                        done
                      subgoal for c
                        apply (subgoal_tac "\<exists> x. (x, t) \<in> set (input (os 1) 1)")
                         defer
                        subgoal
                          unfolding outputs_at_target_def BULK_BENQ_def inputs_at_target_def
                          apply (clarsimp simp add: SIM2(1,2) my_summ_def split: if_splits prod.splits)
                           apply force
                          
                                done
                          
                        subgoal
                          apply (intro exI conjI[rotated])
                           apply (intro relcomppI)
                             apply (rule bisim_refl)
                            defer
                            apply (rule wbisim_refl)
                           apply (rule wstep_trans(1))
                            apply (rule relpowp_imp_rtranclp[where n="1 + 1 + length (outpu (os 1) 0)"]) 
                            apply (simp only: relpowp_add)
                            apply (intro relcomppI)
                              apply (rule step_n_Taus_set_op)
                               apply (simp only: relpowp_add relpowp_1)
                               apply (rule step_Tau_dataflow_op_Inp_Inl_intro[where ?conf' = c])
                                   apply (subst dataflow_tree_to_operator_def)
                                   apply (simp add: Relation.eq_OO)
                                   apply (rule step_map_op)
                                    apply (rule step_comp_op_R_Inp)
                                       apply (rule step_map_op)
                                        apply (subst batch_op_def)
                                        apply (subst batch_op_logic_def)
                                        apply (subst notifier_op_def)
                                        apply (rule step_builder_op_Read_None)
                                          apply (rule refl)
                                         apply simp
                                        apply (rule refl)
                                       apply force
                          subgoal
                            by (clarsimp simp add: ran_def image_iff comp_def split_beta split: if_splits option.splits sum.splits)
                                     apply (rule refl)+
                                   apply simp
                                  apply assumption+
                                apply (rule refl)+
                             apply (rule step_n_Taus_set_op)
                              apply (simp only: relpowp_add relpowp_1)
                              apply (rule step_Tau_dataflow_op_Tau_intro)
                              apply (rule step_map_op)
                               apply (rule step_comp_op_R_Tau)
                                 apply (rule step_map_op[of Tau])
                                  apply (simp add: SIM2(5) operator_state.defs)
                                  apply (rule step_builder_op_Silent)
                                     apply simp
                                    apply simp
                                   apply simp
                                   apply (intro conjI)
                          subgoal
                            apply (rule filter_not_emptyI)
                            subgoal
                                apply (frule propagate_all_frontier_c_imp_correctness[where loc="Loc 1 (Trg 1)"]; (clarsimp simp add: SIM2)?)
                                subgoal
                                  using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                                  apply metis
                                  done
                                subgoal
                                  using assms(14) by force
                                subgoal
                                  unfolding reachable_locations_def
                                  apply (auto simp add: image_iff split_beta )
                                  using loc_2_1_cases apply blast
                                  using loc_2_1_cases apply blast
                                   apply (smt (verit, del_insts) is_empty_antichain_not_empty_list loc_2_1_cases my_summ_def zero_one)+
                                  done
                                subgoal
                                  using SIM2(10)[unfolded dataplane_tracker_inv_def propagation_inv_def SIM2(1,2)] by auto
                                subgoal
                                  using SIM2(10)[unfolded dataplane_tracker_inv_def propagation_inv_def SIM2(1,2)] by auto
                                subgoal
                                  using SIM2(10)[unfolded dataplane_tracker_inv_def propagation_inv_def SIM2(1,2)] by auto
                                subgoal  for d x xa
                                  unfolding inputs_at_target_def
                                  apply simp
                                  apply (rule bexI[of _ t])
                                  subgoal
                                    apply (subgoal_tac "ifrontier (antichain_from_list \<circ>\<circ> my_summ) (-+-) (pt_tr sg) (Loc 1 (Trg 1)) = frontier (to_zmset (ocaps (os 0) 1))")
                                    subgoal
                                      by simp
                                    subgoal
                                      apply (subst dataflow_topology.implied_frontier_alt_def)
                                      subgoal
                                        using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
                                        apply metis
                                        done
                                      apply (subst comm_monoid_add_class.sum.subset_diff[where B="{Loc 0 (Trg 1), Loc 1 (Trg 1), Loc 1 (Src 1)}"])
                                        apply simp
                                      subgoal
                                        by auto
                                       apply simp
                                      apply (subst (2) comm_monoid_add_class.sum.neutral)
                                      subgoal
                                        apply simp
                                        subgoal premises temp
                                          using SIM2(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
                                          apply (elim exE conjE)
                                          subgoal premises INV for caps
                                            using temp apply -
                                        apply (intro conjI)
                                        subgoal
                                        apply (rule comm_monoid_add_class.sum.neutral)
                                        apply (clarsimp simp add: split_beta)
                                          using INV(3)[unfolded c_pts_inv_def c_pts_change_multiplicities extract_progress_def obtain_progress_def, rule_format, of "Loc 0 (Trg 1)"] apply -
                                          unfolding has_progress_def
                                          apply simp
                                          apply (subst INV(2)[unfolded Trg_caps_inv_def outputs_at_target_def, rule_format])
                                          apply (clarsimp simp add: SIM2(1,2) my_summ_def  split: prod.splits)
                                          using SIM2(18) apply simp
                                          done
                                        subgoal
                                        apply (rule comm_monoid_add_class.sum.neutral)
                                        apply (clarsimp simp add: split_beta)
                                          using INV(3)[unfolded c_pts_inv_def c_pts_change_multiplicities extract_progress_def obtain_progress_def, rule_format, of "Loc 1 (Trg 1)"] apply -
                                          unfolding has_progress_def
                                          apply simp
                                          apply (subst INV(2)[unfolded Trg_caps_inv_def outputs_at_target_def, rule_format])
                                          apply (clarsimp simp add: SIM2(1,2) my_summ_def  split: prod.splits)
                                          done
                                        subgoal
                                          apply (rule comm_monoid_add_class.sum.neutral)
                                          apply (clarsimp simp add: split_beta)
                                          apply (clarsimp simp add: SIM2(1,2) my_summ_def  split: prod.splits)
                                          subgoal premises prems2 for s
                                            apply (rule FalseE)
                                            using prems2(20) apply -
                                            unfolding comp_def
                                            apply (simp flip: member_antichain.rep_eq)
                                            apply (drule graph.path_weight_conv_path[rotated])
                                            subgoal
                                              sorry
                                            subgoal
                                              apply (clarsimp simp add: if_distrib[of antichain_from_list])

                                            find_theorems "set_antichain" "_ \<in>\<^sub>A _"

                                            find_theorems "_ \<in>\<^sub>A graph.path_weight _ _ _ \<Longrightarrow> _"

                                  using SIM2(17)[unfolded input_ocaps_inv_def, rule_format, of t 1 0 1] apply -
                                  apply simp

end
                                    apply (subgoal_tac "(\<Sum>loc'\<in>UNIV. zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) loc')))) -++- graph.path_weight (antichain_from_list \<circ>\<circ> my_summ) loc' (Loc 1 (Trg 1))) = {#}\<^sub>z")
                                   
                                    
end
                                    subgoal
                                      by simp
                                    subgoal
                                      apply (rule comm_monoid_add_class.sum.neutral)
                                      apply (clarsimp simp add: split_beta)
                                      apply (rule comm_monoid_add_class.sum.neutral)
                                      apply (clarsimp simp add: split_beta)
                                      subgoal for l s
                                        apply (subgoal_tac "c_pts (pt_tr sg) l = {#}\<^sub>z")
                                        subgoal
                                          by simp
                                        subgoal
                                          subgoal premises temp
                                            using SIM2(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
                                            apply (elim exE conjE)
                                            subgoal premises INV for caps
                                              using temp apply -
                                              using INV(3)[unfolded c_pts_inv_def c_pts_change_multiplicities, rule_format, of l] apply -
                                              unfolding extract_progress_def has_progress_def obtain_progress_def
                                              apply simp
                                              apply (elim disjE)
                                              subgoal
                                                apply (clarsimp simp add: )
                                                apply (subst INV(2)[unfolded Trg_caps_inv_def, rule_format])
                                                unfolding outputs_at_target_def
                                                apply (clarsimp simp add: SIM2(1,2) my_summ_def  split: prod.splits)
                                                subgoal for nid nid'
                                                  apply (subgoal_tac "nid' = 0")
                                                  subgoal
                                                    apply simp
                                                    apply (cases "nid = 0")
                                                    subgoal
                                                      using SIM2(18) by simp
                                                    subgoal
                                                      apply clarsimp
                                                      apply (drule mp)
                                                      subgoal
                                                        using loc_2_1_cases by blast
                                                      subgoal
                                                        by (simp add: antichain_from_list_singleton)
                                                      done
                                                    done
                                                  subgoal
                                                    apply (simp add: antichain_from_list_singleton if_distrib[of antichain_from_list])
                                                    subgoal premises temp
                                                      using temp(27) 
                                                      by (smt (verit, best) Collect_empty_eq antichain_nonempty is_singletonI' is_singleton_def mem_Collect_eq num1_eq1 old.prod.case old.prod.exhaust singleton_iff the_elem_eq)
                                                    done
                                                  done
                                                done
                                              subgoal
                                                apply (clarsimp simp add: )
                                                apply (subst INV(1)[unfolded Src_caps_inv_def, rule_format])
                                                apply (clarsimp simp add: SIM2(1,2) my_summ_def  split: prod.splits)
                                                subgoal for nid'
                                                  apply (subgoal_tac "nid' = 0")
                                                  subgoal
                                                    apply simp
                                                    using SIM2(13)

                                                    find_theorems ocaps timely_input_stream


end
  subgoal
    apply simp
    apply (cases "nid = 0")
    subgoal
      using SIM2(18) by simp
    subgoal
      apply clarsimp
      apply (drule mp)
      subgoal
        using loc_2_1_cases by blast
      subgoal
        by (simp add: antichain_from_list_singleton)
      done
    done
  subgoal
    apply (simp add: antichain_from_list_singleton if_distrib[of antichain_from_list])
    subgoal premises temp
      using temp(27) 
      by (smt (verit, best) Collect_empty_eq antichain_nonempty is_singletonI' is_singleton_def mem_Collect_eq num1_eq1 old.prod.case old.prod.exhaust singleton_iff the_elem_eq)
    done
  done
  done

find_theorems "antichain_from_list [_]"




end
  subgoal
    apply (simp add: SIM2(5) operator_state.defs)

    subgoal premises temp
      using SIM2(10)[unfolded dataplane_tracker_inv_def, simplified] apply -
      apply (elim exE conjE)
      subgoal premises INV for caps
        using temp apply -
        using INV(3)[unfolded c_pts_inv_def c_pts_change_multiplicities, rule_format, of "Loc 1 (Src 1)"] apply -

        using
          INV(3)[unfolded c_pts_inv_def c_pts_change_multiplicities, rule_format, of "Loc 1 (Trg 1)"]
          INV(2)[unfolded Trg_caps_inv_def, rule_format, of 1 1] apply -



        using INV(1)[unfolded Src_caps_inv_def, rule_format, of 1 1, symmetric] apply -

        find_theorems bt_state


end
  apply (simp only: relpowp_add relpowp_1)
  apply (rule step_set_op_intro_Tau_2)
  apply (rule refl)+
  apply (rule step_Tau_dataflow_op_Tau_intro)
  apply (rule step_map_op)
  apply (rule step_comp_op_R_Tau)
  apply (rule step_map_op)
  apply (rule step_builder_op_Silent[where p=1])
  apply (rule refl)+
  apply (simp add: SIM2(5) operator_state.defs)
  subgoal
    apply (simp add: SIM2(5) operator_state.defs)


    term dataflow_op

    using SIM2(16)

    thm cUn_commute

end

end
thm step_tau_Out_pow_comp_op_steps_intro

thm step_set_op_steps_Out_intro

thm step_set_op_intro_Out

find_theorems step Out builder_op


end
  apply (cases "upfro sg 1")
  subgoal
    apply (intro exI conjI[rotated])
    apply (intro relcomppI)
    apply (rule bisim_refl)
    defer
    apply (rule wbisim_refl)
    apply (rule wstep_trans(1))
    apply (rule relpowp_imp_rtranclp[
          where n="
                             1 +
                             1 +
                             (let f_colls = (\<lambda> t'. f (coll (llist_of (map (\<lambda>(x, t). Data t (projl x)) (input (os 1) 0))) t')) in
                             let ts = rmdups {} (map snd ((input (os 1) 0))) in 
                             length (outpu (os 1) 0) + length (concat (map f_colls ts)))"]) 
    apply (simp only: relpowp_add)
    apply (intro relcomppI)
    apply (rule step_n_Taus_set_op)
    apply (simp only: relpowp_add relpowp_1)
    apply (rule step_Tau_dataflow_op_Inp_Inl_intro[where ?conf' = "(pt_tr sg)\<lparr> c_work := (\<lambda> _. {#}\<^sub>z), c_imp := _ \<rparr>"])
    apply (subst dataflow_tree_to_operator_def)
    apply (simp add: Relation.eq_OO)
    apply (rule step_map_op)
    apply (rule step_comp_op_R_Inp)
    apply (rule step_map_op)
    apply (subst batch_op_def)
    apply (subst batch_op_logic_def)
    apply (subst notifier_op_def)
    apply (rule step_builder_op_Read_None3)
    apply (rule refl)
    apply simp
    apply (rule refl)
    apply force
    subgoal
      by (clarsimp simp add: ran_def image_iff comp_def split_beta split: if_splits option.splits sum.splits)
    apply (rule refl)+
    apply simp
    defer
    apply assumption
    apply (rule refl)+
    apply (simp only: relpowp_add relpowp_1)
    apply (rule step_set_op_intro_Tau_2)
    apply (rule refl)+
    apply (rule step_Tau_dataflow_op_Tau_intro)
    apply (rule step_map_op)
    apply (rule step_comp_op_R_Tau)
    apply (rule step_map_op)
    apply (rule step_builder_op_Silent[where p=1])
    apply (rule refl)+
    apply (simp add: SIM2(5) operator_state.defs)
    subgoal
      apply (simp add: SIM2(5) operator_state.defs)



      find_theorems bt_state


end

  apply (intro exI conjI[rotated])
  apply (intro relcomppI)
  apply (rule bisim_refl)
  defer
  apply (rule wbisim_refl)
  apply (rule wstep_trans(1))
  apply (rule relpowp_imp_rtranclp[
      where n="n + 
                             (length (outpu (os 0) 0)) + n + 
                             (n + length (outpu (os 0) 0) + length (cbufs (1, 0))) +
                             1 +
                             (let f_colls = (\<lambda> t'. f (coll (map (\<lambda>(x, t). Data t (projl x)) ((input (os 1) 0) @ (chns (1, 1)) @ (outpu (os 0) 0)) @@- ltake n (inps 1)) t')) in
                             let ts = rmdups {} (filter (\<lambda> t. t \<notin> event.time ` lset (ldropn n (inps 1))) (map snd ((input (os 1) 0) @ (chns (1, 1)) @ (outpu (os 0) 0)) @ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> t) (filter is_Data (ltaken n (inps 1)))))) in 
                             length (outpu (os 1) 0) + length (concat (map f_colls ts)))"]) 
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
  apply (rule step_builder_op_n_Silents[where n=n])
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
  apply (rule step_tau_Out_pow_comp_op_steps_intro)
  apply (rule steps_map_op)
  apply (rule refl)+


  find_theorems steps builder_op


end
  apply (rule step_Tau_dataflow_op_Inp_Inl_intro[where nid=1])
  apply (subst dataflow_tree_to_operator_def)
  apply (simp add: Relation.eq_OO)
  apply (rule step_map_op[of "Inp _ _"])
  apply (rule step_comp_op_R_Inp)
  apply (rule step_map_op[of "Inp None _"])            
  apply (subst batch_op_def)
  apply (subst batch_op_logic_def)
  apply (subst notifier_op_def)
  apply (rule step_builder_op_Read_None3)
  apply (rule refl)
  apply simp
  apply (rule refl)
  apply force
  subgoal
    by (clarsimp simp add: ran_def image_iff comp_def split_beta split: if_splits option.splits sum.splits)
  apply (rule refl)+
  apply simp
  prefer 2
  subgoal



    find_theorems  upfro



end
  apply simp
  prefer 2
  apply (rule refl)
  prefer 2
  apply (rule refl)
  prefer 2
  apply simp
  apply blast

thm step_tau_pow_map_op

find_theorems step builder_op front

find_theorems name: step_builder_op_Read_None
  oops



end
  apply (rule step_tau_pow_map_op)
  apply (rule step_taus_L_pow_comp_op_steps_intro)
  apply (rule step_tau_pow_map_op)
  apply (subst ooo_input_op_def)
  apply (rule step_builder_op_n_Silents[where n=n])
  apply (rule ooo_input_op_logic_iterates_n[where OS="{| ip_state |}" and os=ip_state and p=1])
  subgoal
    by (simp add: SIM2(4,13) operator_state.defs)
  apply simp
  apply simp
  defer
  subgoal
    by (simp add: SIM2(4,13) operator_state.defs)
  apply (rule refl)+


  find_theorems n 

  apply (clarsimp simp add: cimage_iff  simp flip: cin.rep_eq split: if_splits)

  find_theorems ip_state

end
  apply (subst cfilter_cinsert)

  oops

  find_theorems  cfilter cinsert


  term "inps 1"

  find_theorems ts

  term "let f_colls = (\<lambda> t'. f (coll (map (\<lambda>(x, t). Data t (projl x)) ((input (os 1) 0) @ (chns (1, 1)) @ (outpu (os 0) 0)) @@- ltake n (inps 1)) t')) in
                    let ts = rmdups {} (filter (\<lambda> t. t \<notin> event.time ` lset (ldropn n (inps 1))) (map snd ((input (os 1) 0) @ (chns (1, 1)) @ (outpu (os 0) 0)) @ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> t) (filter is_Data (ltaken n (inps 1)))))) in 
                    length (concat (map f_colls ts))"

  term coll

  term ""

  oops



  find_consts "enat \<Rightarrow> nat"

  find_theorems "lfilter _ _ = LCons _ _"


end
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
