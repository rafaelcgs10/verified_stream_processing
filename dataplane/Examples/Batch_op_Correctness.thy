theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Ooo_Input_op
  Batch_op
  "../Correctness/General"
  "../Correctness/Consumes"
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

value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op)"
value [GHC] "check_prefix 100 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 100 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 100 [((1, 1), (Inr 3, MyPair 1 0)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1))] test_op"

section \<open>Generalized Correctness\<close>

definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then antichain_from_list [0]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [0 :: _ :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}]
   else {}\<^sub>A)"


lemma antichain_from_list_empty[simp]:
  "antichain_from_list [] = {}\<^sub>A"
  by (simp add: Executable.antichain_from_list_empty empty_antichain_def)


lemma weights_to_graph_fun_to_next[simp]:
  "weights_to_graph_fun
           (\<lambda>l1 l2.
               (if 0 \<le> node l1 \<and> node l1 < 1 \<and> (1 :: 2) \<le> node l2 \<and> is_Src (port l1) \<and> Locations.is_Trg (port l2)
                then If (0 \<in>\<^sub>A antichain_from_list (case [(0, 1) \<mapsto> (0, 1)] (node l1 - 0, idp (port l1)) of None \<Rightarrow> [] | Some (offset, q) \<Rightarrow> if node l2 = 1 + offset \<and> q = idp (port l2) then [0] else []))
                else If (0 \<in>\<^sub>A antichain_from_list
                                 ((if node l1 = 0 \<and> node l2 = 0 \<and> Locations.is_Trg (port l1) \<and> is_Src (port l2) then [0] else []) @
                                  (if 1 = node l1 \<and> 1 = node l2 \<and> Locations.is_Trg (port l1) \<and> is_Src (port l2) then [0] else []))))
                (antichain_from_list [0]) {}\<^sub>A) = 
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
       apply (auto 0 0 dest!: not_in_empty simp add: antichain_empty set_antichain1 enum_location_def enum_port_def Numeral_Type.enum_num1_def comp_def Enum.enum_prod_def split: sum.splits option.splits sum.splits)
    subgoal premises
      apply code_simp
      done
    done
  done

lemma dataflow_tree_to_graph_to_my_summ[simp]:
  "dataflow_tree_to_graph (Comp [(0, 1) \<mapsto> (0, 1)] (Logic op1 default_internal_summary) (Logic op2 default_internal_summary)) = (my_summ :: (2, 1) location \<Rightarrow> (2, 1) location \<Rightarrow> _ antichain)"
  unfolding dataflow_tree_to_graph_def Let_def default_internal_summary_def
  apply (simp only: split: prod.splits)
  apply (intro allI impI)
  apply (subst (5) if_P)
  subgoal
    apply auto
    subgoal premises prems
      using prems(3) apply -
      apply (auto simp add: if_distrib enum_location_def enum_port_def Numeral_Type.enum_num1_def comp_def Enum.enum_prod_def split: list.splits if_splits sum.splits option.splits sum.splits)
      apply code_simp
      apply eval
      done
    subgoal premises
      unfolding weights_to_graph_fun_def enum_location_def enum_num1_def Enum.enum_prod_def no_self_loop_checker_def
      by (auto simp add: antichain_empty antichain_from_list_empty enum_location_def enum_port_def Numeral_Type.enum_num1_def comp_def Enum.enum_prod_def split: sum.splits option.splits sum.splits)
    subgoal premises
      unfolding implementation_graph_checker_def
      unfolding weights_to_graph_fun_def enum_location_def enum_num1_def Enum.enum_prod_def no_self_loop_checker_def
      by (auto simp add: antichain_empty antichain_from_list_empty enum_location_def enum_port_def Numeral_Type.enum_num1_def comp_def Enum.enum_prod_def split: sum.splits option.splits sum.splits)
    done
  subgoal premises prems
    using prems(1) apply -
    apply clarsimp
    subgoal premises
      unfolding my_summ_def
      apply (rule ext)+
      subgoal for l1 l2
        using loc_2_1_cases[where l=l1] apply -
        using loc_2_1_cases[where l=l2] apply -
        apply (elim disjE; hypsubst_thin)
                       apply (auto 0 0 simp add: antichain_empty antichain_from_list_empty enum_location_def enum_port_def Numeral_Type.enum_num1_def comp_def Enum.enum_prod_def split: sum.splits option.splits sum.splits)
        apply (rule FalseE)
        apply code_simp
        done
      done
    done
  done

abbreviation "coll inps t \<equiv> list_of (lmap (\<lambda> e. case e of Data t d \<Rightarrow> d) (lfilter (\<lambda> e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps))"

abbreviation "ts inps \<equiv> cimage (\<lambda> e. case e of Data t d \<Rightarrow> t) (cfilter is_Data (cset_of_llist inps))"

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_op os f)"

abbreviation "G_op f ip_state os2 chns \<equiv>
   dataflow_tree_to_operator chns (G f (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state) (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2))"

declare if_cong[cong]

lemma correctness_gen:
  fixes inps :: \<open>1 \<Rightarrow> ('t :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
    and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
    and ip_state :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
    and bt_state :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
    and os :: \<open>2 \<Rightarrow> (1, 'd1 + 'd2, 't) operator_state\<close>
    and chns :: \<open>2 \<times> 1 \<Rightarrow> (('d1 + 'd2) \<times> 't) list\<close>
    and sg :: \<open>(2, 1, 't) subgraph\<close>
  assumes
    SUBGRAPH_INV:
    \<open>summ sg = dataflow_tree_to_graph (G f ip_state bt_state)\<close>
    \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    \<open>graph_summar_nt (summ sg) (nxt sg) os\<close>
    and
    OP_STATE_INV: 
    \<open>ip_state = operator_state.extend (os 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, es = inps\<rparr>\<close>
    \<open>bt_state = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr\<rparr>\<close>
    \<open>ty1_check ip_state (curry cbufs 0)\<close>
    \<open>ty2_check bt_state (curry cbufs 1)\<close>
    and
    BUFS_INV: 
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    and
    DT_INV:
    \<open>dataplane_tracker_inv os cbufs sg\<close>
    and S_INV:
    \<open>SP = cUnion (cimage 
      (\<lambda> t. (cset_of_llist o llist_of) (map (\<lambda> x. ((2, 1), (Inr x, t))) (f (coll ((map (\<lambda> (x, t). Data t (projl x)) (chns (1, 0))) @@- (inps 1)) t))))
      (cUn (ts (inps 1)) (cset_of_llist (llist_of (map snd (chns (1, 0)))))))\<close>
    \<open>SO = cset_of_llist (llist_of (map (\<lambda> x. ((2, 1), x)) (outpu (os 1) 0)))\<close>
    and
    INP_STREAM_INV:
    \<open>timely_input_stream (inps 0) (mset (ocaps (os 0) 0))\<close>
  shows 
    \<open>set_op S D (dataflow_op sg (G_op f ip_state bt_state cbufs)) \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms apply -
proof (coinduction arbitrary: os sg ip_state bt_state chns cbufs inps SP SO S D rule: weakBisimWeakUptoBisimCong)
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
            clarsimp simp only: IO.simps ; hypsubst_thin ? ; clarsimp simp flip: cin.rep_eq split: option.splits sum.splits prod.splits if_splits ; hypsubst_thin?)
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
            subgoal premises temp
            using SIM1(1,2,3)
            unfolding graph_summar_nt_def consumes_def add_caps_def
            by auto
          subgoal premises
            using SIM1
            unfolding ty1_check_def
            by (fastforce simp add:  Src_from_Trg_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1
            unfolding ty2_check_def
            by (fastforce simp add:  Src_from_Trg_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
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
            by (simp add: map_tl comp_op_def if_distrib SIM1 consumes_def add_caps_def BTL_def enum_num1_def operator_state.defs fun_upd_def)
          subgoal
            by (simp add: cUn_assoc SIM1  flip:BULK_BENQ_assoc cinsert_code)
                apply (simp_all add: SIM1)
          subgoal premises temp
            using SIM1(1,2,3)
            unfolding graph_summar_nt_def consumes_def add_caps_def
            by auto
          subgoal
            using SIM1
            unfolding ty1_check_def
            by (auto simp add: BTL_def BHD_def  Src_from_Trg_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(5,6,7)
            unfolding ty2_check_def
            apply (auto simp add: operator_state.defs comp_def fun_upd_def BTL_def BHD_def Src_from_Trg_def consumes_def add_caps_def BENQ_def my_summ_def BULK_BENQ_def outputs_at_target_def split: option.splits if_splits prod.splits)
            apply (meson UnCI img_fst in_set_tlD)
            done
          subgoal premises temp
            using SIM1(9) apply -
            apply (rule dataplane_tracker_inv_consumes[where xs="tl (cbufs (1, 1))"])
               apply assumption
            using temp(2,4) apply (simp add: BHD_def )
            using SIM1(1) apply simp
            subgoal
              using dataflow_tree_to_graph_to_my_summ dataflow_topology_from_tree.dataflow_topology_axioms
              by metis
            subgoal
              using SIM1(3) by force
            done
          subgoal
            using SIM1(12) by auto
          done




end
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (BENQ (1, 1) (Inr (a, b)) (\<lambda>x. map Inr (cbufs x)))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} (ip_state\<lparr>outpu := (outpu ip_state)(1 := xs)\<rparr>) (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (bt_state\<lparr>nfron := False\<rparr>) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "initia ip_state"
      and "outpu ip_state 1 = (a, b) # xs"
    for a :: "'d1 + 'd2"
      and b :: 't
      and xs :: "(('d1 + 'd2) \<times> 't) buf"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (BTL (1, 1) (\<lambda>x. map Inr (cbufs x)))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} ip_state (ooo_input_op_logic {|1|}))) \<oslash>)))) op2'"
    if "Inr (1, 1) \<in> ran (case_sum ((\<lambda>_. None)::2 \<Rightarrow> (2 + 2 \<times> 1) option) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid. (\<lambda>p. case if (nid::2) = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q))::1 \<Rightarrow> (_ \<times> _) option)))"
      and "cbufs (1, 1) \<noteq> []"
      and "initia bt_state"
      and "is_Inl (BHD (1, 1) (\<lambda>x. map Inr (cbufs x))::((1, 't) shared_state + (1 \<Rightarrow> 't antichain)) + ('d1 + 'd2) \<times> 't)"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (BTL (1, 1) (\<lambda>x. map Inr (cbufs x)))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} ip_state (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (consumes (bt_state\<lparr>nfron := False\<rparr>) 1 t d) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "Inr (1, 1) \<in> ran (case_sum ((\<lambda>_. None)::2 \<Rightarrow> (2 + 2 \<times> 1) option) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid. (\<lambda>p. case if (nid::2) = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q))::1 \<Rightarrow> (_ \<times> _) option)))"
      and "cbufs (1, 1) \<noteq> []"
      and "initia bt_state"
      and "(Inr (d, t)::((1, 't) shared_state + (1 \<Rightarrow> 't antichain)) + ('d1 + 'd2) \<times> 't) = BHD (1, 1) (\<lambda>x. map Inr (cbufs x))"
    for d :: "'d1 + 'd2"
      and t :: 't
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} os' (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (bt_state\<lparr>nfron := False\<rparr>) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "initia ip_state"
      and "os' |\<in>| ooo_input_op_logic {|1|} ip_state"
      and "ocaps ip_state 1 \<noteq> []"
    for os' :: "(1, 'd1 + 'd2, 'd1, 't) input_state"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 1 (nxt sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} ip_state (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} os' (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "initia bt_state"
      and "has_progress (bt_state\<lparr>nfron := False\<rparr>)"
      and "(os', st) = obtain_progress (bt_state\<lparr>nfron := False\<rparr>)"
    for st :: "(1, 't) shared_state"
      and os' :: "(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 0 (nxt sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} os' (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (bt_state\<lparr>nfron := False\<rparr>) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "initia ip_state"
      and "has_progress ip_state"
      and "(os', st) = obtain_progress ip_state"
    for st :: "(1, 't) shared_state"
      and os' :: "(1, 'd1 + 'd2, 'd1, 't) input_state"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>pt_tr := x2, upfro := (upfro sg)(0 := False)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} (ip_state \<lparr>front := frontier \<circ> (\<lambda>p. c_imp x2 (Loc 0 (Trg 1))), initia := True, nfron := True\<rparr>) (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (bt_state\<lparr>nfron := False\<rparr>) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "upfro sg 0"
      and "\<not> initia ip_state"
      and "propagate_all (summ sg) (pt_tr sg) = Some x2"
    for x2 :: "((2, 1) location, 't) configuration"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>pt_tr := x2, upfro := (upfro sg)(1 := False)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} ip_state (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (bt_state \<lparr>front := frontier \<circ> (\<lambda>p. c_imp x2 (Loc 1 (Trg 1))), initia := True, nfron := True\<rparr>) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "Inl 1 \<notin> ran (case_sum ((\<lambda>_. None)::2 \<Rightarrow> (2 + 2 \<times> 1) option) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid. (\<lambda>p. case if (nid::2) = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q))::1 \<Rightarrow> (_ \<times> _) option)))"
      and "\<not> initia bt_state"
      and "upfro sg 1"
      and "propagate_all (summ sg) (pt_tr sg) = Some x2"
    for x2 :: "((2, 1) location, 't) configuration"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>pt_tr := x2, upfro := (upfro sg)(1 := False)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} ip_state (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (bt_state \<lparr>front := frontier \<circ> (\<lambda>p. c_imp x2 (Loc 1 (Trg 1))), nfron := frontier (c_imp x2 (Loc 1 (Trg 1))) \<noteq> front bt_state 1\<rparr>) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "Inl 1 \<notin> ran (case_sum ((\<lambda>_. None)::2 \<Rightarrow> (2 + 2 \<times> 1) option) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid. (\<lambda>p. case if (nid::2) = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q))::1 \<Rightarrow> (_ \<times> _) option)))"
      and "initia bt_state"
      and "upfro sg 1"
      and "propagate_all (summ sg) (pt_tr sg) = Some x2"
    for x2 :: "((2, 1) location, 't) configuration"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op (cinsert ((1, 1), ab, bb) S) D (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} ip_state (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (bt_state \<lparr>nfron := False, outpu := (outpu bt_state)(1 := xs)\<rparr>) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "initia bt_state"
      and "outpu bt_state 1 = (ab, bb) # xs"
    for ab :: "'d1 + 'd2"
      and bb :: 't
      and xs :: "(('d1 + 'd2) \<times> 't) buf"
    using that sorry
  ultimately show ?thesis
    apply -
    unfolding R_def[symmetric]
    subgoal premises prems2
      apply (simp add: wsim_def dataflow_tree_to_operator_def batch_op_def batch_op_logic_def ooo_input_op_def notifier_op_def)
      apply (intro allI conjI impI)
      apply (elim step_builder_op_elim step_set_op_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim conjE ; 
          clarsimp simp only: IO.simps ; hypsubst_thin ? ; clarsimp simp flip: cin.rep_eq split: option.splits sum.splits prod.splits if_splits ; hypsubst_thin?)
      subgoal
        using prems2(1) by assumption
      subgoal
        using prems2(2) by assumption
      subgoal
        using prems2(3) by assumption
      subgoal
        using prems2(4) by assumption
      subgoal
        using prems2(5) by assumption
      subgoal
        using prems2(6) by assumption
      subgoal
        using prems2(7) by assumption
      subgoal
        using prems2(8) by assumption
      subgoal
        using prems2(9) by assumption
      subgoal
        using prems2(10) by assumption
      subgoal
        using prems2(11) by assumption
      done
    done
qed
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
