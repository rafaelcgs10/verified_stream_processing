theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Ooo_Input_op
  Batch_op
  "../MyProduct_Instances"
  "../AntichainOrder"
  Dataplane.LList_Haskell_Setup
  Source_op
  Set_op
  "HOL-ex.Sketch_and_Explore"
begin
no_notation shiftr  (infixl \<open>>>\<close> 55)

declare cin.rep_eq[simp del]

section \<open>Example\<close>

abbreviation "t0 \<equiv> MyPair (0 :: nat) (0 :: nat)"
abbreviation "t_1_0 \<equiv> MyPair (Suc 0) (0 :: nat)"
abbreviation "t_0_1 \<equiv> MyPair (0 :: nat) (Suc 0)"
abbreviation "t_1_1 \<equiv> MyPair (Suc 0) (Suc 0)"


definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then antichain_from_list [0]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then antichain_from_list [0]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [0]
   else {}\<^sub>A)"

lemma weights_to_graph_fun_to_next[simp]:
  "weights_to_graph_fun
           (\<lambda>l1 l2.
               remove_non_zero_weights (If (0 \<le> node l1 \<and> node l1 < 1 \<and> 1 \<le> node l2 \<and> is_Src (port l1) \<and> Locations.is_Trg (port l2)))
                (case [(0, 1) \<mapsto> (0, 1)] (node l1 - 0, idp (port l1)) of None \<Rightarrow> frontier {#}\<^sub>z
                 | Some (offset, q) \<Rightarrow> if node l2 = 1 + offset \<and> q = idp (port l2) then antichain_from_list [0] else antichain_from_list [])
                ((if node l1 = 0 \<and> node l2 = (0 :: 2) \<and> Locations.is_Trg (port l1) \<and> is_Src (port l2) then antichain_from_list [0] else antichain_from_list []) +
                 (if 1 = node l1 \<and> 1 = node l2 \<and> Locations.is_Trg (port l1) \<and> is_Src (port l2) then antichain_from_list [0] else antichain_from_list []))) = 
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
       apply (auto 0 0 simp add: antichain_empty set_antichain1 antichain_from_list_empty enum_location_def enum_port_def Numeral_Type.enum_num1_def comp_def Enum.enum_prod_def split: sum.splits option.splits sum.splits)
    using not_in_empty apply blast+
      apply code_simp
    using not_in_empty apply blast+
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
      apply (auto simp add: enum_location_def enum_port_def Numeral_Type.enum_num1_def comp_def Enum.enum_prod_def split: sum.splits option.splits sum.splits)
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

abbreviation "list_inps_test \<equiv> 
 [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"
abbreviation "inps_test \<equiv> llist_of list_inps_test"

abbreviation init_input_state where
  "init_input_state su inps \<equiv> \<lparr> 
   summar = su,
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
   es = inps
   \<rparr>"
abbreviation init_operator_state_ty2 where
  "init_operator_state_ty2 su \<equiv> \<lparr> 
   summar = su,
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
   en2 = Inr,
   de2 = projr
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

abbreviation "coll inps t \<equiv> list_of (lmap (\<lambda> e. case e of Data t d \<Rightarrow> d) (lfilter (\<lambda> e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps))"

abbreviation "ts inps \<equiv> cimage (\<lambda> e. case e of Data t d \<Rightarrow> t) (cfilter is_Data (cset_of_llist inps))"

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_op os f)"

abbreviation "G_op f ip_state os2 chns \<equiv>
   dataflow_tree_to_operator chns (G f (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state) (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2))"

definition "c_pts_inv c caps = (\<forall> l. c_pts c l = caps l)"
definition "Src_caps_inv caps os = (\<forall> nid p. caps (Loc nid (Src p)) = zmset_of (mset (ocaps (os nid) p)))"
definition "Trg_caps_inv caps bufs = (\<forall> nid p. caps (Loc nid (Trg p)) = zmset_of (mset (map snd (bufs (nid, p)))))"
definition "extract_prog eds os = concat (map (\<lambda> nid. extract_progress nid eds (snd (obtain_progress (os nid)))) Enum.enum)"
definition "front_inv os c = (\<forall> nid p. front (os nid) p \<le> frontier (c_imp c (Loc nid (Trg p))))"
definition "imp_front_inv su c = (\<forall> l. frontier (c_imp c l) \<le> ifrontier su (+) c l)"
definition "chnls_imp_front_inv su c chns = (\<forall> nid p. \<forall> t \<in> snd ` set (chns (nid, p)). frontier_less_equal (ifrontier su (+) c (Loc nid (Trg p))) t)"

definition "propagation_inv su c = 
  (dataflow_topology.inv_imps_work_sum su (-+-) c \<and>
   dataflow_topology.inv_implications_nonneg c \<and>
   dataflow_topology.inv_imp_plus_work_nonneg c)"

definition "changes_non_zero_inv cgs = (\<forall>d\<in>snd ` snd ` set cgs. d \<noteq> 0)"
definition "changes_above_impl_inv su c cgs = 
  ((\<forall>(l, t, d)\<in>set cgs. frontier_less_equal (ifrontier su (+) c l) t) \<and>
   (\<forall> l' \<in> fst ` set cgs. let (cgs_l, cgs') = partition (\<lambda> (l, t, d). l' = l) cgs in
                         (\<forall> (l, t, d) \<in> set cgs'. frontier_less_equal (ifrontier su (+) (change_multiplicities su cgs_l c) l) t)))"

abbreviation "su_test a b \<equiv> dataflow_tree_to_graph (
    Comp [(0, 0) \<mapsto> (1, 1), (1, 0) \<mapsto> (0, 0)] 
    (Comp [(0, 0) \<mapsto> (0, 0)] (Logic (\<oslash> :: (_, _, unit + unit) op) (\<lambda> _ _. [0 :: nat])) (Logic \<oslash> (\<lambda> _ _. [0 :: nat])))
    (Comp [(0 :: 4, 0 :: 2) \<mapsto> (0, 0)] (Logic \<oslash> (\<lambda> _ _. [0 :: nat])) (Logic \<oslash> (\<lambda> _ _. [0 :: nat])))
    ) a b"


definition Src_from_Trg where
  "Src_from_Trg su nid p = {(nid', p'). su (Loc nid' (Src p')) (Loc nid (Trg p)) \<noteq> {}\<^sub>A}"

definition "outputs_at_target su os = (\<lambda> (nid, p). let S = Src_from_Trg su nid p in if S = {} then [] else let (nid', p') = Set.the_elem S in outpu (os nid') p')"
definition "inputs_at_target os = (\<lambda> (nid, p). input (os nid) p)"

lemma outputs_at_target_consumes[simp]:
  "outputs_at_target su (os(nid := consumes (os nid) p' t d)) = outputs_at_target su os"
  unfolding outputs_at_target_def consumes_def Src_from_Trg_def add_caps_def
  apply (rule ext)+
  apply (auto split: if_splits prod.splits)
  done


definition "all_isl l = (\<forall> x \<in> fst ` set l. isl x)"

definition "dataplane_tracker_inv os cbufs sg Pcaps = 
   (\<exists> c c' cgs chns caps.
     c = pt_tr sg \<and>
     cgs = extract_prog (edges sg) os \<and>
     chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os \<and>
     Src_caps_inv caps os \<and>
     Trg_caps_inv caps cbufs \<and>
     cgs = extract_prog (edges sg) os \<and>
     c' = change_multiplicities (summ sg) cgs c \<and>
     c_pts_inv c' caps \<and>
     front_inv os c \<and>
     imp_front_inv (summ sg) c \<and>
     chnls_imp_front_inv (summ sg) c chns \<and>
     changes_non_zero_inv cgs \<and>
     propagation_inv (summ sg) c \<and>
     Pcaps caps)"

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
    \<open>edges sg = graph_to_edges (summ sg)\<close>
    and
    OP_STATE_INV: 
    \<open>ip_state = operator_state.extend (os 0) \<lparr>en1 = Inl, de1 = projl, es = inps\<rparr>\<close>
    \<open>bt_state = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, en2 = Inr, de2 = projr\<rparr>\<close>
    \<open>all_isl (chns (0, 0))\<close>
    and
    BUFS_INV: 
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    and
    DT_INV:
    \<open>dataplane_tracker_inv os cbufs sg Pcaps\<close>
    and S_INV:
    \<open>SP = cUnion (cimage 
      (\<lambda> t. (cset_of_llist o llist_of) (map (\<lambda> x. ((2, 1), (Inr x, t))) (f (coll ((map (\<lambda> (x, t). Data t (projl x)) (chns (0, 0))) @@- (inps 1)) t))))
      (cUn (ts (inps 1)) (cset_of_llist (llist_of (map snd (chns (0, 0)))))))\<close>
    \<open>SO = cset_of_llist (llist_of (map (\<lambda> x. ((2, 1), x)) (outpu (os 1) 0)))\<close>
    and
    INP_STREAM_INV:
    \<open>Pcaps = (\<lambda> caps. timely_input_stream (inps 0) C \<and> zmset_of C = caps (Loc 0 (Src 0)))\<close>
  shows 
    \<open>set_op S D (dataflow_op sg (G_op f ip_state bt_state cbufs)) \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms apply -
proof (coinduction arbitrary: os sg ip_state bt_state chns cbufs inps SP SO S D C Pcaps rule: weakBisimWeakUptoBisimCong)
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
        apply (simp only: trace_simp)
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
                 apply (simp only: trace_simp)
                 apply (simp add: SIM1)
                apply (simp add: SIM1)
               apply (simp add: SIM1)
              apply (simp add: SIM1)
          subgoal
            using SIM1
            by (auto simp add: all_isl_def Src_from_Trg_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          using SIM1 apply fastforce+
          done
                 defer
        defer
        subgoal for d t
      apply (cases "cbufs (1, 1)"; simp add: BHD_def BTL_def)
      subgoal for a as
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
                 apply simp
                 apply (simp only: trace_simp)
         apply (simp add: SIM1 BTL_def BENQ_def add_caps_def operator_state.defs(3))
         apply (rule arg_cong3[where f=set_op])
           apply (rule refl)+
            apply (rule arg_cong2[where f=dataflow_op])
           apply (rule refl)+
            apply (rule arg_cong3[where f=map_op])
           apply (rule refl)+
            apply (rule arg_cong4[where f=comp_op])
            apply (rule refl)+
            apply (rule arg_cong2[where f=case_sum])
          apply (rule refl)+
  apply fastforce
            apply (rule arg_cong3[where f=map_op])
              apply (rule refl)+
            apply (rule arg_cong3[where f=map_op])
              apply (rule refl)+
            apply (rule arg_cong5[where f=builder_op])
           apply (rule refl)+
        apply (simp add: consumes_def add_caps_def  enum_num1_def operator_state.defs(3))
           apply (rule refl)+
  subgoal premises prems2
    apply (rule arg_cong2[where f=set_spec_op])
     apply simp_all
    using SIM1(6,8,9) apply -
    apply (simp only: cUn_assoc)
    apply (rule arg_cong2[where f= cUn])
     apply simp_all
    subgoal premises
      apply (rule arg_cong2[where f= cUn])
       apply simp_all
      unfolding inputs_at_target_def 
      apply simp
      apply (rule arg_cong2[where f= cUn])
      subgoal
        apply (rule arg_cong[where f= cUnion])
        apply (rule arg_cong2[where f=cimage])
         apply simp_all
        apply (rule ext)+
        apply (rule arg_cong[where f=cset_of_llist])
        apply (rule arg_cong[where f=llist_of])
        apply (rule map_cong)
         apply simp_all
        apply (rule arg_cong[where f=f])
        apply (rule arg_cong[where f=list_of])
        apply (rule arg_cong2[where f=lshift])
         apply simp_all
        apply (rule map_cong)
         apply simp_all
        apply (rule filter_cong)
         apply simp_all
        apply (rule map_cong)
         apply simp_all
        apply (simp flip: BULK_BENQ_assoc)
        unfolding consumes_def add_caps_def BULK_BENQ_def BTL_def
        apply simp
        done
      subgoal
        apply (rule arg_cong[where f= cUnion])
        apply (rule arg_cong2[where f=cimage])
         apply (rule ext)+
         apply (rule arg_cong[where f=cset_of_llist])
         apply (rule arg_cong[where f=llist_of])
         apply (rule map_cong)
          apply simp_all
         apply (rule arg_cong[where f=f])
         apply (rule arg_cong[where f=list_of])
         apply (rule arg_cong2[where f=lshift])
          apply simp_all
         apply (rule map_cong)
          apply simp_all
         apply (rule filter_cong)
          apply simp_all
         apply (rule map_cong)
          apply simp_all
         apply (simp flip: BULK_BENQ_assoc)
        unfolding consumes_def add_caps_def BULK_BENQ_def BTL_def
         apply simp
        unfolding consumes_def add_caps_def BULK_BENQ_def BTL_def
        apply simp
        done
      done
    done

        find_theorems BULK_BENQ name: ass

end
  using SIM1(1,12,13,14) apply -
  apply simp
  apply hypsubst_thin


  find_theorems c

  defer
  defer
  defer
  defer
  defer
  defer


  apply (simp_all only: SIM1 dataflow_tree_to_graph_to_my_summ)
  defer
  using SIM1(21) apply simp
  using SIM1(1,20) apply simp
  defer
  defer
  defer
  using SIM1(1,16) apply simp
  using SIM1(1,15) apply simp
  using SIM1(22) apply simp

  find_theorems graph_to_edges

end

  apply (rule arg_cong[where f="cUnion"])
  apply (rule arg_cong2[where f="cimage"])
  apply (rule ext)+
  apply (simp split: prod.splits)
  apply (rule refl)



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
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 1 (edges sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} ip_state (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} os' (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
    if "initia bt_state"
      and "has_progress (bt_state\<lparr>nfron := False\<rparr>)"
      and "(os', st) = obtain_progress (bt_state\<lparr>nfron := False\<rparr>)"
    for st :: "(1, 't) shared_state"
      and os' :: "(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2"
    using that sorry
  moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (set_spec_op (cUn (cUn S SO) SP) D) op2' \<and> ((~) OO \<U> R OO (\<approx>)) (set_op S D (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 0 (edges sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case if nid = 0 then Some (0, 1) else None of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (1 + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (builder_op False {||} {|1|} os' (ooo_input_op_logic {|1|}))) (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (builder_op True {|1|} {|1|} (bt_state\<lparr>nfron := False\<rparr>) (\<lambda>os. if nfron os then if filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1) = [] then trace STR ''No capabilities'' {||} else let compl_batches = \<lambda>p t. map (de1 (os\<lparr>nfron := False\<rparr>) \<circ> fst) (filter (\<lambda>(d, t'). t' = t \<and> t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)); ts = \<lambda>p. rmdups {} (map snd (filter (\<lambda>(d, t). t \<in> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p))); osa = os\<lparr>nfron := False, input := \<lambda>p. filter (\<lambda>(d, t). t \<notin> set (filter (\<lambda>t. \<not> frontier_less_equal (front os p) t) (ocaps os p))) (input (os\<lparr>nfron := False\<rparr>) p)\<rparr> in Let {|(concat (map (\<lambda>t. map (\<lambda>x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda>t. Cap t 1) (filter (\<lambda>t. \<not> frontier_less_equal (front os 1) t) (ocaps os 1)))|} ((|`|) (\<lambda>(outs, drops). trace (STR ''outs: '' + show_nat (length outs) + STR '' , drops: '' + show_nat (length drops)) (drop_caps (produces osa (map (\<lambda>(d, y). (en2 osa d, y)) outs)) drops))) else {||}))))))) op2'"
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
