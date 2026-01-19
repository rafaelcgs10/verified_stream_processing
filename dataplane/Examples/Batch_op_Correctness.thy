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
   is_en1 = \<top>,
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

abbreviation "coll inps t \<equiv> list_of (lmap (\<lambda> e. case e of Data t d \<Rightarrow> d) (lfilter (\<lambda> e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps))"

abbreviation "ts inps \<equiv> cimage (\<lambda> e. case e of Data t d \<Rightarrow> t) (cfilter is_Data (cset_of_llist inps))"

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_op os f)"

abbreviation "G_op f ip_state os2 chns \<equiv>
   dataflow_tree_to_operator chns (G f (ip_state :: (1, 'd1 + 'd2, 'd1, _) input_state) (os2 :: (1, 'd1 + 'd2, 'd1, 'd2, _) operator_state_ty2))"

definition "c_pts_inv c caps = (\<forall> l. c_pts c l = caps l)"
definition "Src_caps_inv caps os = (\<forall> nid p. caps (Loc nid (Src p)) = to_zmset (ocaps (os nid) p))"
definition "Trg_caps_inv caps bufs = (\<forall> nid p. caps (Loc nid (Trg p)) = to_zmset (map snd (bufs (nid, p))))"
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

lemma inputs_at_target_consumes[simp]:
  "inputs_at_target (os(nid := consumes (os nid) p t d)) = BENQ (nid, p) (d, t) (inputs_at_target os)"
  unfolding inputs_at_target_def consumes_def add_caps_def BENQ_def
  by (auto split: if_splits)

definition "ty1_check os bufs = (\<forall> p. (\<forall> x \<in> fst ` set (input os p) \<union> fst ` set (bufs p) \<union> fst ` set (outpu os p). is_en1 os x))"
definition "ty2_check os bufs = (\<forall> p. (\<forall> x \<in> fst ` set (input os p) \<union> fst ` set (bufs p). is_en1 os x) \<and> (\<forall> x \<in> fst ` set (outpu os p). is_en2 os x))"

definition "dataplane_tracker_inv os cbufs sg = 
   (\<exists> c c' cgs chns caps.
     c = pt_tr sg \<and>
     cgs = extract_prog (edges sg) os \<and>
     chns = outputs_at_target (summ sg) os >> cbufs \<and>
     Src_caps_inv caps os \<and>
     Trg_caps_inv caps chns \<and>
     cgs = extract_prog (edges sg) os \<and>
     c' = change_multiplicities (summ sg) cgs c \<and>
     c_pts_inv c' caps \<and>
     front_inv os c \<and>
     imp_front_inv (summ sg) c \<and>
     chnls_imp_front_inv (summ sg) c chns \<and>
     changes_non_zero_inv cgs \<and>
     propagation_inv (summ sg) c \<and>
     changes_above_impl_inv (summ sg) c cgs)"



lemma zmset_map_filter_Trg_extract_prog:
  "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog (edges sg) os))) = 
   (\<Sum>x\<in>UNIV. \<Sum>xa\<leftarrow>produ (os x). zmset (map (\<lambda>x. snd xa) (filter (\<lambda>x. nid = fst x \<and> p = snd x) (edges sg (x, fst xa)))))
     - zmset (map snd (filter (((=) (p :: 'p :: enum)) o fst) (consu (os nid)))) "
  unfolding extract_prog_def extract_progress_def obtain_progress_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (subst (1) monoid_add_class.sum_list_distinct_conv_sum_set)
   apply (simp_all add:  comm_monoid_add_class.sum.distrib enum_class.enum_distinct enum_class.enum_UNIV)
  done

lemma filter_loc_Trg_extract_prof_consumes_diff_nids[simp]:
  "nid \<noteq> nid' \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog (edges sg) (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog (edges sg) os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply auto
  done

lemma filter_loc_Src_extract_prof_consumes_diff_nids[simp]:
  "nid \<noteq> nid' \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid' (Src p') = l') (extract_prog (edges sg) (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Src p') = l') (extract_prog (edges sg) os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply auto
  done

lemma filter_loc_extract_prof_consumes_diff_ports[simp]:
  "p \<noteq> p' \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog (edges sg) (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog (edges sg) os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply auto
  done

lemma zmset_map_filter_Src_extract_prog[simp]:
  "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p) = l') (extract_prog (edges sg) os))) = 
   zmset (map snd (filter (((=) (p :: 'p :: enum)) o fst) (inter (os nid)))) "
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (subst conj.commute)
  apply (simp flip: filter_filter)
  apply (subst sum_list_filter)
  using enum_class.enum_distinct apply (auto simp add: enum_class.enum_UNIV)
  done

lemma set_extract_prog_consumesD:
  "(l, t', m) \<in> set (extract_prog (edges sg) (os(nid := consumes (os nid) p t d))) \<Longrightarrow>
   (l, t', m) \<in> set (extract_prog (edges sg) os) \<or>
   (l = Loc nid (Trg p) \<and> t = t' \<and> m = -1) \<or>
   (\<exists> p' t''. t'' \<in> set (summar (os nid) p p') \<and> l = Loc nid (Src p') \<and> t' = t + t'' \<and> m = 1)"
  unfolding extract_prog_def obtain_progress_def consumes_def extract_progress_def add_caps_def
  apply (auto del: disjCI simp add: image_iff split_beta if_distrib enum_class.enum_UNIV split: prod.splits if_splits)
       apply (smt (verit, del_insts) image_iff split_pairs2)+
  done


lemma int_sum_minus_cases:
  "(0 :: int) < V \<Longrightarrow> V = n + m - p \<Longrightarrow> 0 \<le> p \<Longrightarrow> 0 < n \<or> 0 < m"
  by auto

lemma sum_list_pos_ex_elem_pos: "(0::int) < (\<Sum>m\<leftarrow>M. f m) \<Longrightarrow> \<exists>m\<in>set M. 0 < f m"
  by (smt (verit, ccfv_threshold) sum_list_0 sum_list_mono)

lemma zcount_sum_list:
  "zcount (\<Sum>m\<leftarrow>M. f m) t = (\<Sum>m\<leftarrow>M. zcount (f m) t)"
  apply (induct M)
   apply auto
  done


lemma length_filter_one:
  "(\<exists>! x \<in> set xs. P x) \<Longrightarrow>
   distinct xs \<Longrightarrow>
   length (filter P xs) = 1"
  by (induct xs)
    (auto simp add: filter_empty_conv)+

lemma data_in_channel_justifies_c_pts:
  "Trg_caps_inv caps chnls \<Longrightarrow>
   c_pts_inv (change_multiplicities su (extract_prog ed os) c) caps \<Longrightarrow> 
   t \<in> snd ` set (chnls (nid, p)) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (produ (os n)). m \<ge> 0) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (consu (os n)). m \<ge> 0) \<Longrightarrow>
   (\<forall> x. distinct (ed x)) \<Longrightarrow>
   zcount (c_pts c (Loc nid (Trg p))) t > 0 \<or> (\<exists> nid' p'. zcount (zmset (map snd ((filter ((=) p' o fst)) (produ (os nid'))))) t > 0 \<and> (nid, p) \<in> set (ed (nid', p')))"
  unfolding Trg_caps_inv_def
  apply (drule spec[of _ nid])
  apply (drule spec[of _ p])
  unfolding c_pts_inv_def
  apply (drule spec[of _ "Loc nid (Trg p)"])
  apply (simp add: c_pts_change_multiplicities)
  subgoal premises prems3
    using prems3(1,6) apply -
    unfolding extract_prog_def obtain_progress_def extract_progress_def
    apply (simp add:  BULK_BENQ_def zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
    apply (subst (asm) (1) monoid_add_class.sum_list_distinct_conv_sum_set)
     apply (simp_all add: enum_distinct enum_UNIV)
    apply (subst (asm) Groups.ab_group_add_class.ab_diff_conv_add_uminus)
    apply (subst (asm) comm_monoid_add_class.sum.distrib)
    apply (simp add: zmultiset_eq_iff)
    apply (drule spec[of _ t])+
    apply (simp add: zcount_sum)
    apply (subgoal_tac "zcount (to_zmset (map snd (chnls (nid, p)))) t > 0")
    subgoal
      apply (drule sym)
      apply simp
      apply (drule int_sum_minus_cases[where n="zcount (c_pts c (Loc nid (Trg p))) t" and m="(\<Sum>x\<in>UNIV. zcount (\<Sum>xa\<leftarrow>produ (os x). zmset (map (\<lambda>x. snd xa) (filter (\<lambda>x. nid = fst x \<and> p = snd x) (ed (x, fst xa))))) t)" and p="zcount (zmset (map snd (filter (\<lambda>x. p = fst x) (consu (os nid))))) t"])
        apply linarith
       apply (rule zcount_zmset_ge_0I)
       apply simp
      using prems3(3) apply blast
      apply (elim disjE)
       apply simp
      apply (rule disjI2)
      apply (drule sum_pos_ex_elem_pos)
      apply (clarsimp simp add: zcount_sum_list)
      apply (drule sum_list_pos_ex_elem_pos)
      apply clarsimp
      subgoal for _ nid' p' x m
        apply (rule exI[of _ nid'])
        apply (rule exI[of _ p'])
        apply (auto simp add: map_filter_map_filter)
         apply (rule zcount_zmset_gt_0I)
           apply (auto simp flip: map_filter_map_filter)
        using prems3(2) apply auto[1]
         apply (rule image_eqI[rotated])
          apply clarsimp
          apply fastforce
         apply (auto simp add: map_replicate_const)
          apply (smt (verit, del_insts) zcount_empty zcount_update_zmultiset)
        subgoal
          apply (cases "(nid, p) \<in> set (ed (nid', p'))")
          subgoal
            using prems3(4) apply -
            apply (subst length_filter_one)
              apply (rule ex1I[of _ "(nid, p)"])
               apply simp_all
            apply (auto simp add: zcount_update_zmultiset)
            done
          subgoal
            using prems3(4) apply -
            apply (clarsimp simp add: zcount_update_zmultiset)
            apply (smt (verit, ccfv_SIG) filter_False length_nth_simps(1) semiring_1_class.of_nat_simps(1) surjective_pairing zero_compare_simps(6))
            done
          done
        subgoal
          apply (clarsimp simp add: zcount_update_zmultiset)
          apply (smt (verit, ccfv_SIG) filter_False length_nth_simps(1) semiring_1_class.of_nat_simps(1) surjective_pairing zero_compare_simps(6))
          done
        done
      done
    subgoal
      apply (auto simp add: zcount_to_zmset)
      apply (metis Nat.add_0_right add_diff_inverse_nat count_list_0_iff diff_0_eq_0 list.set_map prems3(1))
      done
    done
  done

lemma
  "dataflow_topology su (-+-) \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c (Loc nid (Trg p))) t \<Longrightarrow>
   ifrontier su (-+-) (change_multiplicities su (filter (\<lambda>(la, t, d). l = la) (extract_prog ed (os(nid := consumes (os nid) p t d)))) c) l' =
   ifrontier su (-+-) (change_multiplicities su (filter (\<lambda>(la, t, d). l = la) (extract_prog ed os)) c) l'"
  apply (rule ifrontier_eq_all_le)
   apply simp_all
  apply auto
  subgoal for l' t'
    apply (clarsimp simp add:  c_pts_change_multiplicities split_beta extract_prog_def zmset_concat map_concat filter_concat comp_def filter_map split: prod.splits)
    apply (subst (1 2) conj.commute)
    apply (simp flip: filter_filter)
    apply (subst (1 2) Groups_List.monoid_add_class.sum_list_distinct_conv_sum_set)
     apply (simp add: Enum.enum_class.enum_distinct)
    apply (simp add: Enum.enum_class.enum_UNIV)
    apply (simp add:   extract_progress_def obtain_progress_def   split_beta extract_prog_def zmset_concat map_concat filter_concat comp_def filter_map)
    apply (simp add:  Groups_Big.comm_monoid_add_class.sum.distrib Groups_Big.sum_subtractf)
    apply (simp cong: if_cong add: if_distrib[where f="inter"] if_distrib[where f="produ"] if_distrib[where f="consu"])
    apply (simp add: sum_list_zmset zmset_concat)
    oops

(* 
  apply (clarsimp simp add: extract_prog_def extract_progress_def consumes_def c_pts_change_multiplicities split_beta Propagate.dataflow_topology.implied_frontier_alt_def)
 *)

lemma filter_extract_prog_diff_nid:
  "node l \<noteq> nid \<Longrightarrow>
   filter (\<lambda>(la, t, d). l = la) (extract_prog ed (os(nid := consumes (os nid) p t d))) = 
   filter (\<lambda>(la, t, d). l = la) (extract_prog ed os)"
  unfolding extract_prog_def extract_progress_def 
  apply (simp add: filter_concat map_concat comp_def if_distrib filter_map)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply (auto 0 0 split: prod.splits)
  subgoal
    unfolding obtain_progress_def
    apply (simp add: filter_empty_conv enum_class.enum_UNIV split_beta filter_concat comp_def)
    apply (clarsimp simp add: filter_map comp_def split: prod.splits)
    apply (auto simp add: filter_map filter_empty_conv enum_class.enum_UNIV split_beta filter_concat comp_def split: prod.splits)
    done
  subgoal
    unfolding obtain_progress_def
    apply (simp add: filter_empty_conv enum_class.enum_UNIV split_beta filter_concat comp_def)
    apply (clarsimp simp add: filter_map comp_def split: prod.splits)
    done
  done

lemma ifrontier_change_multiplicities_no_path:
  "graph.path_weight su l l' = {}\<^sub>A \<Longrightarrow>
   dataflow_topology su (-+-) \<Longrightarrow>
   ifrontier su (-+-) (change_multiplicities (summ sg) (filter (\<lambda>(la, t, d). l = la) (extract_prog ed os)) c) l'=
   ifrontier su (-+-) c l'"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (simp add: c_pts_change_multiplicities filter_empty_conv enum_class.enum_UNIV split_beta filter_concat comp_def)
  apply (rule frontier_sum_eq)
     apply simp_all
    defer
    apply (metis (lifting) ext dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
   apply (metis (lifting) ext dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
  apply safe
  subgoal
    apply (rule frontier_sum_eq)
       apply simp_all
    apply auto
    apply (subst filter_False)
     apply auto
    done
  subgoal
    apply (rule frontier_sum_eq)
       apply simp_all
    apply auto
    apply (subst filter_False)
     apply auto
    done
  done

lemma c_pts_change_multiplicities_filter_False[simp]:
  "l \<noteq> l' \<Longrightarrow>
   c_pts (change_multiplicities (summ sg) (filter (\<lambda>(la, t, d). l = la) xs) c) l' = c_pts c l'"
  apply (simp add: c_pts_change_multiplicities filter_empty_conv split_beta )
  apply (subst filter_False)
   apply auto
  done

lemma ifrontier_change_multiplicities_filter:
  "dataflow_topology su (-+-) \<Longrightarrow>
   ifrontier su (-+-) (change_multiplicities su (filter (\<lambda>(la, t, d). l = la) xs) c) l' =
   ifrontier su (-+-) (c\<lparr> c_pts := (c_pts c)(l := c_pts c l + zmset (map snd (filter (\<lambda>(la, t, d). l = la) xs))) \<rparr>) l'"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (simp add: c_pts_change_multiplicities filter_empty_conv split_beta )
  apply (rule frontier_sum_eq)
     apply simp_all
    defer
    apply (metis (lifting) ext dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
   apply (simp add: sum_nonneg zcount_sum) 
  apply safe
  subgoal
    apply (rule frontier_sum_eq)
       apply (simp_all add: split_def split_beta split: prod.splits)
    done
  subgoal
    apply (rule frontier_sum_eq)
       apply (simp_all add: split_def split_beta split: prod.splits)
    apply (subst filter_False)
     apply auto
    done
  done

lemma aux:
  "0 \<le> (a :: int) + (c - b) \<Longrightarrow>
   0 < b \<Longrightarrow>
   0 < a \<or> 0 < c"
  by auto

lemma zcount_zmset:
  "zcount (zmset xs) t = sum_list (map snd (filter (\<lambda> (t', x). t = t') xs))"
  by (induct xs) (auto simp add: zcount_update_zmultiset)


lemma sum_gt_0I:
  "xs \<noteq> [] \<Longrightarrow>
   (\<forall> x \<in> set xs. 0 < x) \<Longrightarrow>
   (0 :: int) < sum_list xs"
  apply (induct xs)
   apply auto
  subgoal for a xs
    apply (cases xs)
     apply auto
    done
  done


lemma zcount_zmset_gt0I:
  "\<exists> m. (p, t, m) \<in> set xs \<Longrightarrow>
   \<forall>x\<in>set xs. 0 < snd (snd x) \<Longrightarrow>
  0 < zcount (zmset (map snd (filter (\<lambda>x. p = fst x) xs))) t"
  unfolding zcount_zmset filter_map comp_def
  apply (simp add: split_beta)
  apply (rule sum_gt_0I)
   apply (force simp add: filter_empty_conv)+
  done                

lemma zcount_sum_list_alt:
  "zcount (sum_list xs) t = sum_list (map (\<lambda> x. zcount x t) xs)"
  by (induct xs)
    auto

lemma zcount_zmset_const_diff_0I:
  "t \<noteq> t' \<Longrightarrow>
   zcount (zmset (map (\<lambda>x. (t', c)) xs)) t = 0"
  by (induct xs)
   (auto simp add: zcount_update_zmultiset)


lemma in_extract_prog_cases:
  "Trg_caps_inv caps buf \<Longrightarrow>
   Src_caps_inv caps os \<Longrightarrow>
   c_pts_inv (change_multiplicities su (extract_prog ed os) c) caps \<Longrightarrow>
   (l, t, m) \<in> set (extract_prog ed os) \<Longrightarrow>
   (\<forall> nid. \<forall> (p, t, m) \<in> set (consu (os nid)). 0 < m) \<Longrightarrow>
   (\<forall> nid. \<forall> (p, t, m) \<in> set (produ (os nid)). 0 < m) \<Longrightarrow>
   (\<forall> nid. \<forall> (p, t, m) \<in> set (inter (os nid)). 0 \<noteq> m) \<Longrightarrow>
   (\<exists> nid p m'. (p, t, m') \<in> set (consu (os nid)) \<and> m = -m' \<and> l = Loc nid (Trg p) \<and> (zcount (c_pts c l) t > 0 \<or> (\<exists> nid' p' m'. (nid, p) \<in> set (ed (nid', p')) \<and> (p', t, m') \<in> set (produ (os nid'))))) \<or>
   (\<exists> nid p . C2 \<and> l = Loc nid (Src p) \<and> (p, t, m) \<in> set (inter (os nid))) \<or>
   (\<exists> nid p m. C3 \<and> (p, t, m) \<in> set (produ (os nid)) \<and> l = Loc nid (Trg p) \<and> zcount (c_pts c l) t > 0 \<or> (\<exists> nid' p' a. (nid, p) \<in> set (ed (nid', p')) \<and> a \<in> set (produ (os nid'))))"
  apply (subst (asm) (2) extract_prog_def)
  apply (auto del: disjCI simp add: image_iff enum_class.enum_UNIV extract_progress_def split_beta obtain_progress_def)
  subgoal for nid p m'
    unfolding Trg_caps_inv_def c_pts_inv_def
    apply (drule spec[of _ l])
    apply (drule spec[of _ nid])
    apply (drule spec[of _ p])
    apply (simp add: c_pts_change_multiplicities extract_prog_def extract_progress_def zmset_concat map_concat filter_concat comp_def filter_map split_beta obtain_progress_def)
    apply (subst (asm) (1) monoid_add_class.sum_list_distinct_conv_sum_set)
     apply (simp_all add:  comm_monoid_add_class.sum.distrib enum_class.enum_distinct enum_class.enum_UNIV)
    apply (subst (asm) Groups.ab_group_add_class.ab_diff_conv_add_uminus)
    apply (subst (asm) comm_monoid_add_class.sum.distrib)
    apply simp
    apply (subgoal_tac "zcount (c_pts c (Loc nid (Trg p)) +
   ((\<Sum>x\<in>UNIV. \<Sum>xa\<leftarrow>produ (os x). zmset (map (\<lambda>x. snd xa) (filter (\<lambda>x. nid = fst x \<and> p = snd x) (ed (x, fst xa))))) - zmset (map snd (filter (\<lambda>x. p = fst x) (consu (os nid)))))) t \<ge> 0")
    subgoal premises prems
      using prems(2,5,10) apply -
      apply clarsimp
      apply (subgoal_tac "0 < zcount (c_pts c (Loc nid (Trg p))) t \<or> 0 < zcount (\<Sum>x\<in>UNIV. \<Sum>xa\<leftarrow>produ (os x). zmset (map (\<lambda>x. snd xa) (filter (\<lambda>x. nid = fst x \<and> p = snd x) (ed (x, fst xa))))) t")
       defer
      subgoal
        apply (rule aux)
         apply simp_all
        apply (drule spec[of _ nid])
        apply (rule zcount_zmset_gt0I)
         apply auto[1]
        apply assumption
        done
      subgoal
        apply (elim disjE)
        subgoal
          by auto
        subgoal
          apply (simp add: zcount_sum)
          apply (drule sum_pos_ex_elem_pos)
          apply clarsimp
          subgoal for nid'
            apply (clarsimp simp add: sum_list_zmset zmset_concat )
            unfolding comp_def zcount_sum_list_alt 
            apply (clarsimp simp add: zcount_sum_list_alt comp_def sum_list_zmset zmset_concat )
            apply (drule sum_list_pos_ex_elem_pos)
            apply clarsimp
            subgoal for p' t' c
              apply (rule exI[of _ nid'])
              apply (rule exI[of _ p'])
              apply (intro conjI)
              apply (smt (verit) List.empty_filter_conv list.simps(8) surjective_pairing zcount_empty zmset.simps(1))+
                done
              done
            done
          done
        done
    subgoal
      by (simp add: to_zmset_nenneg)
    done
  subgoal
    sorry
  subgoal
    sorry
  done



lemma
  "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   cbufs (nid, p) = (d, t) # xs \<Longrightarrow>
   dataflow_topology (summ sg) (-+-) \<Longrightarrow>
   dataplane_tracker_inv (os(nid := consumes (os nid) p (t :: 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) d)) (BTL (nid, p) cbufs) sg"
  unfolding dataplane_tracker_inv_def
  apply (elim conjE exE)
  apply simp
  apply hypsubst_thin
  subgoal for c c' cgs chns caps
    apply (rule exI[of _ 
          "(\<lambda> l. case l of 
        Loc nid' (Src p') \<Rightarrow> if nid' = nid then caps l + to_zmset (map (\<lambda> t'. t + t') (summar (os nid) p p')) else caps l 
     | Loc nid' (Trg p') \<Rightarrow> if nid' = nid \<and> p = p' then caps l - {# t #}\<^sub>z else caps l)"])
    apply (intro conjI)
    subgoal premises prems
      using prems(3) apply -
      unfolding Src_caps_inv_def consumes_def add_caps_def to_zmset_correct
      apply (auto 0 0 simp add: filter_empty_conv)
      apply (auto 0 0 simp add:  comp_def  simp flip:  to_zmset_correct)
      subgoal premises prems2 for p''
        apply (simp flip: Multiset.mset_filter mset_map add: map_concat filter_concat comp_def)        
        apply (rule arg_cong[where f=mset])
        apply (subst concat_map_time_filter_out)
        using enum_class.enum_distinct apply (auto simp add: enum_class.enum_UNIV)
        done
      done
    subgoal premises prems
      using prems(1,4) apply -
      unfolding Trg_caps_inv_def
      apply (auto simp add: map_tl BHD_def BTL_def BULK_BENQ_def)
      done
    subgoal premises prems
      using prems(5) apply -       
      unfolding c_pts_inv_def
      apply (auto 0 0 split: location.splits port.splits simp add: c_pts_change_multiplicities)
      subgoal
        apply (subgoal_tac
            "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog (edges sg) (os(nid := consumes (os nid) p t d))))) =
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog (edges sg) os))) - {#t#}\<^sub>z")
        subgoal
          by auto
        subgoal premises
          apply (auto cong: if_cong simp add: if_distrib zmset_map_filter_Trg_extract_prog comp_def)
          apply (rule arg_cong2[where f=minus])
          apply (simp_all add: update_zmultiset_singleton(2))
          apply metis
          done
        done
      subgoal for nid'
        apply (drule spec[of _ "Loc nid (Src nid')"])
        apply (drule sym)
        apply simp
        subgoal premises
          apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
          apply (subst sum_list_filter)
          using enum_class.enum_distinct apply (auto simp add: enum_class.enum_UNIV)
          done
        done
      subgoal for nid' p'
        apply (clarsimp cong: if_cong simp add: if_distrib  comp_def)
        apply (metis (no_types, lifting) ext comp_apply zmset_map_filter_Src_extract_prog)
        done
      done
    subgoal premises prems
      using prems(6) unfolding front_inv_def by auto
    subgoal premises prems
      using prems(1,8) apply -
      unfolding chnls_imp_front_inv_def
      apply (simp_all add: BHD_def BTL_def BULK_BENQ_def)
      done
    subgoal premises prems
      using prems(9) apply -
      unfolding changes_non_zero_inv_def extract_prog_def consumes_def obtain_progress_def extract_progress_def
      apply (clarsimp simp add: enum_class.enum_UNIV split_beta split: prod.splits)
      apply force
      done
    subgoal premises prems
      using prems(11) apply -
      unfolding changes_above_impl_inv_def
      apply (clarsimp simp add: c_pts_change_multiplicities split: prod.splits)
      apply (intro conjI impI allI ballI; clarsimp)
      subgoal for l t' m
        apply (drule set_extract_prog_consumesD)
        apply (elim disjE exE conjE)
        subgoal
          by blast
        subgoal
          using prems(1,8) apply -
          apply hypsubst_thin
          unfolding chnls_imp_front_inv_def
          apply (drule spec[of _ nid])
          apply (drule spec[of _ p])
          apply (drule bspec[of _ _ t'])
          subgoal
            unfolding BULK_BENQ_def
            by simp
          subgoal
            by blast
          done
        subgoal premises prems2 for p' t''
          using prems(4,5) apply -
          apply (drule data_in_channel_justifies_c_pts[where t=t and p=p and nid=nid])
          apply assumption
          using prems(1) apply -
          unfolding BULK_BENQ_def
          apply clarsimp
          subgoal sorry
          subgoal sorry
          subgoal sorry
          apply (elim disjE)
          subgoal
            using prems2(4,5) apply hypsubst_thin
            apply (rule frontier_less_equal_ifrontierI[where l="Loc nid (Trg p)"])
            using prems(2) apply blast
            subgoal sorry
            subgoal
              using frontier_less_equal_zcount_pos by blast
            done
          subgoal
            apply clarsimp
            subgoal for nid' p''
              using prems(11) apply -
              unfolding changes_above_impl_inv_def
              apply clarsimp
              apply (drule gt_0_zcount_msetD)
              apply clarsimp
              subgoal for m
                apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m)"])
                subgoal premises premm
                  unfolding extract_prog_def extract_progress_def obtain_progress_def
                  apply (clarsimp simp add: enum_class.enum_UNIV split_beta c_pts_change_multiplicities split: prod.splits)
                  apply (rule exI[of _ nid'])
                  apply (intro disjI2)
                  using premm(3,4,5) apply -
                  apply (rule bexI[of _ "(p'', t, m)"])
                  apply (rule image_eqI[rotated])
                  apply auto
                  done
                subgoal
                  apply simp
                  using prems2(4,5) apply hypsubst_thin
                  apply (rule frontier_less_equal_ifrontier_trans[of _ _ "Loc nid (Trg p)"])          
                  subgoal sorry
                  subgoal sorry
                  apply assumption
                  done
                done
              done
            done
          done
        done
      subgoal for l t' m l' t'' m'
        apply (drule set_extract_prog_consumesD)
        apply (elim disjE exE conjE)
        subgoal
          apply (drule set_extract_prog_consumesD)
          apply (elim disjE exE conjE)
          subgoal
            apply (cases "graph.path_weight (summ sg) l l' = {}\<^sub>A")
            subgoal
            apply (drule bspec[of _ _ "(l', t'', m')"])
             apply assumption
            apply clarsimp
            apply (drule bspec[of _ _ "(l, t', m)"])
             apply assumption
            apply simp
            apply (drule spec)+
            apply (drule mp)
            apply force
            using prems(1,8) apply -
            unfolding chnls_imp_front_inv_def
            apply (drule spec[of _ nid])
            apply (drule spec[of _ p])
            apply clarsimp
            apply (drule bspec[of _ _ "(_, t)"])
            apply (auto simp add: BULK_BENQ_def)[1]
            apply simp
              apply (subst ifrontier_change_multiplicities_no_path)
              apply assumption
              subgoal
                using prems(2) by force
              apply (subst (asm) ifrontier_change_multiplicities_no_path)
              apply assumption
              subgoal
                using prems(2) by force
              apply assumption
              done
            apply (cases "l = Loc nid (Trg p)")
            subgoal
              apply hypsubst
              apply (drule bspec[of _ _ "(l', t'', m')"])
               apply assumption
              apply simp
              apply (drule bspec[of _ _ "(Loc nid (Trg p), t', m)"])
               apply assumption
              apply simp
              apply (drule spec[of _ "l'"])
              apply (drule spec[of _ "t''"])
              apply simp
              apply (drule mp)
               apply blast
              apply (drule frontier_less_equal_ifrontierE)
              subgoal
                using prems(2) by force
              apply clarsimp
              subgoal for l3 s t3
              apply (drule frontier_less_equal_ifrontierE)
              subgoal
                using prems(2) by force
              apply clarsimp
              subgoal for l4 s' t4
                apply (cases "l4 = l3 \<and> l4 = Loc nid (Trg p)")
                subgoal
                  apply clarsimp
                  apply hypsubst_thin
                  apply (subst (asm) (1 2) frontier_less_equal_iff2)
                  apply clarsimp
                  subgoal for t5 t6
                    apply (cases "t5 = t6 \<and> t5 = t")
                    subgoal
                      apply clarsimp
                      apply hypsubst_thin
                      using prems(1)

                  find_theorems t

                  apply hypsubst


end
              apply (drule in_extract_prog_cases[OF prems(4) prems(3) prems(5), where t=t''])
              subgoal sorry
              subgoal sorry
              subgoal sorry
              apply (elim disjE conjE exE)
              subgoal
                sorry
              subgoal for nid p'' ma nid' p' m''
                apply hypsubst
                apply (drule bspec[of _ _ "(l', t'', -ma)"])
                subgoal premises prems2
                  using prems2(5) apply -
                  unfolding extract_prog_def extract_progress_def obtain_progress_def
                  apply (auto simp add:  image_iff split_beta)
                  apply (rule bexI[of _ nid])
                   apply (rule disjI1)
                   apply (rule bexI[rotated])
                    apply assumption
                  apply simp
                  using prems2(9,6) apply -
                   apply (simp_all add: enum_class.enum_UNIV)
                  done
                apply simp
                  apply (cases "l = Loc nid' (Src p')")
                  subgoal
                    apply hypsubst_thin
                    apply simp
                    sorry
                  subgoal
                apply (drule bspec[of _ _ "(l, t', m)"])
                 apply assumption
                  apply (drule spec[of _ "Loc nid' (Src p')"])
                  apply simp
                apply (drule spec[of _ "t''"])
                apply (drule mp)
                subgoal premises prems2
                  using prems2(4) apply -
                  unfolding extract_prog_def extract_progress_def obtain_progress_def
                  apply (auto simp add:enum_class.enum_UNIV image_iff split_beta)
                  sorry
                subgoal
                  find_theorems l

                  apply simp

                  find_theorems enum_class.enum set

end
                  apply (rule exI)
                  apply (rule bexI[of _ nid])
                   apply (rule disjI1)
                  apply simp
                   apply (rule bexI[rotated])
                    apply assumption
                  apply simp
                  using prems2(8) apply -
                  apply (simp_all add: enum_class.enum_UNIV)
                  done
                apply simp

                  find_theorems set enum_class.enum


end
             apply assumption
            apply clarsimp
   



end

              apply (subst (asm) (2) extract_prog_def)
              apply (auto 0 0 simp add: image_iff enum_class.enum_UNIV extract_progress_def split_beta obtain_progress_def)
              subgoal for l' p' m''
                apply hypsubst_thin

                sorry
              subgoal for nid'' p''
                apply hypsubst_thin
                sorry
              subgoal for nid1 p1 nid2 p2
                apply hypsubst_thin

end
                find_theorems os

                using prems(4,5) apply -
                unfolding c_pts_inv_def apply -
                apply (drule spec[of _ "Loc l' (Trg p')"])
                apply (subst (asm) (3) extract_prog_def)
                apply (simp add: c_pts_change_multiplicities)
                apply (auto 0 0 simp add: zmset_concat map_concat filter_concat comp_def filter_map image_iff enum_class.enum_UNIV extract_progress_def split_beta obtain_progress_def)
                unfolding Trg_caps_inv_def
                apply (drule spec[of _ l'])
                apply (drule spec[of _ p'])
                apply simp
                apply hypsubst_thin


                find_theorems caps

end

  apply (drule frontier_less_equal_ifrontierE[where t=t''])
  subgoal
    using prems(2) by force
  apply clarsimp
  subgoal for l'' s t''
    apply hypsubst_thin
    apply (cases "l'' = l'")
    subgoal
      apply clarsimp
      apply (rule frontier_less_equal_trans)
      apply (rule frontier_less_equal_ifrontierI[of _ s, simplified])
      subgoal
        using prems(2) by force
      apply assumption
      apply auto
      done
    subgoal 
      apply (drule frontier_less_equal_ifrontierE[where t=t])
      subgoal
        using prems(2) by force
      apply clarsimp
      subgoal for l''' s' t
        apply hypsubst_thin
        apply (cases "l'' = l'''")
        subgoal
          apply hypsubst_thin
          apply (cases "l''' = l")
          subgoal
            apply hypsubst_thin
            apply (subgoal_tac "s' = 0")
            subgoal
              apply simp
              apply hypsubst_thin
              apply (cases "l = Loc nid (Trg p)")
              subgoal
                apply hypsubst_thin
                apply simp


                oops
                apply (subst ifrontier_change_multiplicities_filter)
                subgoal
                  using prems(2) by force
                apply simp

                find_theorems zmset extract_prog



                apply (rule frontier_less_equal_trans)
                apply (rule frontier_less_equal_ifrontierI[of _ s, simplified])
                apply simp_all
                subgoal
                  using prems(2) by force
                defer
                apply blast
                apply (subst c_pts_change_multiplicities_filter_False)



                find_theorems 0  graph.path_weight dataflow_topology


                find_theorems name: no_zero_cycle

end
  sorry
  subgoal
    apply (subst filter_extract_prog_diff_nid)
    apply simp_all
    done
  done



end

  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (clarsimp cong: if_cong simp add: if_distrib[where f="filter _"] if_distrib[where f="map _"] split_beta filter_concat zmset_concat map_concat comp_def if_distrib[where f="inter"] if_distrib[where f="produ"] if_distrib[where f="consu"])
  apply (intro impI conjI)
  subgoal

    thm if_distrib[where f="filter _"]

    find_theorems "map _ (if _ then _ else _)"
    find_theorems cbufs

    find_theorems chnls_imp_front_inv


    oops

end
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
    \<open>edges sg = graph_to_edges (summ sg)\<close>
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
          apply (simp add: SIM1)
          apply (simp add: SIM1)
          subgoal
            using SIM1
            unfolding ty1_check_def
            by (auto simp add:  Src_from_Trg_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1
            unfolding ty2_check_def
            by (auto simp add:  Src_from_Trg_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
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
          subgoal
            using SIM1
            unfolding ty1_check_def
            by (auto simp add: BTL_def BHD_def  Src_from_Trg_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
          subgoal
            using SIM1(4,6,7)
            unfolding ty2_check_def
            apply (clarsimp simp add: operator_state.defs fun_upd_def BTL_def BHD_def Src_from_Trg_def consumes_def add_caps_def BENQ_def my_summ_def BULK_BENQ_def outputs_at_target_def split: prod.splits)
            apply (meson UnCI img_fst in_fst_imageE list.set_sel(2))
            done
          subgoal premises
            using SIM1(8) apply -
            unfolding dataplane_tracker_inv_def apply auto


            find_theorems dataplane_tracker_inv


end

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
