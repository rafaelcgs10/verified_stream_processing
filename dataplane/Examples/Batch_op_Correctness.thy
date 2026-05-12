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
   front = (\<lambda> _. frontier {#\<bottom>#}\<^sub>z),
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


value [GHC] "check_prefix 5500 [((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1)),((1, 1), (Inr 3, MyPair 1 0))] test_op"
  (* value [GHC] "check_prefix 5500 [((1, 1), (Inr 7, MyPair 0 1)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 3, MyPair 1 0))] test_op"
value [GHC] "check_prefix 5500 [((1, 1), (Inr 3, MyPair 1 0)), ((1, 1), (Inr 10, MyPair 1 1)), ((1, 1), (Inr 7, MyPair 0 1))] test_op"  *)

value [GHC] "ltaken 3 (lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op))"

term DEBUG


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

lemma filter_filter_True1_pair:
  "(\<forall> (x, y) \<in> set xs. Q y) \<Longrightarrow>
   filter (\<lambda>(x, y). Q y \<and> P y) xs = filter (P o snd) xs"
  by (smt (verit) filter_cong split_def trimono_spec_defs(3))
lemma filter_filter_pair_alt:
  "filter (\<lambda>(x, y). Q y \<and> P y) xs = filter (\<lambda> (x, y). P y) (filter (Q o snd) xs)"
  by (simp add: split_def)

lemma filter_snd:
  "filter (\<lambda>(x, y). P y) xs = filter (P o snd) xs"
  by (metis fn_snd_conv trimono_spec_defs(3))
lemma filter_snd_alt:
  "filter (\<lambda>x. P (snd x)) xs = filter (P o snd) xs"
  by (metis trimono_spec_defs(3))
lemma filter_snd_alt2:
  "map snd (filter (\<lambda>x. P (snd x)) xs) = filter P (map snd xs)"
  by (simp add: filter_map filter_snd_alt)
lemma projl_fst:
  "(\<lambda>x. projl (fst x)) = fst o (\<lambda> (x, t). (projl x, t))"
  by auto

lemma map_fst_filter_snd:
  "map (\<lambda>(x, y). (f x, y)) (filter (\<lambda>x. P (snd x)) xs) = filter (\<lambda>x. P (snd x)) (map (\<lambda>(x, y). (f x, y)) xs)"
  by (induct xs)
    auto
lemma find_None_if:
  "(\<forall> x\<in>set xs. \<not> P x) \<Longrightarrow>
   find P xs = None"
  by (metis find_None_iff2)
lemma image_zmset_empty_if:
  "M = {#}\<^sub>z \<Longrightarrow>
   image_zmset f M = {#}\<^sub>z"
  by simp
lemma zmset_of_empty_if:
  "M = {#} \<Longrightarrow>
   zmset_of M = {#}\<^sub>z"
  by simp
lemma mset_set_empty_if:
  "M = {} \<Longrightarrow>
   mset_set M = {#}"
  by simp
lemma set_antichain_empty_if:
  "M = {}\<^sub>A \<Longrightarrow>
   set_antichain M = {}"
  by simp
lemma frontier_empty_if:
  "M = {#}\<^sub>z \<Longrightarrow>
   frontier M = {}\<^sub>A"
  by simp


(* FIXME: move me *)
lemma change_multiplicities_extract_progress_append:
  "change_multiplicities su (extract_progress nid nt \<lparr>cons = C1 @ C2,  inte = I1 @ I2, prod = P1 @ P2 \<rparr>) c =
   change_multiplicities su (extract_progress nid nt \<lparr>cons = C2,  inte = I2, prod = P2 \<rparr>) (change_multiplicities su (extract_progress nid nt \<lparr>cons = C1,  inte = I1, prod = P1 \<rparr>) c)"
  unfolding extract_progress_def
  apply simp
  apply (smt (verit, del_insts) change_multiplicities_append change_multiplicities_comm)
  done
lemma c_pts_change_multiplicities_append:
  "c_pts (change_multiplicities su (xs @ ys) c) l = (c_pts (change_multiplicities su xs c) l) + (c_pts (change_multiplicities su ys c) l) - c_pts c l"
  by (simp add: c_pts_change_multiplicities)
lemma zmset_Data_to_zmset:
  "(\<forall>x\<in>set xs. is_Data x) \<Longrightarrow>
   zmset (map (\<lambda>x. snd (case x of Data t d \<Rightarrow> (p, t, 1))) xs) = to_zmset (map (\<lambda>x. snd (case x of Data t d \<Rightarrow> (Inl d, t))) xs)" 
  apply (induct xs)
   apply (clarsimp split: event.splits prod.splits)+
  using update_zmultiset_one(2) apply fastforce
  done


(* FIXME: move me *)
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


(* FIXME: move me *)
lemma path_weight_end_of_road:
  assumes G: "Graph.graph su"
  shows  "s \<in>\<^sub>A graph.path_weight su loc1 loc2 \<Longrightarrow> loc2 \<noteq> loc1 \<Longrightarrow>
   (\<forall> loc2. loc2 \<noteq> loc1 \<longrightarrow> su loc1 loc2 = {}\<^sub>A) \<Longrightarrow>
   False"
  apply (drule graph.path_weight_conv_path[OF G])
  apply clarsimp
  subgoal premises prems for xs
    using prems(3,2,1) apply -
    apply (induct xs arbitrary: loc2 rule: rev_induct)
    subgoal
      apply (erule graph.path.cases[OF G])
       apply (auto simp add: )
      done
    subgoal
      apply (erule graph.path.cases[OF G])
       apply (clarsimp simp add: split: if_splits)+
      apply force
      done
    done
  done

(* FIXME: move me *)
lemma frontier_zmset_of_add_minus:
  "frontier (zmset_of (A + B - C)) = frontier (zmset_of A + zmset_of B - zmset_of C)"
  apply transfer
  apply (auto simp add: minimal_antichain_def)
  done

lemma zmset_map_Drop_Mint:
  "(\<forall> x\<in>set xs. \<not> is_Data x) \<Longrightarrow>
   zmset (map (\<lambda>x. snd (case x of Drop t \<Rightarrow> (p, t, - 1) | Mint t \<Rightarrow> (p, t, 1))) xs) =
   zmset_of (event.time `# filter_mset is_Mint (mset xs)) - zmset_of (event.time `# filter_mset is_Drop (mset xs))"
  apply (induct xs)
   apply (auto simp add: zmset_of_plus split: event.splits)
   apply (metis (no_types, lifting) add_zmset_add_single diff_diff_add update_zmultiset_one(1))
  using update_zmultiset_one(2) apply fastforce
  done

(* FIXME: move me *)
thm set_extract_progress_consumesD
lemma set_extract_progressD:
  "(l, t, m) \<in> set (extract_progress nid ed st') \<Longrightarrow>
   st' = st\<lparr> cons := consu os @ xs, inte := inter os @ ys, prod := produ os @ zs \<rparr> \<Longrightarrow>
   (l, t, m) \<in> set (extract_progress nid ed (snd (obtain_progress os))) \<or>
   (\<exists>m' p. l = Loc nid (Trg p) \<and> m = - m' \<and> (p, t, m') \<in> set xs) \<or>
   (\<exists>m' p s. l = Loc nid (Src p) \<and> (p, t, m) \<in> set ys) \<or>
   (\<exists> p' p nid'. l = Loc nid' (Trg p') \<and> ed (nid, p) = Some (nid', p') \<and> (p, t, m) \<in> set zs)"
  unfolding extract_progress_def obtain_progress_def
  apply (auto  simp add: split_beta image_iff Misc.set_map_filter split: option.splits)
  subgoal
    by force
  subgoal
    by force
  subgoal
    by (metis fst_conv option.distinct(1) option.simps(1) snd_conv)
  subgoal
    by (metis fst_conv option.distinct(1) option.simps(1) snd_conv)
  done


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
    OP_EXTRA_INVS:
    \<open>input (os 0) = (\<lambda> _. [])\<close>
    \<open>initia (os 0)\<close>
    \<open>input_ocaps_inv (os 1)\<close>
    \<open>cbufs (0, 0) = []\<close>
  shows 
    \<open>set_op S D (dataflow_op sg (G_op f ip_state bt_state cbufs)) \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms(1-12,13,15,16,17,18) apply -
proof (coinduction arbitrary: os sg ip_state bt_state chns cbufs inps SP SO S D raw_s rule: weakBisimWeakUptoBisimCong)
  case SIM1
  show ?case (is "wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2")
  proof -
    define R where "R = ?R"
    show ?thesis 
      sorry
      (* apply -
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
          apply (intro exI conjI relcomppI impI)
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
          apply (rule exI[of _ "sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 0 (subgraph.nxt sg) st) (pt_tr sg)\<rparr>"])
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
              using assms(14) by force
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
              using SIM1(17) apply -
              unfolding consumes_def add_caps_def BENQ_def input_ocaps_inv_def BHD_def BTL_def
              apply clarsimp
              done
            done
          done
        done
      done *)
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
                                      apply (drule set_latenD)
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
                                      apply (drule set_latenD)
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
                                      apply (drule set_latenD)
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
                                      apply (drule set_latenD)
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
                                    apply (drule set_latenD)
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
                              subgoal premises temp3
                                using TIMESTAMP_COMPARE by simp
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
                              subgoal
                                using TIMESTAMP_COMPARE by assumption
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
                                                apply (simp add: c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
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
                                                    by (simp add:SIM2(17)[simplified]  c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
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
                                          by (simp add: extract_progress_def c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
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
                                            apply (clarsimp simp add: frontier_zmset_of_add_minus zmset_of_plus extract_progress_def c_pts_change_multiplicities comp_def List.map_filter_def split_beta split: event.splits prod.splits)
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
                                        apply (rule arg_cong[where f="rmdups {}"])
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
                                          1 := (os 1)\<lparr> ocaps := _, input := _, outpu := (outpu (os 1))(1 := []), consu := [], inter := [], produ := [], front := frontier \<circ> (\<lambda>p. c_imp c (Loc 1 (Trg 1))), initia := True \<rparr>)"])
                                apply (rule exI[of _ "sg\<lparr>pt_tr := c, upfro := (\<lambda>_. True)(1 := False)\<rparr>"])
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
                                using [[goals_limit = 1]]
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
                                             apply (simp add: fold_consumes)
                                apply (rule operator_state_eqI)
                                subgoal
                                  sorry
                                subgoal
                                  sorry
                                subgoal
                                  apply (simp add: SIM2(1,2,3,4,5)  operator_state.defs flip: filter_append map_append)


                                  find_theorems operator_state.inter produces

                                oops


  
  find_theorems front  consumes

end
                                prefer 2
                                  apply (simp add: SIM2(1,2,3,4,5)  operator_state.defs flip: filter_append map_append)

                                find_theorems  produces

                                term "map fst (filter (\<lambda>(d, t'). t' = t) (map (case_event (\<lambda>t d. (d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n (inps 1))))) = coll (inps 1) t"

                                find_theorems n


                                find_theorems step Out set_op

end
  prefer 2
  apply (rule refl)+
  apply simp


find_theorems "_ \<in> ran _ \<longleftrightarrow> _"

end
  apply blast
  apply simp
  apply simp
  apply (rule refl)+

find_theorems ip_state





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

  term "let f_colls = (\<lambda> t'. f (coll (map (\<lambda>(x, t). Data t (projl x)) (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1)@@- ltake n (inps 1)) t')) in
                    let ts = rmdups {} (filter (\<lambda> t. t \<notin> event.time ` lset (ldropn n (inps 1))) (map snd (input (os 1) 1 @ cbufs (1, 1) @ outpu (os 0) 1)@ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> t) (filter is_Data (ltaken n (inps 1)))))) in 
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
