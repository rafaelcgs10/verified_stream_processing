theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
begin 

(* FIXME: move me *)
abbreviation "choice5 op1 op2 op3 op4 op5 \<equiv> choice3 (choice2 op1 op2) (choice2 op3 op4) op5"

find_consts "_ + _ \<Rightarrow> _" name: "is_"

abbreviation "mint_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"

abbreviation "produces os batch \<equiv> os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

abbreviation "drop_caps os caps \<equiv> (os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, -1)) caps \<rparr>)"



corec max_top' where
  "max_top' os buf caps = choice5
   (Read None (\<lambda> st. if is_Inl st \<and> is_Inr (projl st) then max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps else \<oslash>))
   (let below_caps = [cap \<leftarrow> caps. time_below_frontier (time cap) (front os 0)] in
    let above_caps = [cap \<leftarrow> caps. \<not> time_below_frontier (time cap) (front os 0)] in
    let batch = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps in
    let os' = produces os batch in
    let os'' = drop_caps os' below_caps in
    let buf' = (\<lambda> cap. if cap \<in> set below_caps then [] else buf cap) in
    Silent (max_top' os'' buf' above_caps))
   (Read (Some 0)
    (\<lambda> x. if is_Inl x then \<oslash> else
     let (n, t) = projr x in
     let (caps', os') = (if Cap t 0 \<in> set caps then (caps, os) else (caps @ [Cap t 0], mint_cap os 0 t)) in
     let buf' = BENQ (Cap t 0) n buf in
     max_top' os' buf' (sort_key time caps')))
    ((case outpu os 0 of
         [] \<Rightarrow> Silent (max_top' os buf caps)
       |  x # xs \<Rightarrow> send_output (max_top' (os\<lparr> outpu := (outpu os)(0 := xs ) \<rparr>) buf caps) 0 x))
    (let (os', st) = obtain_progress os in
     send_progress (max_top' os' buf caps) st)"

lemma step_max'_top_elim:
  assumes "step io (max_top' os buf caps) op"
  obtains
    st where "io = Inp None st" "\<not> is_Inl st \<or> (is_Inl st \<and> \<not> is_Inr (projl st))" "op = \<oslash>" 
  | st where "io = Inp None st" "is_Inl st" "is_Inr (projl st)" "op = max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps" 
  | above_caps below_caps batch os' os'' buf' where "io = Tau" "below_caps = [cap \<leftarrow> caps. time_below_frontier (time cap) (front os 0)]"
    "above_caps = [cap \<leftarrow> caps. \<not> time_below_frontier (time cap) (front os 0)]"
    "batch = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps"
    "os' = produces os batch"
    "os'' = drop_caps os' below_caps"
    "buf' = (\<lambda> cap. if cap \<in> set below_caps then [] else buf cap)"
    "op = max_top' os'' buf' above_caps"
  | x where "io = Inp (Some 0) x" "is_Inl x" "op = \<oslash>"
  | x n t caps' os' buf' where "io = Inp (Some 0) x" "\<not> is_Inl x" "(n, t) = projr x"
    "(caps', os') = (if Cap t 0 \<in> set caps then (caps, os) else (caps @ [Cap t 0], mint_cap os 0 t))"
    "buf' = BENQ (Cap t 0) n buf" "op = max_top' os' buf' (sort_key time caps')"
  | "io = Tau" "outpu os 0 = []" "op = max_top' os buf caps"
  | x xs where "io = Out (Some 0) (Inr x)" "outpu os 0 = x # xs"
    "op = max_top' (os\<lparr> outpu := (outpu os)(0 := xs ) \<rparr>) buf caps"
  | os' st where "io = Out None (Inl (Inl st))" "obtain_progress os = (os', st)"
    "op = max_top' os' buf caps"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) max_top'.code)
  apply (cases io)
  subgoal for p x
    apply simp
    apply (cases p; simp; hypsubst_thin)
    subgoal
      by (auto del: disjCI split: if_splits list.splits sum.splits; hypsubst_thin?)
    subgoal
      by (cases x; force split: if_splits list.splits sum.splits; hypsubst_thin?)
    done
  subgoal for p x
    apply simp
    apply (cases p; simp; hypsubst_thin)
    subgoal
      by (auto del: disjCI split: if_splits list.splits sum.splits; hypsubst_thin?)
    subgoal
      by (cases x; force split: if_splits list.splits sum.splits; hypsubst_thin?)
    done
  subgoal
    by (fastforce split: if_splits list.splits)
  done

(* 
  abbreviation "max_top \<equiv> max_top' []"
*)

term "THE x. P x"
term "SOME x. P x"

term The
term Eps
term the_enat

corec max_op where
  "max_op n inps = Choice (cimage (\<lambda> p. case ldropWhile ((=) []) (inps p) of
     LCons xs lxs \<Rightarrow> 
     Write 
     (max_op (n(p := n p + 1 + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps (p := lxs)))
       p (Max (set xs), n p + the_enat (llength (ltakeWhile ((=) []) (inps p)))))
     (cfilter (\<lambda> p. ldropWhile ((=) []) (inps p) \<noteq> LNil) c\<UU>))"


lemma step_max_op_elim:
  assumes "step io (max_op n inps) op"
  obtains p xs lxs where "io = Out p (Max (set xs), n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))" "ldropWhile ((=) []) (inps p) = LCons xs lxs"
    "op = max_op (n (p := n p + 1 + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps(p := lxs))" "p \<notin> defaults"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) max_op.code)
  apply (clarsimp split: llist.splits list.splits)
  done

lemma step_max_op_Out_intro[intro]:
  "inps p = LCons xs lxs \<Longrightarrow>
   xs \<noteq> [] \<Longrightarrow>
   ys = inps(p := lxs) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out p (Max (set xs), n p)) (max_op n inps) (max_op (n(p := Suc (n p))) ys)"
  apply (subst max_op.code)
  apply (clarsimp split: llist.splits)
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force
   apply (rule refl)
  apply simp
  apply force
  done

lemma step_max_op_Out_intro2[intro]:
  "ldropWhile ((=) []) (inps p) = LCons xs lxs \<Longrightarrow>
   xs \<noteq> [] \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out p (Max (set xs), (n p) + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (max_op n inps) (max_op (n (p := n p + 1 + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps(p := lxs)))"
  apply (subst max_op.code)
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force
   apply (rule refl)
  apply auto
  done

lemma step_max_op_not_Tau[simp]:
  "\<not> step Tau (max_op n inps) op"
  apply (subst max_op.code)
  apply (auto split: llist.splits list.splits dest!: ldropWhile_LConsD)
  done

lemma step_max_op_not_Inp[simp]:
  "\<not> step (Inp p x) (max_op n inps) op"
  apply (subst max_op.code)
  apply (auto split: llist.splits list.splits dest!: ldropWhile_LConsD)
  done

lemma wstep_max_op_simp[simp]:
  "io \<noteq> Tau \<Longrightarrow>
   wstep io (max_op n inps) op = step io (max_op n inps) op"
  unfolding wstep_def
  apply (cases io; simp)
  using converse_rtranclpE apply fastforce
  subgoal
    apply (rule iffI)
    subgoal
      apply clarsimp
      apply (metis converse_rtranclpE step_max_op_elim step_max_op_not_Tau)
      done
    subgoal
      by auto
    done
  done

abbreviation "inp_top os caps inps \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (input_top os caps inps)"
abbreviation "m_top os buf caps \<equiv>  map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (max_top' os buf caps)"

abbreviation "inp_m_top os1 caps1 inps buf1 os2 buf2 caps2 \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] buf1 (inp_top os1 caps1 inps) (m_top os2 buf2 caps2))"


(* FIXME: move me *)
lemma dataflow_op_extract_progress_append:
  "dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> @ extract_progress nid (edges sg) \<lparr>cons = cs', inte = is', prod = ps'\<rparr>\<rparr>) op =
   dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>\<rparr>) op"
  apply (rule dataflow_op_change_multiplicities)
     apply simp_all
  unfolding extract_progress_def
  apply simp
  apply (smt (verit, del_insts) change_multiplicities_append change_multiplicities_comm)
  done

lemma propagate_pointstamps_comm:
  "propagate_pointstamps summary conf (cbs1 @ cbs2) = propagate_pointstamps summary conf (cbs2 @ cbs1)"
  unfolding propagate_pointstamps_def Let_def
  by (simp add: change_multiplicities_comm)

lemma propagate_pointstamps_append:
  "propagate_pointstamps summary conf cbs1 = Some conf' \<Longrightarrow>
   propagate_pointstamps summary conf (cbs1 @ cbs2) = propagate_pointstamps summary conf' cbs2"
  apply (induct cbs2 arbitrary: cbs1 conf conf' rule: rev_induct) 
  subgoal for cbs1 conf conf'
    unfolding propagate_pointstamps_def change_multiplicities_def propagate_all_def
    apply simp
    apply (metis (no_types, lifting) while_option_stop while_option_unfold)
    done
  subgoal for a cbs2 cbs1 conf conf'
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    unfolding propagate_pointstamps_def Let_def
    apply (simp; hypsubst_thin?)
    apply (subst change_multiplicities_append_comp)
    apply simp
    oops

(* edges sg = (\<lambda> l. if node l = 0 \<and> port l = Src 1 then [Loc 1 (Trg 0)] else []) \<Longrightarrow> *)

    term "map (\<lambda> xs. case xs of [] \<Rightarrow> [] | xs \<Rightarrow> [Max (set xs)])"

(* FIXME: move me *)
lemma map_in_setD:
  "map f xs = ys \<Longrightarrow>
   x \<in> set xs \<Longrightarrow>
   f x \<in> set ys"
  by force

(* FIXME: move me *)
definition
  buf_dom :: "('a \<Rightarrow> 'b buf) \<Rightarrow> 'a set" where
  "buf_dom m = {a. m a \<noteq> []}"
no_notation shiftr  (infixl \<open>>>\<close> 55)

definition "list_to_buf xs = (\<lambda> t. map fst (filter (\<lambda> (x, t'). t' = t) xs))"

lemma list_to_buf_empty[simp]:
  "list_to_buf [] = (\<lambda>  _. [])"
  unfolding list_to_buf_def by auto

fun rmdups where
  "rmdups S [] = []"
| "rmdups S (x # xs) = (if x \<in> S then rmdups S xs else x # (rmdups (insert x S) xs))"


lemma set_rmdups:
  "set (rmdups S xs) = set xs - S"
  by (induct xs arbitrary: S) auto

lemma rmdups_rmdups[simp]:
  "rmdups S1 (rmdups S2 xs) = rmdups (S1 \<union> S2) xs"
  by (induct xs arbitrary: S1 S2) (auto simp add: insert_absorb)

lemma rmdups_append[simp]:
  "rmdups S (xs @ ys) = rmdups S xs @ rmdups (S \<union> set xs) ys"
  by (induct xs arbitrary: S ys) (auto simp add: insert_absorb)

lemma rmdups_cong:
  "A \<inter> set xs = B \<inter> set xs \<Longrightarrow>
   rmdups A xs = rmdups B xs"
  apply (induct xs arbitrary: A B)
   apply simp
  apply (smt (verit, best) Diff_Diff_Int Diff_iff Int_insert_left_if1 insert_absorb inter_eq_subsetI list.inject list.set(2) list.set_intros(1) rmdups.simps(2) set_subset_Cons)
  done

abbreviation "update_caps caps xs \<equiv> caps @ rmdups (set caps) (map (\<lambda> (x, t). Cap t 0) xs)"

definition "max_from_caps_buf caps buf = map (\<lambda> cap. (Max (set (buf cap)), time cap)) caps"

abbreviation "max_from_buf caps buf xs \<equiv> (let caps' = update_caps caps xs in
                                         let buf' = list_to_buf xs o time in max_from_caps_buf caps' (buf' >> buf))"

(* lemma update_caps_new_cap:
  "snd ` set xs = {t} \<Longrightarrow>
   Cap t (0 :: 1) \<notin> set caps \<Longrightarrow>
   update_caps caps xs = caps @ [Cap t 0]"
  unfolding update_caps_def
  apply (induct xs arbitrary: caps t rule: rev_induct)
   apply clarsimp
  subgoal for a xs caps
    apply (cases a; fastforce)
    done
  done *)

lemma update_caps_append[simp]:                
  "update_caps caps (ys @ xs) = update_caps (update_caps caps ys) xs"
  oops

lemma update_caps_append2:
  "snd ` set xs \<inter> time ` set caps1 = {} \<Longrightarrow>
   caps = caps1 @ caps2 \<Longrightarrow>
   update_caps caps xs = caps1 @ update_caps caps2 xs"
  oops
    (*  apply hypsubst_thin
  apply (induct xs arbitrary: caps1 caps2)
   apply (auto simp add: rev_image_eqI)
  done
 *)

lemma list_to_buf_append[simp]:
  "list_to_buf (ys @ xs) = list_to_buf xs >> list_to_buf ys"
  unfolding list_to_buf_def BULK_BENQ_def
  apply (rule ext)
  apply auto
  done

lemma max_from_buf_append[simp]:
  "max_from_buf caps buf (ys @ xs) = max_from_buf (update_caps caps ys) ((list_to_buf ys o time) >> buf) xs"
  unfolding  Let_def 
  oops
    (*   apply (metis BULK_BENQ_bulk_benq fun_comp_eq_conv)
  done *)

(* 
lemma max_from_buf_move_all:
  "max_from_buf caps buf xs = max_from_buf ((update_caps caps xs)) ((list_to_buf xs o time) >> buf) []" 
  by (metis append.right_neutral max_from_buf_append) *)

lemma max_from_caps_buf_append:
  "max_from_caps_buf (caps1 @ caps2) buf = max_from_caps_buf caps1 buf @ max_from_caps_buf caps2 buf"
  unfolding max_from_caps_buf_def by auto 

(* lemma max_from_caps_buf_BULK_BENQ_empty:
  "buf_dom buf1 \<inter> set caps = {} \<Longrightarrow>
   max_from_caps_buf caps (buf1 >> buf2) = max_from_caps_buf caps buf2"
  unfolding max_from_caps_buf_def BULK_BENQ_def buf_dom_def apply clarsimp
  apply (metis (mono_tags, lifting) List.set_empty disjoint_iff mem_Collect_eq monoid.right_neutral sup_bot.monoid_axioms)
  done *)


(* FIXME: move me *)
lemma rtranclp_intros_1:
  "a = b \<Longrightarrow> r\<^sup>*\<^sup>* a b"
  by auto


lemma not_time_below_frontier_mono[intro]:
  "t < t' \<Longrightarrow>
   \<not> time_below_frontier t f \<Longrightarrow> \<not> time_below_frontier t' f"
  unfolding time_below_frontier_def
  apply simp
  apply transfer
  apply clarsimp
  apply (metis (no_types, lifting) Set.is_empty_def dual_order.strict_trans empty_iff ex_min_if_finite finite_filter member_filter)
  done

lemma zequal_equal[simp]:
  "zequal A B \<longleftrightarrow> A = B"
  apply safe
  subgoal
    apply transfer
    apply (auto simp: equiv_zmset_def)
    subgoal for A B A' B'
      apply transfer
      oops

lemma take_step_PR_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR ^^ k) c)"
  oops

lemma take_step_PR_p_preserves_inv_implications_nonneg:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary PR ^^ k) c)"
  oops

lemma
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   propagate_all summary c = Some c' \<Longrightarrow>
   (t \<in>\<^sub>A frontier (c_imp c' loc)) = (t \<in>\<^sub>A dataflow_topology.implied_frontier_alt summary dataflow_topology_from_tree.followed_by c' loc)"
  unfolding propagate_all_def worklist_is_empty_def
  apply (drule while_option_stop2)
  apply (rule Propagate.dataflow_topology.implication_frontier_iff_implied_frontier_alt_vacant)
     apply simp_all
    (*   using take_step_PR_p_preserves_inv_imps_work_sum apply force
  using take_step_PR_p_preserves_inv_implications_nonneg apply force
  apply (rule Propagate.dataflow_topology.empty_worklists_vacant_to)
   apply simp_all *)
  oops


lemma propagate_all_preserves_c_pts:
  "propagate_all (summ sg) c = Some c' \<Longrightarrow>
   c_pts c' = c_pts c"
  sorry

lemma c_pts_change_multiplicities_cong:
  "c_pts c loc = c_pts c' loc \<Longrightarrow>
   c_pts (change_multiplicities su cbs c) loc = c_pts (change_multiplicities su cbs c') loc"
  sorry

lemma is_empty_antichain_filter_antichain[simp]:
  "is_empty_antichain (filter_antichain P A) \<longleftrightarrow> (\<forall> a. a \<in>\<^sub>A A \<longrightarrow> \<not> P a)"
  apply transfer
  apply (metis Set.is_empty_def emptyE equals0I member_filter)
  done

lemma sorted_caps_append:
  "sorted (map time caps) \<Longrightarrow>
   caps = filter (\<lambda>cap. time_below_frontier (time cap) f) caps @ filter (\<lambda>cap. \<not> time_below_frontier (time cap) f) caps"
  unfolding time_below_frontier_def
  apply simp
  apply (induct caps)
   apply simp_all
  subgoal for cap caps
    by (smt (verit, ccfv_threshold) append_eq_append_conv2 append_same_eq filter_id_conv order_le_less_trans same_append_eq)
  done


definition
  "frontier_below_eq_frontier ft1 ft2 = (\<forall> t2. t2 \<in>\<^sub>A ft2 \<longrightarrow> \<not> (\<exists> t1. t1 \<in>\<^sub>A ft1 \<and> t2 \<le> t1))"

lemma time_below_frontier_iff:
  "time_below_frontier t f \<longleftrightarrow> (\<exists> t'. t' \<in>\<^sub>A f \<and> t < t')"
  unfolding time_below_frontier_def
  apply auto
  done

(*  lemma frontier_below_eq_frontier_not_time_below_frontier:
  "time_below_frontier t f1 \<Longrightarrow>
   frontier_below_eq_frontier f1 f2 \<Longrightarrow>
   \<not> time_below_frontier t f2 \<Longrightarrow>
   False"
  unfolding frontier_below_eq_frontier_def time_below_frontier_iff by force 
 *)
lemma in_M_not_time_below_frontier:
  "0 < zcount M t \<Longrightarrow>
   \<not> time_below_frontier t (frontier M)"
  apply (auto simp add: time_below_frontier_iff)
  apply (drule dataflow_topology_from_tree.in_frontier_least)
  apply (drule spec[of _ t])
  apply (drule mp)
   apply auto
  done


lemma c_pts_change_multiplicities:
  "c_pts (change_multiplicities su xs c) = fold (\<lambda> (l, t, d) M. M(l := update_zmultiset (M l) t d)) xs (c_pts c)"
  unfolding change_multiplicities_def
  apply (induct xs arbitrary: c)
   apply (simp_all split: prod.splits)
  done

lemma in_frontier_iff:
  "t \<in>\<^sub>A frontier M \<longleftrightarrow> ((\<forall> t'. zcount M t' > 0 \<longrightarrow> \<not> t' < t) \<and> zcount M t > 0)"
  by (metis dataflow_topology_from_tree.in_frontier_least dataflow_topology_from_tree.obtain_elem_frontier le_less member_frontier_pos_zmset)

lemma
  "time_below_frontier t f1 \<Longrightarrow>
   frontier_below_eq_frontier f1 f2\<Longrightarrow>
   \<not> t \<in>\<^sub>A f2"
  by (auto simp add:  in_frontier_iff time_below_frontier_iff frontier_below_eq_frontier_def dest: order_less_imp_le)

lemma time_below_frontier_frontier_below_eq_frontier:
  "time_below_frontier t f \<Longrightarrow>
   frontier_below_eq_frontier f (frontier M) \<Longrightarrow>
   zcount M t \<le> 0"
  apply (clarsimp simp add: in_frontier_iff time_below_frontier_iff frontier_below_eq_frontier_def)
  apply (smt (verit, ccfv_SIG) dual_order.strict_iff_order order_trans_rules(23) order_zmset_exists_foundation')
  done

lemma
  \<open>xs 0 = outpu os2 0 \<Longrightarrow>
   ys 0 = max_from_buf caps buf2 ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0) \<Longrightarrow>
   (\<forall> x \<in> set (buf1 (Inr (1, 0))). is_Inr x) \<Longrightarrow>
   sorted (map time caps) \<Longrightarrow>
   obtain_progress os1 = (a, st1) \<Longrightarrow>
   obtain_progress os2 = (b, st2) \<Longrightarrow>
   sg' = sg\<lparr> lo_pt := lo_pt sg @ extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2 \<rparr> \<Longrightarrow>
   c = change_multiplicities (summ sg') (lo_pt sg') (pt_tr sg') \<Longrightarrow>
   c_pts c (Loc 1 (Trg 0)) = zmset_of (mset (map snd ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0))) \<Longrightarrow>
   c_pts c (Loc 0 (Src 0)) = {# n 0 #}\<^sub>z \<Longrightarrow>
   frontier_below_eq_frontier (front os2 0) (frontier (c_pts c (Loc 1 (Trg 0)) + c_pts c (Loc 0 (Src 0)))) \<Longrightarrow>
   dataflow_op sg (inp_m_top os1 (\<lambda> p. n p) inps buf1 os2 buf2 caps) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. xs p @@- ys p @@- lconcat (lmap (\<lambda> (xs, t). case xs of [] \<Rightarrow> [] | _ \<Rightarrow> [(Max (set xs), t)]) (lzip (inps p) (iterates ((+) 1) (n p))))))\<close>
proof (coinduction arbitrary: xs ys os1 os2 n caps buf1 buf2 inps sg sg' a b c st1 st2 rule: weakBisimWeakUptoBisimCong)
  case SIM1
  then show ?case
    apply -
    unfolding wsim_def
    apply (intro allI conjI impI)
    subgoal premises prems for io op1'
      using prems(12-) apply -
      apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin?)
                 prefer 12
      subgoal for nid op'' imp_fron sg' io' op''a p op2' io'a op''b
        using prems(1,2) apply -
        apply (intro exI conjI[rotated])
         apply (intro relcomppI)
           apply (rule bisim_refl)
          defer
          apply (rule wbisim_refl)
         defer
         apply (rule wb_upto_b_base)
         apply (intro conjI exI)
                 apply (rule refl)+
        using prems(3) apply simp
        using prems(4) apply simp
        subgoal
          using prems(5,6,7,8) prems(9)[symmetric] apply -
          apply (auto simp add: propagate_pointstamps_def change_multiplicities_append_comp split: option.splits; hypsubst_thin?)
          subgoal for c'
            apply (drule propagate_all_preserves_c_pts)
            apply (rule c_pts_change_multiplicities_cong)
            apply (rule c_pts_change_multiplicities_cong)
            apply simp
            done
          done
        subgoal
          using prems(10)[symmetric] apply -
          apply (auto simp add: propagate_pointstamps_def change_multiplicities_append_comp split: option.splits; hypsubst_thin?)
          apply (drule propagate_all_preserves_c_pts)
          apply (smt (verit, ccfv_threshold) SIM1(7,8) c_pts_change_multiplicities_cong change_multiplicities_append prems(5,6) prod.simps(1) subgraph.simps(1,2,4,7) subgraph.surjective)
          done
        subgoal
          apply simp
          using prems(11) apply -
          sorry
        apply (simp add: comp_def)
        done
                prefer 8
      subgoal for op'' io' op''a op2' io'a op''b above_caps below_caps batch os' os'' buf'
        using prems(1,2) apply -
        apply (intro exI conjI[rotated])
         apply (intro relcomppI)
           apply (rule bisim_refl)
          defer
          apply (rule wbisim_refl)
         defer
         apply (rule wb_upto_b_base)
         apply (intro conjI exI)
                 apply (rule refl)+
        using prems(3) apply simp
        subgoal
          using prems(4) sorted_filter by blast
        subgoal
          apply simp
          using prems(5,6,7,8) prems(9)[symmetric] apply -
          apply (simp add: change_multiplicities_append_comp)
          apply hypsubst_thin
          sorry
          apply simp
        subgoal
          using prems(10)[symmetric] apply -
          apply (auto simp add: change_multiplicities_append_comp split: option.splits; hypsubst_thin?)
          sorry
        subgoal
          apply simp
          using prems(11)
          sorry
        subgoal
          apply simp
          apply (rule rtranclp_intros_1)
          apply (rule arg_cong3[where f=map_op])
            apply simp_all
          apply (rule arg_cong[where f=source_op])
          apply (rule ext)
          apply (simp_all add: lshift_assoc)
          apply (rule arg_cong2[where f=lshift])
           apply simp_all
          subgoal premises
            apply (subst max_from_caps_buf_append)
            apply (subst (2) max_from_caps_buf_append)
            apply (simp flip: append_assoc)
            apply (rule arg_cong2[where f=append])
            subgoal
              apply (subgoal_tac "caps = filter (\<lambda>cap. time_below_frontier (time cap) (front os2 1)) caps @ filter (\<lambda>cap. \<not> time_below_frontier (time cap) (front os2 1)) caps")
              subgoal
                unfolding max_from_caps_buf_def
                apply (simp add: map_eq_append_conv)
                apply (intro exI conjI)
                  apply assumption
                 apply auto
                subgoal premises prems2 for cap
                  using prems2(2,3) apply -
                  apply (subgoal_tac "(list_to_buf (outpu os1 1) >> list_to_buf (map projr (buf1 (Inr (1, 1)))) \<circ> time) cap = []")
                  subgoal
                    by simp
                  subgoal
                    apply (drule time_below_frontier_frontier_below_eq_frontier)
                    using prems(11) apply simp
                    using prems(9) apply simp
                    apply (auto simp add: list_to_buf_def filter_empty_conv)
                    subgoal
                      by (smt (verit, ccfv_threshold) bot_nat_0.extremum_unique count_image_mset_ge_count count_mset_0_iff of_nat_le_0_iff prems(10) prod.sel(2) semiring_1_class.of_nat_0 zcount_single zero_one)
                    subgoal
                      by (smt (verit, ccfv_threshold) SIM1(10) add.commute add_sign_intros(1) arith_simps(62) bot_nat_0.extremum count_image_mset_ge_count count_mset_0_iff le_antisym not_less of_nat_0_le_iff of_nat_le_0_iff snd_conv verit_comp_simplify(28)
                          zcount_add_zmset zcount_empty zero_one)
                    done
                  done
                subgoal
                  by (simp add: BULK_BENQ_def)
                done
                subgoal
                  using SIM1(4) sorted_caps_append by blast
                done
                subgoal
                  unfolding max_from_caps_buf_def
                  apply (auto simp add: comp_def)  
                  apply (rule arg_cong2[where f=append])
                  subgoal
                    apply (rule List.List.list.map_cong)
                    apply auto
                    subgoal
                      apply (rule rmdups_cong)
                      apply (auto split: prod.splits sum.splits)
                      apply (drule time_below_frontier_frontier_below_eq_frontier)
                    using prems(11) apply simp
                    using prems(9) apply simp
                    apply (auto simp add: list_to_buf_def filter_empty_conv)
                    apply (smt (verit, del_insts) SIM1(10) bot_nat_0.extremum_uniqueI count_image_mset_ge_count count_mset_0_iff of_nat_0_le_iff of_nat_le_0_iff snd_conv zcount_single zero_one)
                    done
                  subgoal for cap
                      apply (rule arg_cong[where f=Max])
                    apply (auto 0 0 simp add: set_rmdups list_to_buf_def filter_empty_conv BULK_BENQ_def split: sum.splits prod.splits; hypsubst_thin)
                    subgoal for yt x y t
                      apply (rule image_eqI[of _ _ "(x, t)"])
                       apply simp
                      apply auto
                            apply (drule time_below_frontier_frontier_below_eq_frontier)
                    using prems(11) apply simp
                    using prems(9) apply simp
                    apply (auto simp add: list_to_buf_def filter_empty_conv)
                    apply (smt (verit) SIM1(10) bot_nat_0.extremum_uniqueI count_image_mset_ge_count count_mset_0_iff of_nat_0_le_iff of_nat_le_0_iff prod.sel(2) zcount_single zero_one)
                    done
                  done
                done
              subgoal
                    apply (rule List.List.list.map_cong)
                    apply auto
                subgoal
                      apply (rule rmdups_cong)
                      apply (auto split: prod.splits sum.splits)
                      apply (drule time_below_frontier_frontier_below_eq_frontier)
                    using prems(11) apply simp
                    using prems(9) apply simp
                    apply (auto simp add: list_to_buf_def filter_empty_conv)
                    apply (smt (verit, best) SIM1(10) count_image_mset_ge_count count_mset_gt_0 linorder_not_le of_nat_0_le_iff of_nat_le_0_iff snd_conv zcount_single zero_one)
                    done
                  subgoal for cap
                      apply (rule arg_cong[where f=Max])
                    apply (auto 0 0 simp add: set_rmdups list_to_buf_def filter_empty_conv BULK_BENQ_def split: sum.splits prod.splits; hypsubst_thin)
                    subgoal for a t x
                      apply (rule image_eqI[of _ _ "(x, t)"])
                       apply simp
                      apply auto
                            apply (drule time_below_frontier_frontier_below_eq_frontier)
                    using prems(11) apply simp
                    using prems(9) apply simp
                    apply (auto simp add: list_to_buf_def filter_empty_conv)
                    apply (smt (verit) SIM1(10) bot_nat_0.extremum_uniqueI count_image_mset_ge_count count_mset_0_iff of_nat_0_le_iff of_nat_le_0_iff prod.sel(2) zcount_single zero_one)
                    done
                  done
                done
              done
            done
          done
        done

end
                      sorry
                    subgoal for cap
                      apply (subgoal_tac "\<not> (time_below_frontier (time cap) (front os2 1))")
                      subgoal
                        by (auto simp add: time_below_frontier_def comp_def BULK_BENQ_def set_rmdups split: sum.splits prod.splits)
                      subgoal
                        apply (auto simp add: set_rmdups split: sum.splits prod.splits; hypsubst_thin)


                        find_theorems set rmdups

end
  apply (drule frontier_below_eq_frontier_not_time_below_frontier)
  using prems(12) apply simp
  subgoal
    apply (auto simp add: time_below_frontier_iff)
    using prems(5,6,7,8,9) apply hypsubst_thin
    apply clarsimp
    apply hypsubst_thin
    apply (auto simp add: in_frontier_iff)
    apply (drule spec[of _ "time cap"])
    apply (drule mp)
    subgoal premises prems2
      using prems2(2,4) apply -
      apply (simp add:  count_image_mset)

      find_theorems sum vimage

      find_theorems "count (image_mset _ _)" 


end
  subgoal
    apply (simp add: c_pts_change_multiplicities)


    find_theorems "filter _ _ = []"

end
