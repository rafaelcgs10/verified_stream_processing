theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
  "../AntichainOrder"
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
     let os'' = consume os' 1 t 1 in
     let buf' = BENQ (Cap t 0) n buf in
     max_top' os'' buf' (sort_key time caps')))
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
  | x n t caps' os' os'' buf' where "io = Inp (Some 0) x" "\<not> is_Inl x" "(n, t) = projr x"
    "(caps', os') = (if Cap t 0 \<in> set caps then (caps, os) else (caps @ [Cap t 0], mint_cap os 0 t))"
    "os'' = consume os' 1 t 1"
    "buf' = BENQ (Cap t 0) n buf" "op = max_top' os'' buf' (sort_key time caps')"
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
  unfolding propagate_pointstamps_def
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
    unfolding propagate_pointstamps_def
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
      apply (simp add: multiset_eq_iff)
      apply (smt (verit, ccfv_threshold) add_diff_cancel_left diff_add_inverse diff_add_inverse2 diff_cancel2 diff_diff_cancel diff_diff_left diff_is_0_eq diff_le_self nat_le_linear ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
      done
    done
  subgoal
    apply transfer
    apply auto
    done
  done


lemma take_step_enum_dataflow_topology_take_step:
  "enum_dataflow_topology su dataflow_topology_from_tree.followed_by \<Longrightarrow>
   take_step su = enum_dataflow_topology.take_step su dataflow_topology_from_tree.followed_by (<)"
  apply (rule ext)+
  subgoal for S c
    apply (cases S; hypsubst_thin)
     apply (simp add: Executable.enum_dataflow_topology.take_step.simps)
    apply (subst Executable.enum_dataflow_topology.take_step.simps(2))
     apply assumption
    apply (simp add: after_summary_def mymin_code_def)
    done
  done

lemma take_step_PR_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   \<exists>t loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR) c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t="(<)", simplified, unfolded enum_dataflow_topology_def])
     apply assumption+
  subgoal 
    apply standard
        apply auto
    done
   apply assumption
  apply (elim exE)
  subgoal for t loc loc' t'
    apply (subst take_step_enum_dataflow_topology_take_step)
     apply (simp add: enum_dataflow_topology_def)
    apply (rule Propagate.dataflow_topology.p_preserves_inv_imps_work_sum[where loc=loc and t=t'])
      apply assumption+
    done
  done

lemma take_step_CM_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   d \<noteq> 0 \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary (CM loc t d)) c)"
  apply (frule Executable.enum_dataflow_topology.CM_next[where delta=d, simplified, unfolded enum_dataflow_topology_def])
    apply assumption+
  apply (elim exE)
  apply (subst take_step_enum_dataflow_topology_take_step)
   apply (simp add: enum_dataflow_topology_def)
  apply (rule Propagate.dataflow_topology.cm_preserves_inv_imps_work_sum)
    apply assumption+
  done

lemma take_step_CM_p_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   d \<noteq> 0 \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary (CM loc t d)) c) \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg ((take_step summary (CM loc t d)) c) \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary (CM loc t d)) c)"
  apply (frule Executable.enum_dataflow_topology.CM_next[where delta=d, simplified, unfolded enum_dataflow_topology_def])
    apply assumption+
  apply (elim exE)
  apply (subst (1 2) take_step_enum_dataflow_topology_take_step)
   apply (simp add: enum_dataflow_topology_def)
  apply (intro conjI)
    apply (rule Propagate.dataflow_topology.cm_preserves_inv_implications_nonneg)
      apply assumption+
   apply (rule Propagate.dataflow_topology.iiws_imp_iipwn)
    apply assumption+
   apply (subst take_step_enum_dataflow_topology_take_step[symmetric])
    apply (simp add: enum_dataflow_topology_def)
   apply (rule take_step_CM_p_preserves_inv_imps_work_sum)
      apply assumption+
   apply auto[1]
  apply (rule take_step_CM_p_preserves_inv_imps_work_sum)
     apply assumption+
  apply auto
  done

lemma change_multiplicities_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   (\<forall> d \<in> snd ` snd ` set xs. d \<noteq> 0) \<Longrightarrow>
   (\<forall> (l, t, d) \<in> set xs. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c l) \<and> t' \<le> t) \<Longrightarrow>
   change_multiplicities summary xs c = c' \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c'"
  apply (induct xs arbitrary: c c')
   apply simp
  subgoal premises prems for a xs c c'
    using prems(2-) apply -
    apply (simp split: prod.splits)
    subgoal for l b t' d t
      apply (subst (asm) change_multiplicities_simps(2)[where summary=summary])
      apply (frule take_step_CM_p_preserves_inv[where loc=l and t=t'])
           apply assumption+
       apply force
      apply (elim conjE)
      using prems(1) apply -
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      back
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply fastforce
      apply (drule meta_mp)
       apply auto
      done
    done
  done

lemma take_step_PR_p_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   \<exists>t loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary PR) c) \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg ((take_step summary PR) c) \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR) c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t="(<)", simplified, unfolded enum_dataflow_topology_def])
     apply assumption+
  subgoal 
    apply standard
        apply auto
    done
   apply assumption
  apply (elim exE)
  subgoal for t loc loc' t'
    apply (subst (1 2) take_step_enum_dataflow_topology_take_step)
     apply (simp add: enum_dataflow_topology_def)
    apply (intro conjI)
      apply (rule Propagate.dataflow_topology.p_preserves_inv_implications_nonneg)
         apply assumption+
     apply (rule Propagate.dataflow_topology.iiws_imp_iipwn)
      apply assumption+
     apply (subst take_step_enum_dataflow_topology_take_step[symmetric])
      apply (simp add: enum_dataflow_topology_def)
     apply (rule take_step_PR_p_preserves_inv_imps_work_sum)
       apply assumption+
     apply auto[1]
    apply (rule take_step_PR_p_preserves_inv_imps_work_sum)
      apply assumption+
    apply auto
    done
  done

lemma propagate_all_preserves_inv:
  "propagate_all summary c = Some c' \<Longrightarrow>
   dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c'"
  unfolding propagate_all_def
  subgoal
    apply (drule while_option_rule[rotated])
      defer
      apply (rule take_step_PR_p_preserves_inv)
          apply assumption+
         apply simp_all
    subgoal
      unfolding worklist_is_empty_def 
      apply clarsimp
      apply blast
      done
    done
  done

lemma propagate_all_frontier_c_imp_correctness_aux:
  "propagate_all summary c = Some c' \<Longrightarrow>
   dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   (t \<in>\<^sub>A frontier (c_imp c' loc)) = (t \<in>\<^sub>A dataflow_topology.implied_frontier_alt summary dataflow_topology_from_tree.followed_by c' loc) \<and>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c'"
  apply (frule propagate_all_preserves_inv)
      apply assumption+
  unfolding propagate_all_def worklist_is_empty_def
  apply (frule while_option_stop2)
  apply (intro conjI)
     apply (rule Propagate.dataflow_topology.implication_frontier_iff_implied_frontier_alt_vacant)
        apply simp_all
  apply (rule Propagate.dataflow_topology.empty_worklists_vacant_to)
   apply auto
  done

lemma propagate_all_frontier_c_imp_correctness:
  "propagate_all summary c = Some c' \<Longrightarrow>
   dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   frontier (c_imp c' loc) = dataflow_topology.implied_frontier_alt summary dataflow_topology_from_tree.followed_by c' loc \<and>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c'"
  using propagate_all_frontier_c_imp_correctness_aux by (metis dataflow_topology.antichain_eqI)


lemma take_step_PR_preserves_c_pts[simp]:
  "c_pts (take_step summary PR c) = c_pts c"
  by (simp_all split: prod.splits if_splits)


lemma propagate_all_preserves_c_pts:
  assumes "propagate_all summary c = Some c'"
  shows "c_pts c' = c_pts c"
  apply (rule while_option_rule[rotated, OF assms[unfolded propagate_all_def comp_def]])
   apply simp
  apply (simp only: take_step_PR_preserves_c_pts)
  done

lemma c_pts_change_multiplicities_cong:
  "c_pts c loc = c_pts c' loc \<Longrightarrow>
   c_pts (change_multiplicities su cbs c) loc = c_pts (change_multiplicities su cbs c') loc"
  apply (induct cbs arbitrary: c c')
   apply simp
  subgoal premises prems for a cbs c c'
    using prems(2-) apply -
    apply (cases a)
    apply (auto split: prod.splits simp add: change_multiplicities_simp_alt)
    using prems(1) apply metis+
    done
  done




lemma propagate_pointstamps_correctness:
  "propagate_pointstamps summary c cbs = Some c' \<Longrightarrow>
   dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   (\<forall> d \<in> snd ` snd ` set cbs. d \<noteq> 0) \<Longrightarrow>
   (\<forall> (l, t, d) \<in> set cbs. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c l) \<and> t' \<le> t) \<Longrightarrow>
   frontier (c_imp c' loc) = dataflow_topology.implied_frontier_alt summary dataflow_topology_from_tree.followed_by (change_multiplicities summary cbs c) loc"
  unfolding propagate_pointstamps_def
  apply simp
  apply (frule propagate_all_frontier_c_imp_correctness[where loc=loc])
       apply assumption+
     prefer 4
  subgoal
    apply simp
    apply (subgoal_tac "c_pts c' = c_pts (change_multiplicities summary cbs c)" )
     apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
      apply assumption
     apply simp
    apply (rule propagate_all_preserves_c_pts)
    apply assumption
    done
  using change_multiplicities_preserves_inv apply fastforce+
  done

lemma propagate_pointstamps_preserve_inv:
  "propagate_pointstamps summary c cbs = Some c' \<Longrightarrow>
   dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   (\<forall> d \<in> snd ` snd ` set cbs. d \<noteq> 0) \<Longrightarrow>
   (\<forall> (l, t, d) \<in> set cbs. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c l) \<and> t' \<le> t) \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c'"
  unfolding propagate_pointstamps_def
  apply simp
  apply (frule propagate_all_frontier_c_imp_correctness)
       apply assumption+
  using change_multiplicities_preserves_inv apply fastforce+
  done

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

lemma time_below_frontier_iff:
  "time_below_frontier t f \<longleftrightarrow> (\<exists> t'. t' \<in>\<^sub>A f \<and> t < t')"
  unfolding time_below_frontier_def
  apply auto
  done

lemma in_M_not_time_below_frontier:
  "0 < zcount M t \<Longrightarrow>
   \<not> time_below_frontier t (frontier M)"
  apply (auto simp add: time_below_frontier_iff)
  apply (drule dataflow_topology_from_tree.in_frontier_least)
  apply (drule spec[of _ t])
  apply (drule mp)
   apply auto
  done

fun zmset where
  "zmset [] = {#}\<^sub>z"
| "zmset ((x, d) # xs) = update_zmultiset (zmset xs) x d"

lemma update_zmultiset_plus[simp]:
  "update_zmultiset (A + B) x n = update_zmultiset A x n + B"
  apply transfer
  apply (auto simp: equiv_zmset_def)
  subgoal for A B A' B'
    apply (auto simp add: multiset_eq_iff split: if_splits)
    done
  done

lemma update_zmultiset_plus_comm:
  "update_zmultiset A x n + B = A + update_zmultiset B x n"
  apply transfer
  apply (auto simp: equiv_zmset_def)
  subgoal for A B A' B'
    apply (auto simp add: multiset_eq_iff split: if_splits)
    done
  done

lemma zmset_append[simp]:
  "zmset (xs @ ys) = zmset xs + zmset ys"
  apply (induct xs arbitrary: ys)
   apply auto
  done


lemma c_pts_change_multiplicities:
  "c_pts (change_multiplicities su xs c) = (\<lambda> l. c_pts c l + zmset (map snd (filter (\<lambda> (l', t, d). l = l') xs)))"
  apply (induct xs arbitrary: c)
   apply simp
  subgoal for x xs c
    apply (rule ext)+
    apply (cases x)
    apply (auto split: if_splits prod.splits simp add: change_multiplicities_simp_alt update_zmultiset_plus_comm) 
    done
  done

lemma c_pts_change_multiplicities_cong_stronger:
  "c_pts c loc = c_pts c' loc \<Longrightarrow>
   filter (\<lambda> (loc', _, _). loc = loc') cbs = filter (\<lambda> (loc', _, _). loc = loc') cbs' \<Longrightarrow>
   c_pts (change_multiplicities su cbs c) loc = c_pts (change_multiplicities su cbs' c') loc"
  apply (subst (1 2) c_pts_change_multiplicities)
  apply simp
  done


lemma time_below_frontier_frontier_below_eq_frontier:
  "time_below_frontier t f \<Longrightarrow>
   f \<le> (frontier M) \<Longrightarrow>
   zcount M t \<le> 0"
  apply (simp add: time_below_frontier_iff less_eq_antichain_def)
  apply (rule ccontr)
  apply (simp add: not_le)
  apply (erule Timely_Infrastructure.dataflow_topology_from_tree.obtain_elem_frontier)
  apply (elim conjE)
  apply (drule spec, drule mp, assumption)
  apply auto
  apply transfer
  unfolding incomparable_def
  apply auto
  apply (metis basic_trans_rules(20,21))
  done

lemma UNIV_location[simp]:
  "(UNIV :: ('a :: enum, 'b :: enum) location set) = (\<lambda> (n, p). Loc n p) ` (UNIV \<times> UNIV)"
  apply (auto split: prod.splits)
  apply (metis UNIV_I location.exhaust pair_imageI)
  done

lemma UNIV_port[simp]:
  "(UNIV :: ('a :: enum) port set) = Trg ` UNIV \<union> Src ` UNIV"
  apply auto
  using port.exhaust_sel apply blast
  done

lemma UNIV_Numerals[simp]:
  "(UNIV :: 1 set) = {1}"
  "(UNIV :: 2 set) = {0, 1}"
   apply auto
  subgoal for x
    apply (cases x)
    apply auto
    subgoal for z
      apply (cases z)
       apply auto
      subgoal for n
        apply (cases n)
         apply auto
        done
      done
    done
  done

definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then antichain {0}
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then antichain {0} 
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain {0 :: nat}
   else {}\<^sub>A)"

lemma my_summ_same[simp]:
  "my_summ loc loc = {}\<^sub>A"
  apply (cases loc)
  subgoal for n p
    apply (cases p)
     apply (simp_all add: my_summ_def)
    done
  done

lemma graph_my_sum[simp]:
  "Graph.graph my_summ"
  apply standard
    apply force
   apply force
  apply simp
  done


lemma dataflow_topology_my_summ[simp]:
  "dataflow_topology my_summ (-+-)"
  apply standard
       apply simp
      apply simp
     apply simp
    apply simp_all
  subgoal for loc xs s
    apply (cases loc)
    subgoal for n p
      apply (cases p; cases n; simp)
      subgoal for z
        apply (cases z; simp)
        subgoal for n
          apply (cases n; simp; hypsubst_thin)
          subgoal
            apply (erule Graph.graph.path.cases[of my_summ, OF graph_my_sum]; simp)
            apply clarsimp
            apply (metis (mono_tags, lifting) location.inject mem_antichain_nonempty my_summ_def my_summ_same one_neq_zero zero_one)     
            done
          subgoal
            apply (erule Graph.graph.path.cases[of my_summ, OF graph_my_sum]; simp)
            apply clarsimp
            apply (smt (verit, best) graph.path.cases graph_my_sum location.inject mem_antichain_nonempty my_summ_def one_neq_zero port.simps(4))
            done
          done
        done
      subgoal for z
        apply (cases z; simp)
        subgoal for n
          apply (cases n; simp; hypsubst_thin)
          subgoal
            apply (erule Graph.graph.path.cases[of my_summ, OF graph_my_sum]; simp)
            apply clarsimp
            apply (metis (no_types, lifting) graph.path.cases graph_my_sum location.inject mem_antichain_nonempty my_summ_def my_summ_same one_neq_zero)
            done
          subgoal
            apply (erule Graph.graph.path.cases[of my_summ, OF graph_my_sum]; simp)
            apply clarsimp
            apply (smt (verit, best) graph.path.cases graph_my_sum location.inject mem_antichain_nonempty my_summ_def one_neq_zero port.simps(4))
            done
          done
        done
      done
    done
  done


lemma after_summary_zero_antichain[simp]:
  "dataflow_topology.after_summary (-+-) M (antichain { 0 :: nat }) = M"
  apply (subst dataflow_topology.after_summary_def[where summary=my_summ])
   apply simp
  apply (subst antichain_inverse)
   apply (auto simp add: incomparable_def)
  done


definition "my_summ' = (\<lambda> l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then frontier (abs_zmultiset (mset [0 :: nat], {#}))
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then frontier (abs_zmultiset (mset [0], {#}))
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then frontier (abs_zmultiset (mset [0], {#}))
   else {}\<^sub>A)"

abbreviation "nxt_l su l \<equiv> {l'. \<not> is_empty_antichain (su l l')}"

abbreviation "conn su l V \<equiv> \<Union> ((\<lambda> l'. (\<lambda> w. (l, w, l')) ` (set_antichain (su l l'))) ` V)"

value "conn my_summ' (Loc (0 :: 2) (Src (0 :: 1))) (nxt_l my_summ' (Loc (0 :: 2) (Src (0 :: 1))))"

(* 
function all_paths where
 "all_paths su V (l :: 'loc :: enum) = 
  (let N = nxt_l su l - V in
    if N = {}
    then {[]}
    else let C = conn su l N in
    (\<lambda> (l, w, l'). [(l, w, l')]) ` C \<union> \<Union> ((\<lambda> (l, w, l'). ((Cons (l, w, l')) ` (all_paths su (insert l V) l'))) ` C))"
     apply auto
  done
termination
  apply (relation "measure (\<lambda> (su, V, l :: 'loc :: enum). card (UNIV - nxt_l su l - V))")
  oops
 *)

lemma sum_weights_foldr:
  "Graph.graph.sum_weights (map (\<lambda>(s, l, t). l) xs) + x = foldr (+) (map (\<lambda>(s, l, t). l) xs) x"
  apply (induct xs arbitrary: x rule: rev_induct)
   apply auto
  by (metis (full_types) add.assoc)

lemma antichain_singletonD[dest]:
  "t \<in>\<^sub>A antichain {x} \<Longrightarrow>
   t = x"
  apply (subst (asm) member_antichain.abs_eq)
   apply (auto simp add: incomparable_def eq_onp_def)
  done

lemma in_sigletonI[simp]:
  "x \<in>\<^sub>A antichain {x}"
  by (metis finite.emptyI finite.insertI in_antichain_minimal_antichain insertI1 minimal_antichain_singleton)

lemma t_in_my_summD[dest]:
  "t \<in>\<^sub>A my_summ l l' \<Longrightarrow>
   t = 0"
  apply (cases l; cases l'; simp)
  subgoal for n p n' p'
    apply (cases n; cases p; cases p'; simp)
    subgoal for z
      apply (cases z; simp)
      subgoal for n
        apply (cases n; simp)
        subgoal
          unfolding my_summ_def
          apply (simp split: if_splits)
          using mem_antichain_nonempty apply blast
          done
        subgoal
          unfolding my_summ_def
          apply (simp split: if_splits)
          using mem_antichain_nonempty apply blast
          done
        done
      done
    subgoal for z
      apply (cases z; simp)
      subgoal for n
        apply (cases n; simp)
        subgoal
          unfolding my_summ_def
          apply (simp split: if_splits)
           apply blast
          using mem_antichain_nonempty apply blast
          done
        subgoal
          unfolding my_summ_def
          apply (simp split: if_splits)
           apply blast
          using mem_antichain_nonempty apply blast
          done
        done
      done
    subgoal for z
      apply (cases z; simp)
      subgoal for n
        apply (cases n; simp)
        subgoal
          unfolding my_summ_def
          apply (simp split: if_splits)
           apply blast
          using mem_antichain_nonempty apply blast
          done
        subgoal
          unfolding my_summ_def
          apply (simp split: if_splits)
          using mem_antichain_nonempty apply blast
          done
        done
      done
    subgoal for z
      apply (cases z; simp)
      subgoal for n
        apply (cases n; simp)
        subgoal
          unfolding my_summ_def
          apply (simp split: if_splits)
          using mem_antichain_nonempty apply blast
          done
        subgoal
          unfolding my_summ_def
          apply (simp split: if_splits)
          using mem_antichain_nonempty apply blast
          done
        done
      done
    done
  done

lemma path_my_summ_sum_path_weights_zeroD:
  "graph.path my_summ l1 l2 xs \<Longrightarrow>
   graph.sum_path_weights xs = 0 \<and>
   (l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) \<or>
    l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0) \<or>
    l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0) \<or>
    l1 = Loc 0 (Trg 0) \<and> l2 = Loc 1 (Trg 0) \<or>
    l1 = Loc 0 (Trg 0) \<and> l2 = Loc 1 (Src 0) \<or>
    l1 = Loc 0 (Src 0) \<and> l2 = Loc 1 (Src 0) \<or>
    l1 = l2)"
  apply (induct xs arbitrary: l1 l2 rule: rev_induct)
   apply simp_all
  subgoal
    apply (erule Graph.graph.path.cases[OF graph_my_sum])
     apply auto
    done
  subgoal for x xs l1 l2
    apply (auto del: disjCI conjI split: prod.splits)
    subgoal for l b l'
      apply (erule Graph.graph.path_AppendE[OF graph_my_sum])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply assumption
      apply simp
      apply (elim conjE disjE)
            apply simp_all
      subgoal
        apply (intro conjI)
         apply fast
        apply (metis mem_antichain_nonempty my_summ_def zero_one)
        done
      subgoal
        apply (intro conjI)
         apply fast
        apply (metis mem_antichain_nonempty my_summ_def zero_one)
        done
      subgoal
        apply (intro conjI)
         apply fast
        apply (metis location.inject mem_antichain_nonempty my_summ_def zero_one)
        done
      subgoal
        apply (intro conjI)
         apply fast
        apply (metis location.inject mem_antichain_nonempty my_summ_def zero_one)
        done
      subgoal
        apply (intro conjI)
         apply fast
        apply (metis location.inject mem_antichain_nonempty my_summ_def zero_one)
        done
      subgoal
        apply (intro conjI)
         apply fast
        apply (metis mem_antichain_nonempty my_summ_def zero_one)
        done
      subgoal
        apply (intro conjI)
         apply fast
        apply (metis mem_antichain_nonempty my_summ_def zero_one)
        done
      done
    done
  done


lemma path_weight_my_summ_simps[simp]:
  "graph.path_weight my_summ = (\<lambda> l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then antichain {0}
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then antichain {0} 
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain {0 :: nat}
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 1 (Trg 0)
   then antichain {0}
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain {0}
   else if l1 = Loc 0 (Src 0) \<and> l2 = Loc 1 (Src 0)
   then antichain {0}
   else if l1 = l2
   then antichain {0}
   else {}\<^sub>A)"
  apply (subst Graph.graph.path_weight_def)
  subgoal
    apply auto
    done
  subgoal
    apply (simp add: map_fun_def comp_def)
    apply (rule ext)+
    subgoal for l1 l2
      apply (rule Propagate.dataflow_topology.antichain_eqI[OF dataflow_topology_my_summ])
      apply (rule iffI)
      subgoal for t
        apply (subst (asm) Antichain.member_antichain.abs_eq[unfolded incomparable_def])
        subgoal
          unfolding graph.path_weightp_def[OF graph_my_sum] minimal_antichain_def
          apply (auto simp add: eq_onp_same_args finite_nat_set_iff_bounded_le)
          apply (meson linorder_le_less_linear)
          done
        subgoal 
          apply (subst (asm) Antichain.in_minimal_antichain)
          apply (elim conjE)
          apply safe
          apply (drule Graph.graph.path_weightp_ex_path[OF graph_my_sum, unfolded Let_def])
          apply (elim conjE exE)
          using path_my_summ_sum_path_weights_zeroD
          by (smt (verit) Collect_cong \<open>Graph.graph my_summ\<close> graph.finite_minimal_antichain_path_weightp graph.minimal_antichain_path_weightp_member graph.path_weightp_def in_antichain_minimal_antichain le_neq_implies_less
              mem_Collect_eq memb_imp_not_empty minimal_antichain_subset singleton_conv2 subset_singletonD zero_one)
        done
      subgoal premises prems for t
        apply (subst Antichain.member_antichain.abs_eq[unfolded incomparable_def])
        subgoal
          unfolding graph.path_weightp_def[OF graph_my_sum] minimal_antichain_def
          apply (auto simp add: eq_onp_same_args finite_nat_set_iff_bounded_le)
          apply (meson linorder_le_less_linear)
          done
        subgoal 
          apply (subst Antichain.in_minimal_antichain)
          unfolding graph.path_weightp_def[OF graph_my_sum] minimal_antichain_def
          using prems apply -
          apply (simp only: split: if_splits; (drule antichain_singletonD)?; (elim conjE)?; hypsubst_thin?)
          subgoal
            apply auto
            apply (rule exI[of _ "[] @ [((Loc 0 (Src 1), 0,Loc 1 (Trg 1)))]"])
            apply (intro conjI)
             apply (rule Graph.graph.path.intros(2))
               apply (simp_all add: graph.path0)
            unfolding my_summ_def
            apply auto
            done
          subgoal
            apply auto
            apply (rule exI[of _ "[] @ [((Loc 0 (Trg 1), 0, Loc 0 (Src 1)))]"])
            apply (intro conjI)
             apply (rule Graph.graph.path.intros(2))
               apply (simp_all add: graph.path0)
            unfolding my_summ_def
            apply auto
            done
          subgoal
            apply auto
            apply (rule exI[of _ "[] @ [((Loc 1 (Trg 1), 0, Loc 1 (Src 1)))]"])
            apply (intro conjI)
             apply (rule Graph.graph.path.intros(2))
               apply (simp_all add: graph.path0)
            unfolding my_summ_def
            apply auto
            done
          subgoal
            apply auto
            apply (rule exI[of _ "([] @ [((Loc 0 (Trg 1), 0, Loc 0 (Src 1)))]) @ [((Loc 0 (Src 1), 0, Loc 1 (Trg 1)))]"])
            apply (intro conjI)
             apply (rule Graph.graph.path.intros(2))
               apply (simp add: graph.path0)
              apply (rule Graph.graph.path.intros(2))
                apply (simp_all add: graph.path0)
            unfolding my_summ_def
             apply auto
            done
          subgoal
            apply auto
            apply (rule exI[of _ "(([] @ [((Loc 0 (Trg 1), 0, Loc 0 (Src 1)))]) @ [((Loc 0 (Src 1), 0, Loc 1 (Trg 1)))]) @ [((Loc 1 (Trg 1), 0, Loc 1 (Src 1)))]"])
            apply (intro conjI)
             apply (rule Graph.graph.path.intros(2))
               apply (simp add: graph.path0)
              apply (rule Graph.graph.path.intros(2))
                apply (simp add: graph.path0)
               apply (rule Graph.graph.path.intros(2))
                 apply (simp add: graph.path0)
                apply (simp_all add: graph.path0)
            unfolding my_summ_def
              apply auto
            done
          subgoal
            apply auto
            apply (rule exI[of _ "([] @ [((Loc 0 (Src 1), 0, Loc 1 (Trg 1)))]) @ [((Loc 1 (Trg 1), 0, Loc 1 (Src 1)))]"])
            apply (intro conjI)
             apply (rule Graph.graph.path.intros(2))
               apply (simp add: graph.path0)
              apply (rule Graph.graph.path.intros(2))
                apply (simp add: graph.path0)
               apply (simp_all add: graph.path0)
            unfolding my_summ_def
             apply auto
            done
          subgoal
            apply auto
            apply (rule exI[of _ "[]"])
            apply (intro conjI)
             apply (rule Graph.graph.path.intros(1))
              apply auto
            done
          subgoal
            by (metis mem_antichain_nonempty)
          done
        done
      done
    done
  done

(* FIXME: move me *)
lemma concat_map_empty_tripple[simp]:
  "concat (map (\<lambda>(l', t, d). []) xs) = []"
  by simp
lemma concat_map_empty[simp]:
  "concat (map (\<lambda>x. []) xs) = []"
  by simp

lemma map_filter_different[simp]:
  "l1 \<noteq> l2 \<Longrightarrow>
   filter (\<lambda>(l', t, d). l2 = l') (map (\<lambda>(p, y). (l1, y)) xs) = []"
  by (induct xs) auto

lemma map_filter_different_tripple[simp]:
  "l1 \<noteq> l2 \<Longrightarrow>
   filter (\<lambda>(l', t, d). l2 = l') (map (\<lambda>(p, t, m). (l1, t, - m)) xs) = []"
  by (induct xs) auto

lemma zcount_zmset:
  "zcount (zmset xs) t = sum_list (map snd (filter (\<lambda> (t', x). t = t') xs))"
  by (induct xs) (auto simp add: zcount_update_zmultiset)



lemma zcount_zmset_filter_neg[simp]:
  "(\<forall> (p, t, m) \<in> set xs. m \<ge> 0) \<Longrightarrow>
   zcount (zmset (map snd (filter (\<lambda>(l', t, d). l = l') (map (\<lambda>(p, t, m). (l, t, - m)) xs)))) t \<le> 0"
  apply (auto simp add: zcount_zmset)
  apply (induct xs )
   apply auto
  done

lemma map_snd_concat[simp]:
  "map snd (concat (map (\<lambda>(p, t, m). [(x, t, m)]) ys)) = map snd ys"
  by (induct ys) auto

lemma map_snd_filter[simp]:
  "map snd (filter (\<lambda>(l', t, d). l = l') (map (\<lambda>(p, y). (l, y)) xs)) =
   map snd xs"
  by (induct xs) auto

lemma frontier_update_zmultiset_keep1[simp]:
  "zcount A x > 0 \<Longrightarrow> zcount A x + m > 0 \<Longrightarrow> frontier (update_zmultiset A x m) = frontier A"
  apply transfer
  unfolding minimal_antichain_def
  apply (auto simp add: zcount_update_zmultiset dest: less_imp_not_eq2)
  done

lemma frontier_update_zmultiset_keep2[simp]:
  "zcount A x \<le> 0 \<Longrightarrow> zcount A x + m \<le> 0 \<Longrightarrow> frontier (update_zmultiset A x m) = frontier A"
  apply transfer
  unfolding minimal_antichain_def
  apply (clarsimp simp add: zcount_update_zmultiset dest: less_imp_not_eq2)
  apply fastforce
  done

lemma reachable_locations_my_summ[simp]:
  "reachable_locations my_summ = UNIV"
  unfolding reachable_locations_def
  apply auto
  subgoal for x loc'
    apply (cases x; simp)
    subgoal for x1 x2
      apply (cases x1; simp)
      subgoal for z
        apply (cases z; simp)
        subgoal for n
          apply (cases n; simp)
           apply (metis (full_types) num1_eq1 port.set_cases port.set_sel(1,2))
          apply (metis (full_types) num1_eq1 port.exhaust)
          done
        done
      done
    done
  subgoal for x loc'
    apply (cases x; simp)
    subgoal for x1 x2
      apply (cases x1; simp)
      subgoal for z
        apply (cases z; simp)
        subgoal for n
          apply (cases n; simp)
           apply (metis (full_types) num1_eq1 port.set_cases port.set_sel(1,2))
          apply (metis (full_types) num1_eq1 port.exhaust)
          done
        done
      done
    done
  subgoal
    apply (rule exI[of _ "Loc 0 (Trg 1)"])
    apply (auto simp add: is_empty_antichain.rep_eq Set.is_empty_def)
    apply (metis dataflow_topology_from_tree.empty_antichain empty_antichain.rep_eq empty_antichain_def in_sigletonI my_summ_def set_antichain_inject zero_one)
    done
  subgoal
    apply (rule exI[of _ "Loc 0 (Src 1)"])
    apply (auto simp add: is_empty_antichain.rep_eq Set.is_empty_def)
    apply (metis dataflow_topology_from_tree.empty_antichain empty_antichain.rep_eq empty_antichain_def in_sigletonI my_summ_def set_antichain_inject zero_one)
    done
  subgoal
    apply (rule exI[of _ "Loc 1 (Trg 1)"])
    apply (auto simp add: is_empty_antichain.rep_eq Set.is_empty_def)
    apply (metis dataflow_topology_from_tree.empty_antichain empty_antichain.rep_eq empty_antichain_def in_sigletonI my_summ_def set_antichain_inject zero_one)
    done
  subgoal
    apply (rule exI[of _ "Loc 1 (Src 1)"])
    apply (auto simp add: is_empty_antichain.rep_eq Set.is_empty_def)
    apply (metis dataflow_topology_from_tree.empty_antichain empty_antichain.rep_eq empty_antichain_def in_sigletonI my_summ_def set_antichain_inject zero_one)
    done
  done

definition "changes_bellow_impl chgs impls = (\<forall>(l, t, d)\<in>set chgs. \<exists>t'. t' \<in>\<^sub>A frontier (impls l) \<and> t' \<le> t)"

definition "changes_non_zero chgs = (\<forall>d\<in>snd ` snd ` set chgs. d \<noteq> 0)"

lemma mset_tl:
  "xs \<noteq> [] \<Longrightarrow>
   mset (tl xs) = mset xs - {#hd xs#}"
  by (metis mset_remove1 remove1_tl)


lemma zmset_of_remove1_mset:
  "x \<in># xs \<Longrightarrow>
   zmset_of (remove1_mset x xs) = update_zmultiset (zmset_of xs) x (-1)"
  by (smt (verit, del_insts) Groups.add_ac(2,3) Multiset.multi_member_split add_cancel_right_left add_mset_diff_bothsides add_uminus_conv_diff diff_empty eq_iff_diff_eq_0 numeral_nat(7) of_nat_0_eq_iff of_nat_eq_1_iff
      union_mset_add_mset_left update_zmultiset_simps(1,3) zmset_of_add_mset zmset_of_plus)

(* FIXME: move me *)
lemma sort_key_append:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> k x \<le> k y"
  and "inj_on k (set xs \<union> set ys)"
  shows   "sort_key k (xs @ ys) = sort_key k xs @ sort_key k ys"
  using assms apply -
  apply (rule properties_for_sort_key)
    apply simp_all
  subgoal
    apply (rule arg_cong2[where f=append])
    subgoal
      apply safe
      apply (smt (verit, best) filter_cong sort_key_stable)
      apply (smt (verit, best) filter_cong sort_key_stable)
      done
    subgoal
      apply safe
      apply (smt (verit, best) filter_cong sort_key_stable)
      apply (smt (verit, best) filter_cong sort_key_stable)
      done
    done
  subgoal
    by (metis (mono_tags, lifting) map_append set_sort sorted_sort_key sorted_wrt_append sorted_wrt_map)
  done

find_consts name: sorted name: w

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
   (front os2 0) \<le> (frontier (c_pts c (Loc 1 (Trg 0)) + c_pts c (Loc 0 (Src 0)))) \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum (summ sg) dataflow_topology_from_tree.followed_by (pt_tr sg) \<Longrightarrow>
   summ sg = my_summ \<Longrightarrow>
   edges sg = (\<lambda> l. if l = Loc 0 (Src 1) then [Loc 1 (Trg 1)] else []) \<Longrightarrow>
   (\<forall> (p, t, m) \<in> set (consu os2). m \<ge> 0) \<Longrightarrow>
   c_pts c (Loc 0 (Trg 1)) = {#}\<^sub>z \<Longrightarrow>
   consu os1 = [] \<Longrightarrow>
   frontier (zmset (map snd (produ os1))) \<le> frontier (zmset (map snd (inter os1))) \<Longrightarrow>
   (frontier (c_pts (change_multiplicities (summ sg) (lo_pt sg) (pt_tr sg)) (Loc 0 (Src 0)) + c_pts (change_multiplicities (summ sg) (lo_pt sg) (pt_tr sg)) (Loc 1 (Trg 0)))) \<le> (frontier (zmset (map snd (produ os1)))) \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum (summ sg) (-+-) (pt_tr sg) \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg (pt_tr sg) \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg (pt_tr sg) \<Longrightarrow>
   changes_bellow_impl (lo_pt sg) (c_imp (pt_tr sg)) \<Longrightarrow>
   changes_non_zero (lo_pt sg) \<Longrightarrow>
   (\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). \<forall> t' p. Cap t' p \<in> set caps \<longrightarrow> t' \<le> t) \<Longrightarrow>
   sorted_wrt (\<lambda> (_, x) (_, y). x \<le> y) ((map projr (buf1 (Inr (1, 1)))) @ (outpu os1 0)) \<Longrightarrow>
   dataflow_op sg (inp_m_top os1 (\<lambda> p. n p) inps buf1 os2 buf2 caps) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. xs p @@- ys p @@- lconcat (lmap (\<lambda> (xs, t). case xs of [] \<Rightarrow> [] | _ \<Rightarrow> [(Max (set xs), t)]) (lzip (inps p) (iterates ((+) 1) (n p))))))\<close>
proof (coinduction arbitrary: xs ys os1 os2 n caps buf1 buf2 inps sg sg' a b c st1 st2 rule: weakBisimWeakUptoBisimCong)
  case SIM1
  show ?case (is "wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2")
  proof -
    define R where "R = ?R"
    from SIM1 show ?thesis unfolding R_def[symmetric]
      apply -
      unfolding wsim_def
      apply (intro allI conjI impI)
      subgoal premises prems for io op1'
        using prems(27-) apply -
        apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin?)
        apply simp_all
        prefer 8
        subgoal 
          unfolding R_def
          apply simp
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
            using prems(5,6,7,8, 14) prems(9)[symmetric] apply -
            apply (simp add: change_multiplicities_append_comp comp_def)
            apply (elim conjE)
            apply hypsubst_thin
            apply (rule c_pts_change_multiplicities_cong_stronger)
            apply simp
            unfolding extract_progress_def
            apply (auto simp add: comp_def filter_empty_conv)
            done
          apply simp
          subgoal
            using prems(5,6,7,8,14) prems(10)[symmetric]  apply -
            apply (auto simp add: change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            unfolding extract_progress_def
            apply (simp add: comp_def)
            done
          subgoal
            apply simp
            using prems(5,6,7,8,14) apply simp
            apply (rule Orderings.preorder_class.order_trans)
            apply (rule prems(11)[simplified])
            apply simp
            apply hypsubst_thin
            apply (auto simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          subgoal
            using prems(12) by simp
          using prems(13) apply simp
          using prems(14) apply simp
          using prems(15) apply simp
          subgoal
            using prems(5,6,7,8,14,16) 
            apply simp
            apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          using prems(17) apply simp
          using prems(18) apply simp
          using prems(19) apply simp
          using prems(20) apply simp
          using prems(21) apply simp
          using prems(22) apply simp
          using prems(23) apply simp
          using prems(24) apply simp
          using prems(25) apply simp
          using prems(26) apply simp
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
        prefer 11
        subgoal 
          unfolding R_def
          apply simp
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
            apply (auto split: option.splits)
            subgoal for c'
              apply (subst propagate_pointstamps_correctness)
              apply assumption
              using prems(13) apply simp
              subgoal premises
                using prems(13) apply simp
                done
              using prems(20) apply simp
              using prems(21) apply simp
              using prems(22) apply simp
              using prems(24)[unfolded changes_non_zero_def] apply simp
              using prems(23)[unfolded changes_bellow_impl_def] apply simp
              using prems(25) apply simp
              using prems(26) apply simp
              subgoal
                apply (subst dataflow_topology.implied_frontier_alt_def)
                using prems(13) apply simp
                apply simp
                using prems(13) apply -
                apply (simp add: dataflow_topology.after_summary_empty_summary[OF dataflow_topology_my_summ])
                unfolding propagate_pointstamps_def Let_def
                apply (subst (1 2 3) propagate_all_preserves_c_pts[symmetric])
                apply assumption+
                using prems(5,6,7,8,14) apply simp
                apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                apply (subgoal_tac "c_pts c' (Loc 0 (Trg 1)) = {#}\<^sub>z \<and> consu os1 = []")
                subgoal
                  apply (auto 0 0)
                  apply (drule propagate_all_preserves_c_pts)
                  apply (simp add: c_pts_change_multiplicities)
                  apply (rule Orderings.preorder_class.order_trans)
                  apply (rule frontier_below_eq_frontier_plus)
                  subgoal premises
                    apply (rule Orderings.preorder_class.order_trans)
                    apply (rule frontier_below_eq_frontier_plus_frontier_below_eq_frontier_plus[where M="zmset (map snd (filter (\<lambda>(l'::(2, 1) location, t::nat, d::int). Loc 0 (Src 1) = l') (map (\<lambda>(p::1, y::nat \<times> int). (Loc 0 (Src 1), y)) (operator_state.inter os1)))) + zmset (map snd (concat (map (\<lambda>(p::1, t::nat, m::int). [(Loc 1 (Trg 1), t, m)]) (produ os1))))"])
                    subgoal
                      apply (subst (4) Groups.add_ac(2))
                      apply (rule frontier_below_eq_frontier_plus_frontier_below_eq_frontier_plus_gen)
                      subgoal
                        using prems(18) apply -
                        apply simp
                        done
                      subgoal
                        using prems(19) apply -
                        apply (auto 0 0 simp add: Groups.add_ac(2) extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                        done
                      done
                    apply (rule Orderings.preorder_class.order_trans)
                    apply (rule frontier_below_eq_frontier_plus_neg_alt)
                    apply (intro allI)
                    apply (rule zcount_zmset_filter_neg[where l="Loc (1 :: 2) (Trg (1 :: 1))"])
                    using prems(15) apply blast
                    apply (rule Orderings.preorder_class.eq_refl)
                    apply (rule arg_cong[where f=frontier])
                    apply simp
                    done
                  done
                subgoal
                  using prems(5,6,7,8,14,15,16,17) apply simp
                  apply (drule propagate_all_preserves_c_pts)
                  apply simp
                  apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                  done
                done
              done
            done
          subgoal
            using prems(13) prems(20-24)[unfolded changes_bellow_impl_def changes_non_zero_def] by (auto split: option.splits dest!: propagate_pointstamps_preserve_inv)
          subgoal
            using prems(13) prems(20-24)[unfolded changes_bellow_impl_def changes_non_zero_def] by (auto split: option.splits dest!: propagate_pointstamps_preserve_inv)
          subgoal
            using prems(14) by (auto split: option.splits)
          using prems(15) apply simp
          subgoal
            using prems(5,6,7,8,14,16) 
            apply simp
            apply (auto 0 0 simp add: extract_progress_def propagate_pointstamps_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits dest!: propagate_all_preserves_c_pts; hypsubst_thin?)
            done
          using prems(17) apply simp
          using prems(18) apply simp
          subgoal
            using prems(19) apply simp
            apply (auto 0 0 simp add: extract_progress_def propagate_pointstamps_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits dest!: propagate_all_preserves_c_pts; hypsubst_thin?)
            done
          subgoal
            using prems(13) prems(20-24)[unfolded changes_bellow_impl_def changes_non_zero_def] by (auto split: option.splits dest!: propagate_pointstamps_preserve_inv)
          subgoal
            using prems(13) prems(20-24)[unfolded changes_bellow_impl_def changes_non_zero_def] by (auto split: option.splits dest!: propagate_pointstamps_preserve_inv)
          subgoal
            using prems(13) prems(20-24)[unfolded changes_bellow_impl_def changes_non_zero_def] by (auto split: option.splits dest!: propagate_pointstamps_preserve_inv)
          subgoal
            using prems(13) prems(20-24) by (auto simp add: changes_bellow_impl_def changes_non_zero_def split: option.splits dest!: propagate_pointstamps_preserve_inv)
          subgoal
            using prems(13) prems(20-24) by (auto simp add: changes_bellow_impl_def changes_non_zero_def split: option.splits dest!: propagate_pointstamps_preserve_inv)
          using prems(25) apply simp
          using prems(26) apply simp
          apply (simp add: comp_def)
          done
        defer
        subgoal for x xs
          unfolding R_def
          apply simp
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
            using prems(5,6,7,8, 14) prems(9)[symmetric] apply -
            apply (simp add: change_multiplicities_append_comp comp_def)
            done
          subgoal
            using prems(5,6,7,8,14) prems(10)[symmetric]  apply -
            apply (auto simp add: change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          subgoal
            apply simp
            using prems(5,6,7,8,14) apply simp
            apply (rule Orderings.preorder_class.order_trans)
            apply (rule prems(11)[simplified])
            apply simp
            done
          subgoal
            using prems(12) by simp
          using prems(13) apply simp
          using prems(14) apply simp
          using prems(15) apply simp
          subgoal
            using prems(5,6,7,8,14,16) 
            apply simp
            done
          using prems(17) apply simp
          using prems(18) apply simp
          using prems(19) apply simp
          using prems(20) apply simp
          using prems(21) apply simp
          using prems(22) apply simp
          using prems(23) apply simp
          using prems(24) apply simp
          subgoal
            using prems(25)
            unfolding BENQ_def
            apply auto
            done
          subgoal 
            using prems(26)
            unfolding BENQ_def
            apply (auto simp add: List.linorder_class.sorted_append)
            done
          subgoal
            apply (rule rtranclp_intros_1)
            apply (rule arg_cong3[where f=map_op])
            apply simp
            apply simp
            apply (rule arg_cong[where f=source_op])
            apply (rule ext)
            apply (rule arg_cong2[where f=lshift])
            apply simp
            apply (rule arg_cong2[where f=lshift])
            subgoal
              apply (auto split: prod.splits)
              subgoal
                apply (rule arg_cong2[where f=max_from_caps_buf])
                apply (auto simp add: comp_def)
                apply (metis UnI1 insert_absorb)
                apply (rule ext)
                apply (metis append_Cons empty_append_eq_id list_to_buf_append)
                done
              subgoal
                apply (rule arg_cong2[where f=max_from_caps_buf])
                apply (auto simp add: comp_def)
                apply (metis (no_types, lifting) UnCI image_iff insert_absorb split_conv)
                apply (rule ext)
                apply (metis append_Cons empty_append_eq_id list_to_buf_append)
                done
              subgoal
                apply (rule arg_cong2[where f=max_from_caps_buf])
                apply (auto simp add: comp_def)
                apply (rule ext)
                apply (metis append_Cons empty_append_eq_id list_to_buf_append)
                done
              done
            apply simp
            done
          done
        subgoal 
          using prems(3) apply -
          apply (rule FalseE)
          unfolding BHD_def
          apply auto
          apply (drule spec[of _ "hd (buf1 (Inr (1, 1)))"])
          apply (drule mp)
          apply (auto split: sum.splits)
          apply (cases "hd (buf1 (Inr (1, 1)))"; simp)
          done
        subgoal for n t
          unfolding R_def 
          apply simp
          using prems(1,2,3) apply -
          apply (intro exI conjI[rotated])
          apply (intro relcomppI)
          apply (rule bisim_refl)
          defer
          apply (rule wbisim_refl)
          defer
          apply (rule wb_upto_b_base)
          apply (intro conjI exI)
          apply (rule refl)+
          apply (metis BTL_access list.set_sel(2) zero_one)
          subgoal
            using prems(4) sorted_filter by auto
          subgoal
            apply simp
            using prems(5,6,7,8, 14) prems(9) apply -
            apply (simp add: change_multiplicities_append_comp comp_def)
            apply (elim conjE)
            apply hypsubst_thin
            unfolding extract_progress_def
            apply (auto simp add: comp_def filter_empty_conv c_pts_change_multiplicities)
            subgoal premises prems2
              using prems2(1,2) prems2(9,3)[symmetric] apply -
              unfolding BTL_def
              apply auto
              apply (subst mset_tl)
               apply fast
              apply simp
              apply (subst image_mset_remove1_mset_if)
              apply (simp split: if_splits)
              apply (subst zmset_of_remove1_mset)
               apply simp
              apply simp
              apply (metis BHD_def add_cancel_right_right snd_conv update_zmultiset_plus_comm)
              done
            done
          subgoal
            using prems(5,6,7,8,14) prems(10)[symmetric]  apply -
            apply (auto simp add: change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            unfolding extract_progress_def
            apply (simp add: comp_def)
            done
          subgoal
            apply simp
            using prems(5,6,7,8,14) apply simp
            apply (rule Orderings.preorder_class.order_trans)
             apply (rule prems(11)[simplified])
            apply simp
            apply hypsubst_thin
            apply (auto simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply (subgoal_tac "\<forall> t'. zcount (update_zmultiset {#}\<^sub>z t (- 1)) t' \<le> 0")
            using frontier_below_eq_frontier_plus_neg apply (smt (verit, ccfv_SIG) Max_top.update_zmultiset_plus arith_simps(50) update_zmultiset_plus_comm)
            apply (auto simp add: zcount_update_zmultiset)
            done
          subgoal
            using prems(12) by simp
          using prems(13) apply simp
          using prems(14) apply simp
          using prems(15) apply simp
          subgoal
            using prems(5,6,7,8,14,16) 
            apply simp
            apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          using prems(17) apply simp
          using prems(18) apply simp
          using prems(19) apply simp
          using prems(20) apply simp
          using prems(21) apply simp
          using prems(22) apply simp
          using prems(23) apply simp
          using prems(24) apply simp
          subgoal
            unfolding BTL_def
            using prems(25) apply clarsimp
            apply (metis (no_types, lifting) image_iff in_set_tlD)
            done
          subgoal 
            using prems(26)
            unfolding BENQ_def BHD_def BTL_def
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
            done
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
            subgoal 
              apply (subst max_from_caps_buf_append)
              apply (subst (2) max_from_caps_buf_append)
              apply (rule arg_cong2[where f=append])
              subgoal
                apply (rule arg_cong2[where f=max_from_caps_buf])
                using prems(4) apply (simp add: sort_key_id_if_sorted)
                apply (simp add: comp_def list_to_buf_def BTL_def BHD_def BENQ_def BULK_BENQ_def)
                apply (rule ext)+
                apply (auto simp add: map_eq_Cons_conv)
                apply (rule exI[of _ t])
                apply (intro conjI exI[of _ "filter (\<lambda>(x, t'). t' = t) (map projr (tl (buf1 (Inr (1, 1)))))"])
                  apply auto
                apply (smt (verit, best) case_prod_conv filter.simps(2) list.collapse list.simps(9))
                subgoal for t'
                  apply (cases t')
                  apply auto
                apply (smt (verit, best) case_prod_conv filter.simps(2) list.collapse list.simps(9))
                  done
                done
              subgoal
                apply (rule arg_cong2[where f=max_from_caps_buf])
                subgoal
                 apply (simp add: comp_def list_to_buf_def BTL_def BHD_def BENQ_def BULK_BENQ_def flip: rmdups_append)
                  apply (rule arg_cong2[where f=append])
                  subgoal
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
                    done
                  subgoal
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
                apply (rule rmdups_cong)
                    apply (auto split: prod.splits)
                    done
                  done
                subgoal
                  apply (rule ext)+
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
                  apply (auto 0 0 simp add: comp_def list_to_buf_def BTL_def BHD_def BENQ_def BULK_BENQ_def split: if_splits)
                  apply (metis (full_types) capability.exhaust capability.sel(1) num1_eq1) 
                  done
                done
              done
            done
          done
  subgoal for n t
          unfolding R_def 
          apply simp
          using prems(1,2,3) apply -
          apply (intro exI conjI[rotated])
          apply (intro relcomppI)
          apply (rule bisim_refl)
          defer
          apply (rule wbisim_refl)
          defer
          apply (rule wb_upto_b_base)
          apply (intro conjI exI)
          apply (rule refl)+
          apply (metis BTL_access list.set_sel(2) zero_one)
          subgoal
            using prems(4) sorted_filter by auto
          subgoal
            apply simp
            using prems(5,6,7,8, 14) prems(9) apply -
            apply (simp add: change_multiplicities_append_comp comp_def)
            apply (elim conjE)
            apply hypsubst_thin
            unfolding extract_progress_def
            apply (auto simp add: comp_def filter_empty_conv c_pts_change_multiplicities)
            subgoal premises prems2
              using prems2(1,2) prems2(9,3)[symmetric] apply -
              unfolding BTL_def
              apply auto
              apply (subst mset_tl)
               apply fast
              apply simp
              apply (subst image_mset_remove1_mset_if)
              apply (simp split: if_splits)
              apply (subst zmset_of_remove1_mset)
               apply simp
              apply simp
              apply (metis BHD_def add_cancel_right_right snd_conv update_zmultiset_plus_comm)
              done
            done
          subgoal
            using prems(5,6,7,8,14) prems(10)[symmetric]  apply -
            apply (auto simp add: change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            unfolding extract_progress_def
            apply (simp add: comp_def)
            done
          subgoal
            apply simp
            using prems(5,6,7,8,14) apply simp
            apply (rule Orderings.preorder_class.order_trans)
             apply (rule prems(11)[simplified])
            apply simp
            apply hypsubst_thin
            apply (auto simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply (subgoal_tac "\<forall> t'. zcount (update_zmultiset {#}\<^sub>z t (- 1)) t' \<le> 0")
            using frontier_below_eq_frontier_plus_neg apply (smt (verit, ccfv_SIG) Max_top.update_zmultiset_plus arith_simps(50) update_zmultiset_plus_comm)
            apply (auto simp add: zcount_update_zmultiset)
            done
          subgoal
            using prems(12) by simp
          using prems(13) apply simp
          using prems(14) apply simp
          using prems(15) apply simp
          subgoal
            using prems(5,6,7,8,14,16) 
            apply simp
            apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          using prems(17) apply simp
          using prems(18) apply simp
          using prems(19) apply simp
          using prems(20) apply simp
          using prems(21) apply simp
          using prems(22) apply simp
          using prems(23) apply simp
          using prems(24) apply simp
          subgoal premises prems2
            using prems2(1,2,4,7) prems2(3)[symmetric] prems(25) prems(26) prems(4) apply -
            unfolding BTL_def BHD_def
            apply (cases "buf1 (Inr (1, 1))"; simp)
            apply (auto 0 0 simp add: sorted_wrt_append split: prod.splits sum.splits)
            subgoal for a xs a' t' x'
              apply (cases a; cases x'; simp)
              apply (meson is_Inr.simps(2))
              apply (meson UnI1 image_iff sum.sel(2))  
              done
          subgoal for a xs a' t' 
            by (metis UnCI)
          done
   subgoal 
            using prems(26)
            unfolding BENQ_def BHD_def BTL_def
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
            done
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
            subgoal 
              apply (rule arg_cong2[where f=max_from_caps_buf])
              subgoal
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
                  apply (auto 0 0 simp add: comp_def list_to_buf_def BTL_def BHD_def BENQ_def BULK_BENQ_def split: if_splits)
                apply (subgoal_tac "\<forall> t' \<in> time ` set caps. t \<ge> t' ")
                subgoal
                  apply (subst sort_key_append)
                    apply force
                   apply simp
                  apply (smt (verit, best) capability.exhaust capability.sel(1) image_iff inj_on_def num1_eq1)
                  apply simp
                  using prems(4) apply (metis sort_key_id_if_sorted)
                  done
                subgoal
                  using prems(25) apply -
                  apply (drule spec[of _ "(n, t)"])
                  apply (drule mp)
                   apply simp_all
                  subgoal premises prems2
                    using prems2(8) apply -
                    apply (intro ballI impI)
                    subgoal for t'
                    apply (drule spec[of _ "time t'"])
                      apply (drule mp)
                      apply (metis (full_types) capability.exhaust capability.sel(1) num1_eq1)
                      apply simp
                      done
                    done
                  done
                done
              subgoal
                apply (rule ext)+
            unfolding BENQ_def BHD_def BTL_def BULK_BENQ_def list_to_buf_def
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
            apply (metis (full_types) capability.exhaust capability.sel(1) num1_eq1)
            done
          done
        done
      done

                find_theorems "sort_key _ (_ @ _)"


end
                using prems(4) apply (simp add: sort_key_id_if_sorted)
                apply (simp add: comp_def list_to_buf_def BTL_def BHD_def BENQ_def BULK_BENQ_def)
                apply (rule ext)+
                apply (auto simp add: map_eq_Cons_conv)
                apply (rule exI[of _ t])
                apply (intro conjI exI[of _ "filter (\<lambda>(x, t'). t' = t) (map projr (tl (buf1 (Inr (1, 1)))))"])
                  apply auto
                apply (smt (verit, best) case_prod_conv filter.simps(2) list.collapse list.simps(9))
                subgoal for t'
                  apply (cases t')
                  apply auto
                apply (smt (verit, best) case_prod_conv filter.simps(2) list.collapse list.simps(9))
                  done
                done
              subgoal
                apply (rule arg_cong2[where f=max_from_caps_buf])
                subgoal
                 apply (simp add: comp_def list_to_buf_def BTL_def BHD_def BENQ_def BULK_BENQ_def flip: rmdups_append)
                  apply (rule arg_cong2[where f=append])
                  subgoal
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
                    done
                  subgoal
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
                apply (rule rmdups_cong)
                    apply (auto split: prod.splits)
                    done
                  done
                subgoal
                  apply (rule ext)+
                    apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
                  apply (auto 0 0 simp add: comp_def list_to_buf_def BTL_def BHD_def BENQ_def BULK_BENQ_def split: if_splits)
                  apply (metis (full_types) capability.exhaust capability.sel(1) num1_eq1) 
                  done
                done
              done
            done
          done


                find_theorems rmdups name: cong


                find_theorems BTL BENQ BULK_BENQ
 

end
qed
next
  case SIM2
  show ?case (is "wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2")
  proof -
    define R where "R = ?R"
    from SIM2 show ?thesis unfolding R_def[symmetric]
      apply -
      unfolding wsim_def
      apply (intro allI conjI impI)
      subgoal premises prems for io op1'
        using prems(25-) apply -
        apply (elim step_source_op_elim step_map_op_elim step_comp_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin?)      apply simp_all


end

  done
  subgoal
    using prems(5,6,7,8,14) prems(10)[symmetric]  apply -
    apply (auto simp add: change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
    done
  subgoal
    apply simp
    using prems(5,6,7,8,14) apply simp
    apply (rule Orderings.preorder_class.order_trans)
    apply (rule prems(11)[simplified])
    apply simp
    done
  subgoal
    using prems(12) by simp
  using prems(13) apply simp
  using prems(14) apply simp
  using prems(15) apply simp
  subgoal
    using prems(5,6,7,8,14,16) 
    apply simp
    done
  using prems(17) apply simp
  using prems(18) apply simp
  using prems(19) apply simp
  using prems(20) apply simp
  using prems(21) apply simp
  using prems(22) apply simp
  using prems(23) apply simp
  using prems(24) apply simp
  subgoal
    apply (rule rtranclp_intros_1)
    apply (rule arg_cong3[where f=map_op])
    apply simp
    apply simp
    apply (rule arg_cong[where f=source_op])
    apply (rule ext)
    apply (rule arg_cong2[where f=lshift])
    apply simp


end


end