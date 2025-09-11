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
   (let below_caps = [cap \<leftarrow> caps. \<not> frontier_less_equal (front os 0) (time cap) ] in
    let above_caps = [cap \<leftarrow> caps. frontier_less_equal (front os 0) (time cap) ] in
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
  | above_caps below_caps batch os' os'' buf' where "io = Tau" "below_caps = [cap \<leftarrow> caps. \<not> frontier_less_equal (front os 0) (time cap)]"
    "above_caps = [cap \<leftarrow> caps. frontier_less_equal (front os 0) (time cap)]"
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
(* lemma dataflow_op_extract_progress_append:
  "dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> @ extract_progress nid (edges sg) \<lparr>cons = cs', inte = is', prod = ps'\<rparr>\<rparr>) op =
   dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>\<rparr>) op"
  apply (rule dataflow_op_change_multiplicities)
     apply simp_all
  unfolding extract_progress_def
  apply simp
  apply (smt (verit, del_insts) change_multiplicities_append change_multiplicities_comm)
  done *)

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


lemma set_rmdups[simp]:
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

lemma rmdups_NilI:
  "(set xs \<subseteq> A \<and> xs \<noteq> []) \<or> xs = [] \<Longrightarrow>
   rmdups A xs = []"
  apply (induct xs arbitrary: A)
   apply simp_all
  done

lemma rmdups_insert_NilI:
  "(set xs = {a} \<and> xs \<noteq> []) \<or> xs = [] \<Longrightarrow>
   rmdups (insert a A) xs = []"
  apply (induct xs arbitrary: A)
   apply auto
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
   take_step su = enum_dataflow_topology.take_step su dataflow_topology_from_tree.followed_by cless"
  apply (rule ext)+
  subgoal for S c
    apply (cases S; hypsubst_thin)
     apply (simp add: Executable.enum_dataflow_topology.take_step.simps)
    apply (subst Executable.enum_dataflow_topology.take_step.simps(2))
     apply assumption
    apply (simp add: after_summary_def mymin_code_def)
    done
  done

lemma nat_cless_less:
  \<open>(cless :: nat \<Rightarrow> nat \<Rightarrow> bool) = (<) \<close>
  by (simp add: ID_code ccompare_nat_def ord_defs(2))

lemma nat_less_less_eq:
  \<open>(\<lambda>(t :: nat) u. t < u \<or> t = u) = (\<le>)\<close>
  using nat_less_le by auto

lemma take_step_PR_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   \<exists>(t :: nat) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR) c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
     apply assumption
    apply (simp add: nat_cless_less nat_less_less_eq linorder_class.linorder_axioms)
   apply (simp add: nat_cless_less)
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
   \<exists>(t :: nat) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary PR) c) \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg ((take_step summary PR) c) \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR) c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
     apply assumption
    apply (simp add: nat_cless_less nat_less_less_eq linorder_class.linorder_axioms)
   apply (simp add: nat_cless_less)
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
  "propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> nat antichain) c = Some c' \<Longrightarrow>
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
   ((t :: nat) \<in>\<^sub>A frontier (c_imp c' loc)) = (t \<in>\<^sub>A dataflow_topology.implied_frontier_alt summary dataflow_topology_from_tree.followed_by c' loc) \<and>
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
  "propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> nat antichain) c = Some c' \<Longrightarrow>
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
   (\<forall> (l, t :: nat, d) \<in> set cbs. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c l) \<and> t' \<le> t) \<Longrightarrow>
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

lemma update_zmultiset_plus_comm:
  "update_zmultiset A x n + B = A + update_zmultiset B x n"
  apply transfer
  apply (auto simp: equiv_zmset_def)
  subgoal for A B A' B'
    apply (auto simp add: multiset_eq_iff split: if_splits)
    done
  done


lemma c_imp_change_multiplicities[simp]:
  "c_imp (change_multiplicities su xs c) = c_imp c"
  apply (induct xs arbitrary: c)
   apply simp
  apply (auto split: if_splits prod.splits simp add: change_multiplicities_simp_alt update_zmultiset_plus_comm) 
  done

lemma propagate_pointstamps_preserve_inv:
  "propagate_pointstamps summary c cbs = Some c' \<Longrightarrow>
   dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   (\<forall> d \<in> snd ` snd ` set cbs. d \<noteq> 0) \<Longrightarrow>
   (\<forall> (l, t :: nat, d) \<in> set cbs. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c l) \<and> t' \<le> t) \<Longrightarrow>
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
   caps = filter (\<lambda>cap. \<not> frontier_less_equal f (time cap)) caps @ filter (\<lambda>cap. frontier_less_equal f (time cap)) caps"
  unfolding frontier_less_equal_def
  apply simp
  apply (induct caps)
   apply simp_all
  subgoal for cap caps
    by (metis (mono_tags, lifting) basic_trans_rules(23) filter_id_conv self_append_conv2)
  done

lemma frontier_less_equal_iff:
  "frontier_less_equal f t \<longleftrightarrow> f \<le> frontier {#t#}\<^sub>z"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply (auto simp add: in_frontier_iff)
  done

lemma frontier_less_equal_le_trans:
  "frontier_less_equal f1 t \<Longrightarrow>
   f2 \<le> f1 \<Longrightarrow> 
   frontier_less_equal f2 t"
  unfolding frontier_less_equal_iff
  apply (rule Orderings.preorder_class.order_trans)
   apply assumption+
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


lemma frontier_less_equal_frontier_below_eq_frontier:
  "\<not> frontier_less_equal f t \<Longrightarrow>
   f \<le> (frontier M) \<Longrightarrow>
   zcount M t \<le> 0"
  apply (simp add: frontier_less_equal_iff less_eq_antichain_def)
  apply (rule ccontr)
  apply (simp add: not_le)
  apply (erule Timely_Infrastructure.dataflow_topology_from_tree.obtain_elem_frontier)
  apply (elim conjE)
  apply (drule spec, drule mp, assumption)
  apply auto
  oops

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
  (* 
 (*Initial state: only initial capability at source ports *)
abbreviation "cbs1 \<equiv> concat (map (\<lambda> nid. map (\<lambda> p. (Loc (nid :: 2) (Src (p :: 1)), 0, 1)) enum_class.enum) enum_class.enum)"

abbreviation "c1 \<equiv> the (propagate_pointstamps my_summ' empty_conf cbs1)"

(* Implications at Trg of op2: abs_zmultiset (mset [0], mset []) *)
value "c_imp c1 (Loc 1 (Trg 1))"

(* op2 consumes some message *)
abbreviation "cbs2 \<equiv> ([(Loc 1 (Trg 1), 0, -1)]) :: ((2, 1) location \<times> _ \<times> _) buf"

abbreviation "c2 \<equiv> the (propagate_pointstamps my_summ' c1 cbs2)"

(* Implications at Trg of op2 is the same: abs_zmultiset (mset [0], mset []) *)
value "c_imp c2 (Loc 1 (Trg 1))"
(* But pts at Trg of op2 is now negative: abs_zmultiset (mset [], mset [0]) *)
value "c_pts c2 (Loc 1 (Trg 1))"

value "c_pts c2 (Loc 1 (Trg 1)) + c_pts c2 (Loc 0 (Src 1))"

(* op1 finally informs about the message that was already consumed by op2 *)
abbreviation "cbs3 \<equiv> ([(Loc 1 (Trg 1), 0, 1)]) :: ((2, 1) location \<times> _ \<times> _) buf"

abbreviation "c3 \<equiv> the (propagate_pointstamps my_summ' c2 cbs3)"

(* Implications at Trg of op2 is still the same: abs_zmultiset (mset [0], mset []) *)
value "(c_imp c3 (Loc 1 (Trg 1)))"

(* op1 drops its initial capability *)
abbreviation "cbs4 \<equiv> ([(Loc 0 (Src 1), 0, -1)]) :: ((2, 1) location \<times> _ \<times> _) buf"

abbreviation "c4 \<equiv> the (propagate_pointstamps my_summ' c3 cbs4)"

(* Implications at Trg of op2 is now empty (mset [0], mset [0]) *)
value "(c_imp c4 (Loc 1 (Trg 1)))"


value "conn my_summ' (Loc (0 :: 2) (Src (0 :: 1))) (nxt_l my_summ' (Loc (0 :: 2) (Src (0 :: 1))))" 

abbreviation "cbs2b \<equiv> ([(Loc 1 (Trg 1), 0, 1)]) :: ((2, 1) location \<times> _ \<times> _) buf"

abbreviation "c2b \<equiv> the (propagate_pointstamps my_summ' c1 cbs2b)"

abbreviation "cbs3b \<equiv> ([(Loc 0 (Src 1), 0, -1)]) :: ((2, 1) location \<times> _ \<times> _) buf"

abbreviation "c3b \<equiv> the (propagate_pointstamps my_summ' c2b cbs3b)"

value [GHC] "frontier (c_imp c3b (Loc 1 (Trg 1)))"  *)


abbreviation "nxt_l su l \<equiv> {l'. \<not> is_empty_antichain (su l l')}"

abbreviation "conn su l V \<equiv> \<Union> ((\<lambda> l'. (\<lambda> w. (l, w, l')) ` (set_antichain (su l l'))) ` V)"


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

lemma sum_gt_zeroD:
  "(0 :: int) < a + b \<Longrightarrow>
   0 < a \<or> 0 < b"
  by force

lemma sum_ge_zeroD:
  "(0 :: int) \<le> a + b \<Longrightarrow>
   0 \<le> a \<or> 0 \<le> b"
  by force

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

lemma zmset_map_one_zmset_of:
  "zmset (map (\<lambda>cap. (time cap, 1)) caps) = zmset_of (mset (map time caps))"
  apply (induct caps)
   apply (auto simp add: zcount_update_zmultiset zcount_zmset zmultiset_eq_iff)
  done

lemma zmset_of_eq_add:
  "zmset_of (mset (map time caps)) = A + B \<Longrightarrow>
   time x \<in> time ` set caps \<Longrightarrow> zcount A (time x) > 0 \<or> zcount B (time x) > 0"
  apply (simp add: zcount_zmset zmultiset_eq_iff)
  apply (induct caps)
   apply (auto 0 0 simp add: zcount_update_zmultiset zcount_zmset zmultiset_eq_iff split: if_splits)
   apply (smt (verit) of_nat_less_0_iff)
  apply (smt (verit, ccfv_SIG) count_image_mset_ge_count count_mset_gt_0 of_nat_eq_0_iff of_nat_less_0_iff verit_comp_simplify1(3))
  done

lemma zmset_of_eq_add_add:
  "zmset_of (mset (map time caps)) = A + B + C \<Longrightarrow>
   time x \<in> time ` set caps \<Longrightarrow> zcount A (time x) > 0 \<or> zcount B (time x) > 0 \<or> zcount C (time x) > 0"
  by (metis sum_gt_zeroD zcount_union zmset_of_eq_add)

lemma map_snd_concat[simp]:
  "map snd (concat (map (\<lambda>(p, t, m). [(x, t, m)]) ys)) = map snd ys"
  by (induct ys) auto

lemma map_snd_filter[simp]:
  "map snd (filter (\<lambda>(l', t, d). l = l') (map (\<lambda>(p, y). (l, y)) xs)) =
   map snd xs"
  by (induct xs) auto

lemma map_snd_filter_neg[simp]:
  "zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (map (\<lambda>(p, t, m). (Loc 1 (Trg 1), t, - m)) xs))) = {#}\<^sub>z - zmset (map snd xs)"
  apply (induct xs)
   apply (auto simp add: update_zmultiset_replicate)
  apply (metis diff_add_zmset semiring_norm(57))
  done

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

definition "changes_above_impl f chgs = (\<forall>(l, t, d)\<in>set chgs. \<exists>t'. t' \<in>\<^sub>A f l \<and> t' \<le> t)"

(* lemma changes_above_impl_unionI:
  "changes_above_impl cgs1 impls \<Longrightarrow>
   changes_above_impl cgs2 impls \<Longrightarrow>
   set cgs3 \<subseteq> set cgs1 \<union> set cgs2 \<Longrightarrow>
   changes_above_impl cgs3 impls"
  unfolding changes_above_impl_def
  by blast *)

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

definition "input_cap inps n = (if inps 0 = LNil then {#}\<^sub>z else {# n 0 #}\<^sub>z)"


(* FIXME: move me *)
lemma replicate_mset_length[simp]:
  "replicate_mset (length batch) (n 1) = {#n 1. x \<in># mset batch#}"
  unfolding replicate_mset_def
  by (induct batch) auto

lemma zcount_zmset_all_neg:
  "(\<forall> t \<in> snd ` snd ` set xs. t \<ge> 0) \<Longrightarrow>
   zcount (zmset (map snd (filter (\<lambda>(l', t, d). l = l') (map (\<lambda>(p, t, m). (l, t, - m)) xs)))) t \<le> 0"
  apply (induct xs rule: rev_induct)
   apply (auto simp add: zcount_update_zmultiset)
  done

lemma outpu_produce:
  "outpu (produce os1 (Cap t 1) (a # xs)) 1 = outpu os1 1 @ map (\<lambda> x. (x, t)) (a # xs)"
  unfolding produce_def
  apply auto
  done

definition "below_n A n = (\<forall> t. zcount A t > 0 \<longrightarrow> t \<le> n)"

lemma neg_minus_single[simp]:
  "- A - {#x#}\<^sub>z = - add_zmset x A"
  by (metis arith_simps(56) diff_add_zmset_swap minus_diff_eq)

lemma zmultiset_move_add_other_side:
  "(A :: _ zmultiset) + B = C \<longleftrightarrow> A = C - B"
  apply (simp add: zmultiset_eq_iff)
  apply auto
  apply (smt (verit))
  done

lemma zcount_gt_0_in_set:
  "0 < zcount (zmset (map snd (filter (\<lambda>(l', t, d). l = l') xs))) t \<Longrightarrow> \<exists>m. (l, t, m) \<in> set xs \<and> 0 < m"
  apply (induct xs)
   apply (simp_all split: if_splits prod.splits)
   apply (smt (verit, best) list.distinct(1) list_tail_coinc zcount_update_zmultiset zmset.elims)
  apply blast
  done

lemma zcount_gt_0_in_set_2:
  "0 < zcount (zmset (map snd xs)) t \<Longrightarrow> \<exists>m. (1 :: 1, t, m) \<in> set xs \<and> 0 < m"
  apply (induct xs)
   apply (auto simp add: zcount_update_zmultiset split: if_splits prod.splits)
  apply fastforce
  done

lemma change_multiplicities_appen_cong:
  "change_multiplicities su ys1 = change_multiplicities su ys2 \<Longrightarrow>
   change_multiplicities su (xs @ ys1) = change_multiplicities su (xs @ ys2)"
  by (simp add: change_multiplicities_append_comp)

(*
   changes_above_impl (dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg)) (extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2)  \<Longrightarrow>
   dataflow_topology.implied_frontier_alt my_summ (+) c (Loc 1 (Trg 0)) \<le> frontier (input_cap inps n) \<Longrightarrow>
*)

lemma
  \<open>summ sg = my_summ \<Longrightarrow>
   edges sg = (\<lambda> l. if l = Loc 0 (Src 1) then [Loc 1 (Trg 1)] else []) \<Longrightarrow>
   consu os1 = [] \<Longrightarrow>
   xs 0 = outpu os2 0 \<Longrightarrow>
   ys 0 = max_from_buf caps buf2 ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0) \<Longrightarrow>
   (\<forall> x \<in> set (buf1 (Inr (1, 0))). is_Inr x) \<Longrightarrow>
   sorted (map time caps) \<Longrightarrow>
   (\<forall>t. 0 \<le> zcount (zmset (map snd (consu os2))) t) \<Longrightarrow>

   obtain_progress os1 = (a, st1) \<Longrightarrow>
   obtain_progress os2 = (b, st2) \<Longrightarrow>
   c = change_multiplicities (summ sg) (extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2) (pt_tr sg) \<Longrightarrow>
   c_pts c (Loc 1 (Trg 0)) = zmset_of (mset (map snd ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0))) \<Longrightarrow>
   c_pts c (Loc 0 (Src 0)) = input_cap inps n \<Longrightarrow>
   c_pts c (Loc 0 (Trg 1)) = {#}\<^sub>z \<Longrightarrow>
   c_pts c (Loc 1 (Src 0)) = zmset_of (mset (map time caps)) \<Longrightarrow>

   front os2 0 \<le> frontier (c_imp (pt_tr sg) (Loc 1 (Trg 0))) \<Longrightarrow>
   (\<forall> l. frontier (c_imp (pt_tr sg) l) \<le> dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg) l) \<Longrightarrow>
   (\<forall> l. dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg) l \<le> dataflow_topology.implied_frontier_alt my_summ (+) (change_multiplicities (summ sg) (extract_progress 0 (edges sg) st1) (pt_tr sg)) l) \<Longrightarrow>
   (\<forall> l. dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg) l \<le> dataflow_topology.implied_frontier_alt my_summ (+) (change_multiplicities (summ sg) (extract_progress 1 (edges sg) st2) (pt_tr sg)) l) \<Longrightarrow>

   (\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). frontier_less_equal (dataflow_topology.implied_frontier_alt my_summ (+) c (Loc 1 (Trg 0))) t) \<Longrightarrow>

   dataflow_topology.inv_imps_work_sum (summ sg) (-+-) (pt_tr sg) \<Longrightarrow>
   dataflow_topology.inv_implications_nonneg (pt_tr sg) \<Longrightarrow>
   dataflow_topology.inv_imp_plus_work_nonneg (pt_tr sg) \<Longrightarrow>
   changes_non_zero (extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2) \<Longrightarrow>

   sorted_wrt (\<lambda> (_, x) (_, y). x \<le> y) ((map projr (buf1 (Inr (1, 1)))) @ (outpu os1 0)) \<Longrightarrow>
   (\<forall> t' p. Cap t' p \<in> set caps \<longrightarrow> t' < n 0) \<Longrightarrow>
   (\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). t < n 0) \<Longrightarrow>
   (\<forall> t\<ge>n 0. buf2 (Cap t 1) = []) \<Longrightarrow>

   dataflow_op sg (inp_m_top os1 (\<lambda> p. n p) inps buf1 os2 buf2 caps) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. xs p @@- ys p @@- lconcat (lmap (\<lambda> (xs, t). case xs of [] \<Rightarrow> [] | _ \<Rightarrow> [(Max (set xs), t)]) (lzip (inps p) (iterates ((+) 1) (n p))))))\<close>
proof (coinduction arbitrary: xs ys os1 os2 n caps buf1 buf2 inps sg a b c st1 st2 rule: weakBisimWeakUptoBisimCong)
  case SIM1
  show ?case (is "wsim ((~) OO \<U> ?R OO (\<approx>)) ?op1 ?op2")
  proof -
    define R where "R = ?R"
    from SIM1 show ?thesis unfolding R_def[symmetric]
      apply -
      unfolding wsim_def
      apply (intro allI conjI impI)
      subgoal premises prems for io op1'
        using prems(29) apply -
        apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin?)
                   apply simp_all
                   prefer 8
        subgoal 
          unfolding R_def
          apply simp
          using prems(4,5) apply -
          apply (intro exI conjI[rotated])
           apply (intro relcomppI)
             apply (rule bisim_refl)
            defer
            apply (rule wbisim_refl)
           defer
           apply (rule wb_upto_b_base)
           apply (intro conjI exI)
                              apply (rule refl)+
          subgoal using prems(1) by simp
          subgoal using prems(2) by simp
          subgoal using prems(3) by simp
                              apply (rule refl)+
          subgoal using prems(6) by simp
          subgoal using prems(7) apply -
            using sorted_filter by blast
          subgoal using prems(8) by simp
          subgoal using prems(9,2,3,9,10,11,12) 
            by (auto simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13)
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14,15) apply -
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            subgoal premises
              apply (induct caps)
               apply auto
              apply (metis Num.of_nat_simps(1) One_nat_def insert_Diff_zmset int_ops(2) semiring_norm(52) union_zmset_add_zmset_right update_zmultiset_simps(1,3))
              done
            done
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(1,10,9,2,3,9,10,11,12,13,14,15,18) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(1,10,9,2,3,9,10,11,12,13,14,15,19) apply -
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            subgoal for l
              apply (drule spec[of _ l])
              apply (rule Orderings.preorder_class.order_trans)
               apply assumption
              subgoal premises prems2
                apply (subst (1 2) dataflow_topology.implied_frontier_alt_def)
                 apply (simp_all add: comp_def)
                apply (intro impI conjI)
                subgoal
                  by (auto simp add: c_pts_change_multiplicities intro!: arg_cong[where f=frontier])
                subgoal
                  by (auto simp add: c_pts_change_multiplicities intro!: arg_cong[where f=frontier])
                subgoal
                  by (auto simp add: c_pts_change_multiplicities intro!: arg_cong[where f=frontier])
                subgoal
                  by (auto simp add: c_pts_change_multiplicities intro!: arg_cong[where f=frontier])
                subgoal
                  by (auto simp add: c_pts_change_multiplicities intro!: arg_cong[where f=frontier])
                subgoal
                  using prems2(9) apply -
                  apply (auto simp add: c_pts_change_multiplicities intro!: arg_cong[where f=frontier])
                  subgoal 
                    apply (auto simp flip: add.assoc simp add: comp_def in_frontier_iff simp flip: Antichain.member_antichain.rep_eq)
                    apply (rule frontier_add_le_gen)
                       apply simp_all
                     apply (metis (no_types, opaque_lifting) add_diff_cancel_left' frontier_below_eq_frontier_minus frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus)
                    apply (rule frontier_add_le_gen)
                       apply simp_all
                     apply (rule Orderings.preorder_class.order_trans)
                      apply (rule frontier_below_eq_frontier_plus_neg[where M="zmset (map (\<lambda>x. (time x, - 1)) (filter (\<lambda>cap. \<not> frontier_less_equal (front os2 1) (time cap)) caps))"])
                    subgoal premises
                      apply (auto simp: zcount_zmset)
                      apply (induct caps)
                       apply auto
                      using dual_order.trans le_numeral_extra(1) apply blast
                      done
                    subgoal              
                      by (auto simp add: c_pts_change_multiplicities intro!: arg_cong[where f=frontier])
                    subgoal
                      by (metis Groups.add_ac(2) add_empty_zmultiset(1) frontier_below_eq_frontier_plus_pos frontier_idempotent prems2(8) trivial_dataflow_topology_interpretation.zmset_frontier_empty zcount_zmset_of_nonneg)
                    done
                  done
                subgoal
                  by (auto simp add: c_pts_change_multiplicities intro!: arg_cong[where f=frontier])
                done
              done
            done
          subgoal 
            apply (subst (1 2) dataflow_topology.implied_frontier_alt_def)
             apply simp
            using prems(1,10,9,2,3,9,10,11,12,13,14,15,20) apply -
            apply (subst (asm) (1) dataflow_topology.implied_frontier_alt_def)
             apply simp
            apply simp
            apply (intro allI impI conjI)
            subgoal for a b
              unfolding extract_progress_def frontier_less_equal_def
              apply (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              subgoal
                by blast
              done
            subgoal for a b
              unfolding extract_progress_def frontier_less_equal_def by
                (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          subgoal using prems(21) by simp
          subgoal using prems(22) by simp
          subgoal using prems(23) by simp
          subgoal using prems(1,10,9,2,3,9,10,11,12,13,14,15,24) apply -
            apply auto
            apply hypsubst_thin
            unfolding changes_non_zero_def extract_progress_def comp_def
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply force
            done
          subgoal using prems(25) by simp
          subgoal using prems(26) by simp
          subgoal using prems(27) by simp
          subgoal using prems(28) by simp
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
                apply (subgoal_tac "caps = filter (\<lambda>cap. \<not>  frontier_less_equal (front os2 1) (time cap) ) caps @ filter (\<lambda>cap. frontier_less_equal (front os2 1) (time cap) ) caps")
                subgoal premises prems2
                  apply (subst prems2(1))
                  apply (subst max_from_caps_buf_append)
                  apply (rule arg_cong2[where f=append])
                  subgoal
                    unfolding max_from_caps_buf_def
                    apply (rule map_cong)
                     apply (rule refl)
                    apply simp
                    apply (rule Max_eq_if)
                       apply auto
                    subgoal for x a
                      unfolding list_to_buf_def BULK_BENQ_def
                      apply auto              
                      subgoal
                        apply (subgoal_tac "(\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). frontier_less_equal (front os2 0) t)")
                        subgoal
                          apply (drule bspec[of _ _ "(a, time x)"])
                          subgoal 
                            by (metis UnI1 fst_eqD map_in_setD set_map)
                          apply auto
                          done
                        subgoal
                          apply safe
                          subgoal
                            apply (rule frontier_less_equal_le_trans)
                            using prems(19,20) apply fast
                            using prems(16,17,18,19,20) apply -
                            find_theorems "_ \<le> frontier ("

end
                            done
                          subgoal
                            apply (rule frontier_less_equal_le_trans)
                            using prems(19) apply fast
                            using prems(16,17,18,19) apply -
                            apply (meson order.trans)
                            done
                          done
                        done
                      subgoal
                        apply (subgoal_tac "(\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). frontier_less_equal (front os2 0) t)")
                        subgoal
                          apply (drule bspec[of _ _ "(a, time x)"])
                           apply auto
                          done
                        subgoal
                          apply safe
                          subgoal
                            apply (rule frontier_less_equal_le_trans)
                            using prems(19) apply fast
                            using prems(16,17,18,19) apply -
                            apply (meson order.trans)
                            done
                          subgoal
                            apply (rule frontier_less_equal_le_trans)
                            using prems(19) apply fast
                            using prems(16,17,18,19) apply -
                            apply (meson order.trans)
                            done
                          done
                        done
                      done
                    subgoal
                      unfolding max_from_caps_buf_def list_to_buf_def BULK_BENQ_def
                      apply auto
                      done
                    done
                  subgoal
                    unfolding max_from_caps_buf_def list_to_buf_def BULK_BENQ_def
                    apply auto
                    done
                  done
                subgoal
                  using prems(7) sorted_caps_append by blast
                done
              subgoal
                unfolding max_from_caps_buf_def list_to_buf_def BULK_BENQ_def
                apply (rule map_cong)
                subgoal
                  apply (rule arg_cong2[where f=append])
                  subgoal
                    apply (subgoal_tac "(\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). frontier_less_equal (front os2 0) t)")
                    subgoal
                      apply (simp add: comp_def)
                      apply (rule rmdups_cong)
                      apply (auto split: prod.splits)
                      done
                    subgoal
                      apply safe
                      subgoal
                        apply (rule frontier_less_equal_le_trans)
                        using prems(19) apply fast
                        using prems(16,17,18,19) apply -
                        apply (meson order.trans)
                        done
                      subgoal
                        apply (rule frontier_less_equal_le_trans)
                        using prems(19) apply fast
                        using prems(16,17,18,19) apply -
                        apply (meson order.trans)
                        done
                      done
                    done
                  subgoal
                    apply (subgoal_tac "(\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). frontier_less_equal (front os2 0) t)")
                    subgoal
                      apply (simp add: comp_def)
                      apply (rule rmdups_cong)
                      apply (auto split: prod.splits)
                      apply fastforce
                      done
                    subgoal
                      apply safe
                      subgoal
                        apply (rule frontier_less_equal_le_trans)
                        using prems(19) apply fast
                        using prems(16,17,18,19) apply -
                        apply (meson order.trans)
                        done
                      subgoal
                        apply (rule frontier_less_equal_le_trans)
                        using prems(19) apply fast
                        using prems(16,17,18,19) apply -
                        apply (meson order.trans)
                        done
                      done
                    done
                  done
                subgoal
                  apply auto
                  subgoal
                    apply (subgoal_tac "(\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). frontier_less_equal (front os2 0) t)")
                    subgoal
                      apply (rule Max_eq_if)
                         apply (auto split: prod.splits)
                      apply fastforce
                      done
                    subgoal
                      apply safe
                      subgoal
                        apply (rule frontier_less_equal_le_trans)
                        using prems(19) apply fast
                        using prems(16,17,18,19) apply -
                        apply (meson order.trans)
                        done
                      subgoal
                        apply (rule frontier_less_equal_le_trans)
                        using prems(19) apply fast
                        using prems(16,17,18,19) apply -
                        apply (meson order.trans)
                        done
                      done
                    done
                  subgoal
                    apply (subgoal_tac "(\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). frontier_less_equal (front os2 0) t)")
                    subgoal
                      apply (rule Max_eq_if)
                         apply (auto split: prod.splits)
                      done
                    subgoal
                      apply safe
                      subgoal
                        apply (rule frontier_less_equal_le_trans)
                        using prems(19) apply fast
                        using prems(16,17,18,19) apply -
                        apply (meson order.trans)
                        done
                      subgoal
                        apply (rule frontier_less_equal_le_trans)
                        using prems(19) apply fast
                        using prems(16,17,18,19) apply -
                        apply (meson order.trans)
                        done
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
          using prems(4,5) apply -
          apply (intro exI conjI[rotated])
           apply (intro relcomppI)
             apply (rule bisim_refl)
            defer
            apply (rule wbisim_refl)
           defer
           apply (rule wb_upto_b_base)
           apply (intro conjI exI)
                              apply (rule refl)+
          subgoal using prems(1) by (auto 0 0 simp add: propagate_pointstamps_def c_pts_change_multiplicities extract_progress_def change_multiplicities_append_comp split: option.splits if_splits dest!: propagate_all_preserves_c_pts; hypsubst_thin?)
          subgoal using prems(2) by (auto 0 0 simp add: propagate_pointstamps_def c_pts_change_multiplicities extract_progress_def change_multiplicities_append_comp split: option.splits if_splits dest!: propagate_all_preserves_c_pts; hypsubst_thin?)
          subgoal using prems(3) by (auto 0 0 simp add: propagate_pointstamps_def c_pts_change_multiplicities extract_progress_def change_multiplicities_append_comp split: option.splits if_splits dest!: propagate_all_preserves_c_pts; hypsubst_thin?)
                              apply (rule refl)+
          subgoal using prems(6) by simp
          subgoal using prems(7) apply -
            using sorted_filter by blast
          subgoal using prems(8) by simp
          subgoal using prems(2,3,9,10,11,12,13) by (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
          subgoal using prems(2,3,9,10,11,12,13,14) by (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
          subgoal using prems(2,3,9,10,11,12,13,14) by (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
          subgoal
            using prems(1,2,3,9,10,11) prems(15)[symmetric] by (auto 0 0 simp add: c_pts_change_multiplicities extract_progress_def change_multiplicities_append_comp split: option.splits if_splits dest!: propagate_all_preserves_c_pts; hypsubst_thin?)
          subgoal by (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
          subgoal using prems(1,2,3,9,10,11,12,17) apply -
            apply (intro allI)
            subgoal for l
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            apply (drule propagate_all_frontier_c_imp_correctness[where loc=l])
                 apply simp_all
            using prems(20) apply simp
            using prems(21) apply simp
            using prems(22) apply simp
            done
          done
          subgoal using prems(1,2,3,9,10,11,12,18) apply -
            apply (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
                apply (subst (1 2) dataflow_topology.implied_frontier_alt_def)
            apply simp
                apply (subst (asm) (1 2) dataflow_topology.implied_frontier_alt_def)
             apply simp
            apply (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            done
          subgoal using prems(1,2,3,9,10,11,12,19) apply -
            apply (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
    subgoal
              apply (drule spec2)
              apply (elim conjE)
              apply (drule mp)
              apply blast
              apply auto
              unfolding frontier_less_equal_iff
              apply (rule Orderings.preorder_class.order_trans[rotated])
              apply assumption
              apply (subst (1 2) dataflow_topology.implied_frontier_alt_def)
              apply simp_all
              apply (auto 0 0 simp flip: mset_pos_neg_partition simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              done
 subgoal
              apply (drule spec2)
              apply (elim conjE)
              apply (drule mp)
              back
              apply blast
              apply auto
              unfolding frontier_less_equal_iff
              apply (rule Orderings.preorder_class.order_trans[rotated])
              apply assumption
              apply (subst (1 2) dataflow_topology.implied_frontier_alt_def)
              apply simp_all
              apply (auto 0 0 simp flip: mset_pos_neg_partition simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              done
            done
          subgoal
using prems(1,2,3,9,10,11,12,17) apply -
              apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            apply (drule propagate_all_frontier_c_imp_correctness[where loc=l])
                 apply simp_all
            using prems(20) apply simp
            using prems(21) apply simp
            using prems(22) apply simp
            done
          subgoal
using prems(1,2,3,9,10,11,12,17) apply -
              apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            apply (drule propagate_all_frontier_c_imp_correctness[where loc=l])
                 apply simp_all
            using prems(20) apply simp
            using prems(21) apply simp
            using prems(22) apply simp
            done
          subgoal
            using prems(1,2,3,9,10,11,12,17) apply -
              apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            apply (drule propagate_all_frontier_c_imp_correctness[where loc=l])
                 apply simp_all
            using prems(20) apply simp
            using prems(21) apply simp
            using prems(22) apply simp
            done
          subgoal
            using prems(1,2,3,9,10,11,12,23) apply -
              apply (auto 0 0 simp flip: mset_pos_neg_partition simp add: changes_non_zero_def propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            done
          subgoal
            using prems(24) by auto
          subgoal
            using prems(25) by auto
          subgoal
            using prems(26) by auto
          subgoal
            using prems(27) by auto
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
          done
        done
        subgoal
          by (auto simp add: comp_def)
        done
      done
             prefer 9
  subgoal 
          unfolding R_def
          apply simp
          using prems(4,5) apply -
          apply (intro exI conjI[rotated])
           apply (intro relcomppI)
             apply (rule bisim_refl)
            defer
            apply (rule wbisim_refl)
           defer
           apply (rule wb_upto_b_base)
           apply (intro conjI exI)
                              apply (rule refl)+
          subgoal using prems(1) by simp
          subgoal using prems(2) by simp
          subgoal using prems(3) by simp
                              apply (rule refl)+
          subgoal using prems(6) by simp
          subgoal using prems(7) apply -
            using sorted_filter by blast
          subgoal using prems(8) by simp
          subgoal using prems(9,2,3,9,10,11,12) apply -
            by (auto simp add: diff_add_eq extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13)
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14,15) apply -
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(11,17,18) apply -
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            subgoal for l
              apply (drule spec[of _ l])+
              

              find_theorems "_ \<le> frontier (_ + _)"

end
               apply simp
              subgoal premises prems2
            apply (subst (1 2) dataflow_topology.implied_frontier_alt_def)
                 apply simp_all
                apply (intro impI allI conjI)
                subgoal
                  using prems(1,12,13,14,15) by simp
                subgoal
                  using prems(1,12,13,14,15) by simp
                subgoal
                  using prems(1,12,13,14,15) by simp
                subgoal
                  apply (drule sym)
                  using prems(1,12,13,14,15) apply simp
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)


end
          subgoal using prems(1,2,3,4,5,9,10,11,18) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(1,2,3,4,5,9,10,11,19) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(20) by simp
          subgoal using prems(21) by simp
          subgoal using prems(22) by simp
          subgoal 
            using prems(1,2,4,5,9,10,11,23) 
            by (auto simp add: extract_progress_def changes_non_zero_def)
          subgoal using prems(24) by simp
          subgoal using prems(25) by simp
          subgoal using prems(26) by simp
          subgoal using prems(27) by simp
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
          done
        done
        subgoal
          by (auto simp add: comp_def)
        done
      done

end
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
  subgoal for n' t
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
      apply (auto simp add: update_zmultiset_replicate comp_def filter_empty_conv c_pts_change_multiplicities)
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
        apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
        apply (auto simp add: BHD_def update_zmultiset_replicate comp_def filter_empty_conv c_pts_change_multiplicities)
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
      apply (auto 0 0 simp add: BHD_def extract_progress_def update_zmultiset_replicate change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      done
    subgoal
      using prems(5,6,7,8,14,16) 
      apply simp
      apply (auto 0 0 simp add: BHD_def extract_progress_def update_zmultiset_replicate change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      done         
    using prems(17) apply simp
    using prems(18) apply simp
    using prems(19) apply simp
    using prems(20) apply simp
    using prems(21) apply simp
    using prems(22) apply simp
    using prems(23) apply simp
    subgoal
      unfolding BTL_def
      using prems(24) apply clarsimp
      apply (metis (no_types, lifting) image_iff in_set_tlD)
      done
    subgoal 
      using prems(25)
      unfolding BENQ_def BHD_def BTL_def
      apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
      done
    subgoal
      apply simp
      using prems(26) prems(5,6,7,8,14,16,10,9)
      unfolding BENQ_def BHD_def BTL_def input_cap_def
      apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
      apply (auto 0 0 simp del: neg_minus_single simp add: update_zmultiset_replicate extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      subgoal premises prems2
        using prems2(4,6) apply -
        apply (subst add_zmset_add_single)
        apply (subst add_zmset_add_single)
        apply (subst (asm) add_zmset_add_single)
        apply (subgoal_tac
            "c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg))) + zmset (map snd (produ os1)) - (zmset (map snd (consu os2)) + {#t#}\<^sub>z) + {#n 1#}\<^sub>z =
    c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg))) + zmset (map snd (produ os1)) - zmset (map snd (consu os2)) + {#n 1#}\<^sub>z - {#t#}\<^sub>z")
        defer
        subgoal
          by (metis diff_add_zmset uminus_add_add_uminus)
        subgoal
          apply (simp only: )
          apply auto
          apply (metis add.commute add_zmset_add_single frontier_below_eq_frontier_plus_pos zcount_zmset_of_nonneg)
          done
        done
      done
    subgoal
      apply simp
      using prems(27) prems(5,6,7,8,14,16,10,9) 
      unfolding BENQ_def BHD_def BTL_def input_cap_def
      apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
      done
    using prems(28) apply simp
    subgoal
      using prems(29) 
      unfolding BENQ_def BHD_def BTL_def input_cap_def
      by (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
    subgoal
      using prems(28,30) apply simp
      unfolding BENQ_def
      apply auto
      done
    using prems(31) apply simp
    using prems(32) apply simp
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
      apply (auto simp add: update_zmultiset_replicate comp_def filter_empty_conv c_pts_change_multiplicities)
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
        apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
        apply (auto simp add: BHD_def update_zmultiset_replicate comp_def filter_empty_conv c_pts_change_multiplicities)
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
      using prems(5,6,7,8,14,16,15) 
      apply simp
      apply (auto 0 0 simp add: zcount_update_zmultiset extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      done
    subgoal
      using prems(5,6,7,8,14,16) 
      apply simp
      apply (auto 0 0 simp add: zcount_update_zmultiset extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      done
    using prems(17) apply simp
    using prems(18) apply simp
    using prems(19) apply simp
    using prems(20) apply simp
    using prems(21) apply simp
    using prems(22) apply simp
    using prems(23) apply simp
    subgoal premises prems2
      using prems2(1,2,4,7) prems2(3)[symmetric] prems(24) prems(25) prems(4) apply -
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
      using prems(25)
      unfolding BENQ_def BHD_def BTL_def
      apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
      done
    subgoal
      apply simp
      using prems(26) prems(5,6,7,8,14,16,10,9)
      unfolding BENQ_def BHD_def BTL_def input_cap_def
      apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
      apply (auto 0 0 simp del: neg_minus_single simp add: update_zmultiset_replicate extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      subgoal premises prems2
        using prems2(4,6) apply -
        apply (subst add_zmset_add_single)
        apply (subst add_zmset_add_single)
        apply (subst (asm) add_zmset_add_single)
        apply (subgoal_tac
            "c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg))) + zmset (map snd (produ os1)) - (zmset (map snd (consu os2)) + {#t#}\<^sub>z) =
    c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg))) + zmset (map snd (produ os1)) - (zmset (map snd (consu os2))) - {#t#}\<^sub>z")
        defer
        subgoal
          using diff_add_zmset by blast
        subgoal
          apply (simp only: )
          apply auto
          apply (metis (lifting) add.commute add_zmset_add_single frontier_below_eq_frontier_plus_pos zcount_zmset_of_nonneg)
          done
        done
      done
    subgoal
      apply simp
      using prems(27) prems(5,6,7,8,14,16,10,9) 
      unfolding BENQ_def BHD_def BTL_def input_cap_def
      apply (cases "buf1 (Inr (1, 1))"; simp split: prod.splits)
      done
    subgoal premises prems2
      using prems2(1,2,4,7) prems2(3)[symmetric] prems(24) prems(25,26,28,4,29) apply -
      unfolding BENQ_def BHD_def BTL_def input_cap_def
      apply (cases "buf1 (Inr (1, 1))"; auto 0 0 split: prod.splits)
      done
    subgoal premises prems2
      using prems2(1,2,4,7) prems2(3)[symmetric] prems(25) prems(26,29,4,30) apply -
      unfolding BENQ_def BHD_def BTL_def input_cap_def
      apply (cases "buf1 (Inr (1, 1))"; auto 0 0 split: prod.splits)
      done
    subgoal
      unfolding BENQ_def BHD_def
      using prems(29,30,31) apply -
      apply (cases "buf1 (Inr (1, 1))"; auto 0 0 split: prod.splits)
      apply auto
      done
    using prems(31) apply simp
    using prems(32) apply simp
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
            using prems(24) apply -
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
  subgoal for batch
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
    using prems(3) apply simp
    using prems(4) apply simp
    subgoal
      apply simp
      using prems(5,6,7,8, 14) prems(9)[symmetric] apply -
      apply (simp add: change_multiplicities_append_comp comp_def)
      apply (elim conjE)
      apply hypsubst_thin
      unfolding extract_progress_def
      apply (auto simp flip: add.assoc simp add: zmset_of_plus comp_def filter_empty_conv c_pts_change_multiplicities produce_def dest!: propagate_all_preserves_c_pts)
      done
    subgoal
      using prems(5,6,7,8,14) prems(10)  apply -
      apply (auto simp add: input_cap_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      unfolding extract_progress_def
      apply (simp add:  comp_def produce_def)
      apply (subgoal_tac "update_zmultiset {#}\<^sub>z (n 1) (- 1) + {#n 1#}\<^sub>z = {#}\<^sub>z")
      apply (metis (no_types, lifting) Max_top.update_zmultiset_plus arith_extra_simps(5,6) update_zmultiset_plus_comm)
      subgoal premises
        using add_cancel_right_right by (fastforce simp add: update_zmultiset_replicate)
      done
    subgoal
      apply simp
      apply (cases batch)
      subgoal
        using prems(5,6,7,8,14,27) prems(9,10)[symmetric] apply simp
        apply (rule Orderings.preorder_class.order_trans)
        apply (rule prems(11)[simplified])
        apply simp
        apply hypsubst_thin
        apply (auto 0 0 simp flip: Multiset.union_assoc simp add: below_n_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
        apply (rule Orderings.preorder_class.order_trans)
        apply (rule frontier_below_eq_frontier_minus[where M="{#n 1#}\<^sub>z"])
        subgoal premises
          by simp
        subgoal premises
          apply (rule Orderings.preorder_class.eq_refl)
          apply (rule arg_cong[where f=frontier])
          apply auto
          done
        done
      subgoal for x batch'
        using prems(5,6,7,8,14,26,10) prems(9)[symmetric] apply simp
        apply (rule Orderings.preorder_class.order_trans)
        apply (rule prems(11)[simplified])
        apply simp
        apply hypsubst_thin
        apply (auto 0 0 simp flip: Int.Suc_nat_eq_nat_zadd1 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
        subgoal premises prems2
          using prems2(7) apply -
          apply (rule Orderings.preorder_class.order_trans)
          apply (rule frontie_add_zmset_add[where xs=batch'])
          apply simp_all
          apply (rule Orderings.preorder_class.eq_refl)
          apply (rule arg_cong[where f=frontier])
          apply auto
          done
        done
      done
    subgoal
      using prems(12) by simp
    using prems(13) apply simp
    using prems(14) apply simp
    using prems(15) apply simp
    subgoal
      using prems(5,6,7,8,14,16) 
      apply simp
      apply (auto 0 0 simp add: produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      done
    subgoal
      using prems(17) by (auto 0 0 simp add: produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)         
    using prems(19) apply simp
    using prems(20) apply simp
    using prems(21) apply simp
    using prems(22) apply simp
    using prems(23) apply simp
    subgoal premises prems2
      using prems2(2,5) prems(24,25,26,10,5,6,7,8,14,16,10,4,28) prems(9)[symmetric] apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: if_splits option.splits; hypsubst_thin?)
      using nat_less_le apply blast       
      done
    subgoal
      using prems(25,28,29) 
      apply (auto 0 0 simp add: sorted_wrt_append input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: if_splits prod.splits option.splits; hypsubst_thin?)
      apply (smt (verit, best) case_prod_conv le_refl sorted_wrt_map_mono sorted_wrt_true)
      apply (meson nat_less_le)
      apply (metis imageI nat_less_le)
      done
    apply (simp add: input_cap_def)
    apply (simp add: input_cap_def)
    using prems(28) apply force
    subgoal
      using prems(29) 
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply fastforce+
      done
    subgoal
      using prems(29,28,30) by auto
    subgoal
      using prems(31) apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply (rule frontier_le_add)
      apply assumption
      using prems(5,6,7,8,14,16,19,27,10,9) apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply (rule Orderings.preorder_class.order_trans)
      apply assumption
      back
      apply auto
      done
    subgoal
      using prems(32) apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply (smt (verit) Signed_Multiset.multi_member_split add_zmset_remove_trivial basic_trans_rules(23) frontier_add_zmset order_refl)
      done
    subgoal
      apply (simp add: comp_def)
      apply (rule rtranclp_intros_1)
      apply (rule arg_cong3[where f=map_op])
      apply simp_all
      apply (rule arg_cong[where f=source_op])
      apply (rule ext)
      apply (subst iterates.code)
      apply simp
      apply (cases batch)
      apply (simp_all add: lshift_assoc)
      apply (rule arg_cong2[where f=lshift])
      apply simp_all
      subgoal
        unfolding max_from_caps_buf_def map_is_Nil_conv append_is_Nil_conv produce_def
        by simp
      subgoal premises prems2 for a list
        using prems2(2,5,6) prems(28,29) apply -
        apply (simp flip: lshift_assoc)
        apply (rule arg_cong2[where f=lshift])
        apply simp
        apply (subgoal_tac "rmdups (set caps \<union> (\<lambda>x. case projr x of (x, t) \<Rightarrow> Cap t 1) ` set (buf1 (Inr (1, 1)))) (map (\<lambda>(x, t). Cap t 1) (outpu (produce os1 (Cap (n 1) 1) (a # list)) 1)) = rmdups (set caps \<union> (\<lambda>x. case projr x of (x, t) \<Rightarrow> Cap t 1) ` set (buf1 (Inr (1, 1)))) (map (\<lambda>(x, t). Cap t 1) (outpu os1 1)) @ [Cap (n 0) 1]")
        subgoal
          apply (auto simp add:  max_from_caps_buf_append list_to_buf_def simp flip: snoc_shift lshift_assoc split: if_splits)
          apply (rule arg_cong2[where f=append])
          subgoal
            unfolding outpu_produce
            apply (auto split: if_splits)
            subgoal for x
              apply (cases x)
              apply auto
              subgoal for a
                apply (drule spec[of _ a])
                apply (drule spec[of _ "n 0"])
                back
                apply (elim conjE)
                apply (drule mp)
                apply force
                apply auto
                done
              done
            subgoal
              unfolding max_from_caps_buf_def BULK_BENQ_def
              apply (rule List.List.list.map_cong)
              apply auto
              apply (rule Lattices_Big.linorder_class.Max_eq_if)
              subgoal
                by (auto split: if_splits)
              subgoal
                by (auto split: if_splits)
              subgoal
                apply (clarsimp split: if_splits)
                apply fast+
                done
              subgoal
                apply (auto 0 0 simp add: set_rmdups split: if_splits)
                apply (metis capability.exhaust capability.sel(1) num1_eq1)+
                done
              done
            done
          apply (rule arg_cong2[where f=append])
          subgoal
            unfolding outpu_produce
            apply (auto split: if_splits)
            subgoal for x
              apply (cases x)
              apply auto
              subgoal for a
                apply (drule spec[of _ a])
                apply (drule spec[of _ "n 0"])
                back
                apply (elim conjE)
                apply (drule mp)
                apply force
                apply auto
                done
              done
            subgoal
              unfolding max_from_caps_buf_def BULK_BENQ_def
              apply (rule List.List.list.map_cong)
              apply auto
              apply (rule Lattices_Big.linorder_class.Max_eq_if)
              subgoal
                by (auto split: if_splits)
              subgoal
                by (auto split: if_splits)
              subgoal
                apply (clarsimp split: if_splits)
                apply fast+
                done
              subgoal for z
                apply (cases z)
                apply (auto 0 0 simp add: set_rmdups split: if_splits)
                done
              done
            done
          apply (rule arg_cong2[where f=append])
          subgoal
            unfolding outpu_produce
            apply (auto split: if_splits)
            subgoal for x
              apply (cases x)
              apply auto
              subgoal for a
                apply (drule spec[of _ a])
                apply (drule spec[of _ "n 0"])
                back
                apply (elim conjE)
                apply (drule mp)
                apply force
                apply auto
                done
              done
            subgoal
              unfolding max_from_caps_buf_def BULK_BENQ_def
              apply (rule List.List.list.map_cong)
              apply auto
              apply (rule Lattices_Big.linorder_class.Max_eq_if)
              subgoal
                by (auto split: if_splits)
              subgoal
                by (auto split: if_splits)
              subgoal
                apply (clarsimp split: if_splits)
                apply fast+
                done
              subgoal for z
                apply (cases z)
                apply (auto 0 0 simp add: set_rmdups split: if_splits)
                done
              done
            done
          subgoal premises prems3
            unfolding max_from_caps_buf_def produce_def BULK_BENQ_def
            apply auto
            apply (rule Lattices_Big.linorder_class.Max_eq_if)
            apply auto
            subgoal
              using prems(30) by auto
            subgoal 
              by (metis image_iff nless_le prems3(5))
            subgoal
              using prems3(5) by blast
            done
          done
        subgoal
          unfolding produce_def 
          apply (auto split: sum.splits)
          subgoal for x
            apply (cases x; auto simp add: comp_def)
            using image_iff apply fastforce
            done
          subgoal
            apply (simp add: comp_def)
            apply (rule rmdups_NilI)
            apply auto
            done
          done
        done
      done
    done
      (* *)
  subgoal for batch lxs
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
    using prems(3) apply simp
    using prems(4) apply simp
    subgoal
      apply simp
      using prems(5,6,7,8, 14) prems(9) apply -
      apply (simp add: change_multiplicities_append_comp comp_def)
      apply (elim conjE)
      apply hypsubst_thin
      unfolding extract_progress_def
      apply (auto simp add: comp_def filter_empty_conv c_pts_change_multiplicities produce_def dest!: propagate_all_preserves_c_pts)
      apply (smt (verit, ccfv_SIG) add.commute group_cancel.add2 group_cancel.sub1 zmset_of_plus)
      done
    subgoal
      using prems(5,6,7,8,14) prems(10)[symmetric]  apply -
      apply (auto simp add: input_cap_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      unfolding extract_progress_def
      apply (simp add:  comp_def produce_def update_zmultiset_replicate)
      done
    subgoal
      apply simp
      apply (cases batch)
      subgoal
        using prems(5,6,7,8,14,26,10) prems(9)[symmetric] apply simp
        apply (rule Orderings.preorder_class.order_trans)
        apply (rule prems(11)[simplified])
        apply simp
        apply (auto 0 0 simp flip: Multiset.union_assoc simp add: input_cap_def below_n_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
        apply (smt (z3) add_zmset_add_single basic_trans_rules(23) frontier_below_eq_frontier_plus_pos frontier_le_add frontier_le_singletons group_cancel.sub1 plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(2)
            zcount_single)
        done
      subgoal for x batch'
        using prems(5,6,7,8,14,26,10) prems(9)[symmetric] apply simp
        apply (rule Orderings.preorder_class.order_trans)
        apply (rule prems(11)[simplified])
        apply simp
        apply (auto 0 0 simp flip: Int.Suc_nat_eq_nat_zadd1 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
        apply (simp only: flip: add.assoc)
        apply (subst (1 2 3) add_zmset_add_single)
        apply (subgoal_tac "frontier {#n 1#}\<^sub>z \<le> frontier (zmset_of {#n 1. x \<in># mset batch'#} + {#n 1#}\<^sub>z + {#Suc (n 1)#}\<^sub>z)")
        subgoal premises prems2
          using prems2(8,9,11) apply -
          apply (rule Orderings.preorder_class.order_trans)
          apply (rule frontier_add_le)
          apply assumption
          apply simp_all
          apply (rule Orderings.preorder_class.eq_refl)
          apply (rule arg_cong[where f=frontier])
          apply auto
          done
        subgoal
          by (metis Suc_eq_plus1_left add.commute arith_extra_simps(6) frontie_add_zmset_add frontier_le_add frontier_le_singletons trivial_dataflow_topology_interpretation.le_plus(2))
        done
      done
    subgoal
      using prems(12) by simp
    using prems(13) apply simp
    using prems(14) apply simp
    using prems(15) apply simp
    subgoal
      using prems(5,6,7,8,14,16) 
      apply simp
      apply (auto 0 0 simp add: produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      done
    subgoal
      using prems(17) by (auto 0 0 simp add: produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
    using prems(19) apply simp
    using prems(20) apply simp
    using prems(21) apply simp
    using prems(22) apply simp
    using prems(23) apply simp
    subgoal premises prems2
      using prems2(2,5) prems(24,25,26,10,5,6,7,8,14,16,10,4,29,28) prems(9)[symmetric] apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: if_splits option.splits; hypsubst_thin?)
      using nat_less_le apply blast
      done
    subgoal
      using prems(27,28,29,25) 
      apply (auto 0 0 simp add: sorted_wrt_append input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: if_splits prod.splits option.splits; hypsubst_thin?)
      apply (smt (verit, best) case_prod_conv le_refl sorted_wrt_map_mono sorted_wrt_true)
      apply (meson nat_less_le)
      apply (metis imageI nat_less_le)
      done
    subgoal
      using prems(26,27,29) prems(5,6,7,8,14,16,10,18) prems(9)[symmetric] apply -
      apply (auto 0 0 simp add: produce_def input_cap_def update_zmultiset_replicate extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      subgoal
        apply (subst add_zmset_add_single)
        apply (subst (asm) add_zmset_add_single)
        apply (simp only: flip: add.assoc)
        apply (rule Orderings.preorder_class.order_trans[rotated])
        apply (rule frontier_add_le_alt2[where t="n 0"])
        apply simp
        apply simp
        subgoal premises prems2
          using prems2(9) prems2(13)[symmetric] apply -
          apply simp
          done
        subgoal
          apply (rule Orderings.preorder_class.eq_refl)
          apply (rule arg_cong[where f=frontier])
          apply auto
          done
        done
      subgoal
        apply (simp only: flip: add.assoc)
        apply (cases batch; simp)
        apply (subst (1 2 3) add_zmset_add_single)
        apply (subst (asm) add_zmset_add_single)
        apply (subst add_empty_zmultiset)
        apply hypsubst_thin
        subgoal for x batch'
          apply (subgoal_tac "frontier (zmset_of {#n 1. x \<in># mset batch'#} + {#Suc (n 1)#}\<^sub>z) \<le> frontier {#Suc (n 1)#}\<^sub>z")
          subgoal
            apply (rule Orderings.preorder_class.order_trans[rotated])
            apply (rule frontier_add_le_alt[rotated 2])
            apply assumption
            apply (rule Orderings.preorder_class.order_trans)
            apply assumption
            apply simp_all
            apply (simp add: frontier_le_singletons)
            subgoal
              apply (rule Orderings.preorder_class.eq_refl)
              apply (rule arg_cong[where f=frontier])
              apply auto
              done
            done
          subgoal
            by (metis (no_types, lifting) Groups.add_ac(2) frontier_below_eq_frontier_plus_pos semiring_norm(174) zcount_zmset_of_nonneg)
          done
        done
      done
    subgoal
      using prems(27,29) prems(5,6,7,8,14,16,10,18) prems(9)[symmetric] apply -
      apply (auto 0 0 simp add: produce_def input_cap_def update_zmultiset_replicate extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      subgoal premises prems2
        using prems2(7) apply -
        apply (rule Orderings.preorder_class.order_trans)
        apply assumption
        apply (meson frontier_le_singletons le_Suc_eq not_less_eq_eq)
        done
      done
    subgoal
      using prems(28) by auto
    subgoal
      using prems(29) apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply fastforce+
      done
    subgoal
      using prems(30) by auto
    subgoal
      using prems(31) apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply (rule frontier_le_add)
      apply assumption
      using prems(5,6,7,8,14,16,19,27,10,9) apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply (rule Orderings.preorder_class.order_trans)
      apply assumption
      back
      apply auto
      done
    subgoal
      using prems(32) apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply (subst (1) add_zmset_add_single)
      apply (rule frontier_le_add)
      apply (smt (verit, ccfv_SIG) basic_trans_rules(23) diff_single_eq_union_zmset frontier_add_zmset order_refl)
      using prems(5,6,7,8,14,16,19,27,10,9) apply -
      apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: prod.splits if_splits option.splits; hypsubst_thin?)
      apply (rule Orderings.preorder_class.order_trans)
      apply assumption
      back
      apply (metis frontier_le_singletons le_add2 plus_1_eq_Suc)
      done
    apply (simp add: comp_def)
    apply (rule rtranclp_intros_1)
    apply (rule arg_cong3[where f=map_op])
    apply simp_all
    apply (rule arg_cong[where f=source_op])
    apply (rule ext)
    apply (subst iterates.code)
    apply simp
    apply (cases batch)
    apply (simp_all add: lshift_assoc)
    apply (rule arg_cong2[where f=lshift])
    apply simp_all
    subgoal
      unfolding max_from_caps_buf_def map_is_Nil_conv append_is_Nil_conv produce_def
      by simp
    subgoal premises prems2 for a list
      using prems2(2,7,6) prems(28,29) apply -
      apply (simp flip: lshift_assoc)
      apply (rule arg_cong2[where f=lshift])
      apply simp
      apply (subgoal_tac "\<not> Cap (n 1) 1 \<in> set caps")
      subgoal
        unfolding produce_def
        apply (simp only: max_from_caps_buf_append list_to_buf_def flip: singleton_lshift snoc_shift lshift_assoc split: if_splits)
        apply simp
        apply (simp only: max_from_caps_buf_append list_to_buf_def flip: singleton_lshift snoc_shift lshift_assoc split: if_splits)
        apply safe
        subgoal for x
          apply (rule FalseE)
          apply (cases x; auto split: sum.splits)
          apply (metis image_iff less_not_refl sum.sel(2))
          done
        subgoal for x
          apply (rule FalseE)
          apply (auto split: sum.splits)
          done
        subgoal
          apply (rule arg_cong2[where f=lshift])
          subgoal
            unfolding max_from_caps_buf_def BULK_BENQ_def 
            apply (rule List.List.list.map_cong)
            apply auto
            apply (rule Lattices_Big.linorder_class.Max_eq_if)
            subgoal
              by (auto split: if_splits)
            subgoal
              by (auto split: if_splits)
            subgoal for z
              by (auto split: prod.splits sum.splits if_splits)
            subgoal for z
              apply (auto split: prod.splits sum.splits if_splits)
              apply (metis prems(28) capability.exhaust capability.sel(1) verit_comp_simplify(1) zero_one)+
              done
            done
          subgoal
            apply (rule arg_cong2[where f=lshift])
            subgoal
              unfolding max_from_caps_buf_def BULK_BENQ_def 
              apply (rule List.List.list.map_cong)
              apply auto
              apply (rule Lattices_Big.linorder_class.Max_eq_if)
              subgoal
                by (auto split: if_splits)
              subgoal
                by (auto split: if_splits)
              subgoal for z
                by (auto split: prod.splits sum.splits if_splits)
              subgoal for z
                apply (cases z)
                apply (auto simp add: set_rmdups split: prod.splits sum.splits if_splits)
                done
              done
            subgoal
              apply (rule arg_cong2[where f=lshift])
              subgoal
                unfolding max_from_caps_buf_def BULK_BENQ_def 
                apply (rule List.List.list.map_cong)
                apply (auto simp add: set_rmdups split: if_splits)
                done
              subgoal
                unfolding max_from_caps_buf_def BULK_BENQ_def 
                apply auto
                apply (rule Lattices_Big.linorder_class.Max_eq_if)
                subgoal
                  by (auto split: if_splits)
                subgoal
                  by (auto split: if_splits)
                subgoal
                  apply (clarsimp split: if_splits)
                  apply fast+
                  done
                subgoal
                  using prems(30) apply -
                  apply (auto 0 0 simp add: set_rmdups split: if_splits)
                  apply fast+
                  done
                subgoal
                  using prems(30) apply -
                  apply (auto 0 0 simp add: set_rmdups split: if_splits)
                  apply (subst rmdups_insert_NilI)
                  apply auto
                  done
                done
              done
            done
          done
        done
      subgoal
        by auto
      done
    done
  defer
  subgoal
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
    using prems(3) apply simp
    using prems(4) apply simp
    subgoal
      apply simp
      using prems(5,6,7,8, 14) prems(9) apply -
      apply (simp add: change_multiplicities_append_comp comp_def)
      apply (elim conjE)
      apply hypsubst_thin
      unfolding extract_progress_def
      apply (auto simp add: diff_add_eq comp_def filter_empty_conv c_pts_change_multiplicities produce_def dest!: propagate_all_preserves_c_pts)
      done
    subgoal
      using prems(5,6,7,8,14) prems(10)[symmetric]  apply -
      apply (auto simp add: input_cap_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      unfolding extract_progress_def
      apply (simp add:  comp_def produce_def update_zmultiset_replicate)
      done
    subgoal
      apply simp
      using prems(5,6,7,8,14) apply simp
      apply (rule Orderings.preorder_class.order_trans)
      apply (rule prems(11)[simplified])
      apply simp
      apply hypsubst_thin
      apply (auto simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      apply (rule Orderings.preorder_class.eq_refl)
      apply (rule arg_cong[where f=frontier])
      apply auto
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
    using prems(19) apply simp
    using prems(20) apply simp
    using prems(21) apply simp
    subgoal
      using prems(22) apply (simp add: changes_above_impl_def)
      apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      apply fastforce


end
  using prems(23) apply simp
  subgoal premises prems2
    using prems2(2,5) prems(24,25,26,10,5,6,7,8,14,16,10,4,29,28) prems(9)[symmetric] apply -
    apply (auto 0 0 simp add: input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: if_splits option.splits; hypsubst_thin?)
    using nat_less_le apply blast
    done
  subgoal
    using prems(27,28,29,25) 
    apply (auto 0 0 simp add: sorted_wrt_append input_cap_def update_zmultiset_replicate produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: if_splits prod.splits option.splits; hypsubst_thin?)
    apply (smt (verit, best) case_prod_conv le_refl sorted_wrt_map_mono sorted_wrt_true)
    apply (meson nat_less_le)
    apply (metis imageI nat_less_le)
    done
  subgoal


    subgoal premises prems2
      using prems(14,18,15) apply simp
      apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
      apply (rule Orderings.preorder_class.order_trans[rotated])
      apply assumption


      find_theorems "frontier (_  _) \<le> _"



end
  using prems(19) apply simp
  using prems(20) apply simp
  using prems(21) apply simp
  using prems(22) apply simp
  using prems(23) apply simp
  using prems(24) apply simp
  using prems(25) apply simp
  subgoal
    using prems(26) prems(5,6,7,8,14,16) 
    apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
    done
  subgoal
    using prems(27) prems(5,6,7,8,14,16) 
    apply (auto 0 0 simp add: extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
    done
  using prems(28) apply simp
  using prems(29) apply simp
  using prems(30) apply simp
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

    find_theorems change_multiplicities c_pts

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
    using prems(5,6,7,8,14) prems(10)[unfolded input_cap_def][symmetric]  apply -
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