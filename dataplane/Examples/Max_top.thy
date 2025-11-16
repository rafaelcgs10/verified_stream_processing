theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
  "../AntichainOrder"
begin 

corec max_top' where
  "max_top' os buf caps = choice5
   (Read None (\<lambda> st. if isl st \<and> isr (projl st) then max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps else \<oslash>))
   (let below_caps = [cap \<leftarrow> caps. \<not> frontier_less_equal (front os 0) (time cap) ] in
    let above_caps = [cap \<leftarrow> caps. frontier_less_equal (front os 0) (time cap) ] in
    let batch = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps in
    let os' = produces os batch in
    let os'' = drop_caps_old os' below_caps in
    let buf' = (\<lambda> cap. if cap \<in> set below_caps then [] else buf cap) in
    Silent (max_top' os'' buf' above_caps))
   (Read (Some 0)
    (\<lambda> x. if isl x then \<oslash> else
     let (n, t) = projr x in
     let (caps', os') = (if Cap t 0 \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, mint_cap os 0 t)) in
     let os'' = consume os' 1 t 1 in
     let buf' = BENQ (Cap t 0) n buf in
     max_top' os'' buf' caps'))
    ( ((case outpu os 0 of
         [] \<Rightarrow> Choice {||}
       |  x # xs \<Rightarrow> (send_output (max_top' (os\<lparr> outpu := (outpu os)(0 := xs ) \<rparr>) buf caps) 0 x))))
    (let (os', st) = obtain_progress os in
     send_progress (max_top' os' buf caps) st)"

lemma step_max'_top_elim:
  assumes "step io (max_top' os buf caps) op"
  obtains
    st where "io = Inp None st" "\<not> isl st \<or> (isl st \<and> \<not> isr (projl st))" "op = \<oslash>" 
  | st where "io = Inp None st" "isl st" "isr (projl st)" "op = max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps" 
  | above_caps below_caps batch os' os'' buf' where "io = Tau" "below_caps = [cap \<leftarrow> caps. \<not> frontier_less_equal (front os 0) (time cap)]"
    "above_caps = [cap \<leftarrow> caps. frontier_less_equal (front os 0) (time cap)]"
    "batch = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps"
    "os' = produces os batch"
    "os'' = drop_caps_old os' below_caps"
    "buf' = (\<lambda> cap. if cap \<in> set below_caps then [] else buf cap)"
    "op = max_top' os'' buf' above_caps"
  | x where "io = Inp (Some 0) x" "isl x" "op = \<oslash>"
  | x n t caps' os' os'' buf' where "io = Inp (Some 0) x" "\<not> isl x" "(n, t) = projr x"
    "(caps', os') = (if Cap t 0 \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, mint_cap os 0 t))"
    "os'' = consume os' 1 t 1"
    "buf' = BENQ (Cap t 0) n buf" "op = max_top' os'' buf' caps'"
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

lemma step_max_top'_Out_intro[intro!]:
  "op = max_top' (os\<lparr> outpu := (outpu os)(0 := xs ) \<rparr>) buf caps \<Longrightarrow>
   outpu os 0 = x # xs \<Longrightarrow>
   step (Out (Some 0) (Inr x)) (max_top' os buf caps) op"
  apply (subst max_top'.code)
  apply auto
  done

lemma step_max_top'_Inp_Some_intro[intro!]:
  "op = max_top' os'' buf' caps' \<Longrightarrow>
   (caps', os') = (if Cap t 0 \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, mint_cap os 0 t)) \<Longrightarrow>
   os'' = consume os' 1 t 1 \<Longrightarrow>
   \<not> isl x \<Longrightarrow>
   (n, t) = projr x \<Longrightarrow>
   buf' = BENQ (Cap t 0) n buf \<Longrightarrow>
   step (Inp (Some 0) x) (max_top' os buf caps) op"
  apply (cases x; simp)
  apply (subst max_top'.code)
  apply (auto 0 0 split: list.splits if_splits sum.splits)
  subgoal
    unfolding Let_def
    apply (rule SC)
     apply (auto 0 0)
    apply (rule SC)
     apply auto
    done
  subgoal
    unfolding Let_def
    apply (rule SC)
     apply (auto 0 0)
    apply (rule SC)
     apply auto
    done
  subgoal
    unfolding Let_def
    apply (rule SC)
     apply (auto 0 0)
    apply (rule SC)
     apply auto
    done
  subgoal
    unfolding Let_def
    apply (rule SC)
     apply (auto 0 0)
    apply (rule SC)
     apply auto
    done
  done



lemma steps_max_top'_Inp_Some_intro[intro]:
  "\<forall> x \<in> set xs. isr x \<Longrightarrow>
   (caps', os') = fold (\<lambda> t (caps, os). if Cap t 0 \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, mint_cap os 0 t)) (map (snd o projr) xs) (caps, os) \<Longrightarrow>
   os'' = fold (\<lambda> t os. consume os 1 t 1) (map (snd o projr) xs) os' \<Longrightarrow>
   buf' = fold (\<lambda> (n, t) buf. BENQ (Cap t 0) n buf) (map projr xs) buf \<Longrightarrow>
   op = max_top' os'' buf' caps' \<Longrightarrow>
   sorted (map time caps) \<Longrightarrow>
   steps (map (\<lambda> e. Inp (Some 0) e) xs) (max_top' os buf caps) op"
  apply (induct xs arbitrary: os os' os'' buf buf' caps caps' op rule: rev_induct)
  subgoal for os os' os'' buf buf' caps caps' op
    by (simp add: sort_key_id_if_sorted)
  subgoal premises prems for a xs os os' os'' buf buf' caps caps' op
    using prems(2-) apply -
    apply (cases a; simp)
    subgoal for p
      apply (cases p; simp)
      subgoal for n t
        apply (auto 0 0 split: sum.splits prod.splits if_splits)
        subgoal
          apply hypsubst_thin
          apply (intro relcomppI)
           apply (rule prems(1))
                apply simp
               defer
               apply (rule refl)+
            apply force
           apply (rule step_max_top'_Inp_Some_intro)
                apply simp_all
          done
        subgoal for caps''' os'''
          apply (intro relcomppI)
           apply (rule prems(1))
                apply simp
               defer
               apply (rule refl)+
            apply blast
           apply (rule step_max_top'_Inp_Some_intro[where t=t])
                apply (rule refl)+
               apply simp_all
          apply hypsubst_thin
          subgoal premises
            apply (induct xs arbitrary: os''' rule: rev_induct)
             apply auto
            done
          done
        done
      done
    done
  done

lemma step_max_top'_Tau_output[intro]:
  "below_caps = [cap \<leftarrow> caps. \<not> frontier_less_equal (front os 0) (time cap)] \<Longrightarrow>
   above_caps = [cap \<leftarrow> caps. frontier_less_equal (front os 0) (time cap)] \<Longrightarrow>
   batch = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps \<Longrightarrow>
   os' = produces os batch \<Longrightarrow>
   os'' = drop_caps_old os' below_caps \<Longrightarrow>
   buf' = (\<lambda> cap. if cap \<in> set below_caps then [] else buf cap) \<Longrightarrow>
   op = max_top' os'' buf' above_caps \<Longrightarrow>
   step Tau (max_top' os buf caps) op"
  apply (subst max_top'.code)
  apply (auto split: list.splits if_splits sum.splits)
  done

lemma step_max_top'Inp_None[intro!]:
  "isl st \<Longrightarrow>
   isr (projl st) \<Longrightarrow>
   op = max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps \<Longrightarrow>
   step (Inp None st) (max_top' os buf caps) op"
  apply (subst max_top'.code)
  apply (auto 0 0 split: list.splits if_splits sum.splits)
  subgoal
    unfolding Let_def
    apply (rule SC)
     apply simp
     apply (rule disjI1)
     apply (auto 0 0)
    apply force
    done
  subgoal
    unfolding Let_def
    apply (rule SC)
     apply simp
     apply (rule disjI1)
     apply (auto 0 0)
    apply force
    done
  done

lemma step_max_top'_Out_None[intro!]:
  "obtain_progress os = (os', st) \<Longrightarrow>
   op = max_top' os' buf caps \<Longrightarrow>
   step (Out None (Inl (Inl st))) (max_top' os buf caps) op"
  apply (subst max_top'.code)
  apply (auto split: list.splits if_splits sum.splits)
  done

(* 
  abbreviation "max_top \<equiv> max_top' []"
*)

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

abbreviation "inp_top os caps inps \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (input_top os caps inps)"
abbreviation "m_top os buf caps \<equiv>  map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (max_top' os buf caps)"

abbreviation "inp_m_top os1 caps1 inps buf1 os2 buf2 caps2 \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] buf1 (inp_top os1 caps1 inps) (m_top os2 buf2 caps2))"


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

definition propagate_invs where "propagate_invs summary c = (dataflow_topology_from_tree.inv_implications_nonneg c \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c)"

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

lemma propagate_all_preserves_c_pts_alt:
  "c_pts (the (propagate_all summary c)) = c_pts c"
  using propagate_all_preserves_c_pts by force


lemma propagate_all_frontier_c_imp_correctness_alt:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c  \<Longrightarrow>
   dataflow_topology summary trivial_dataflow_topology_interpretation.followed_by \<Longrightarrow>
   frontier (c_imp (the (propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> nat antichain) c)) loc) = dataflow_topology.implied_frontier_alt summary dataflow_topology_from_tree.followed_by c loc"
  apply (cases "propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> nat antichain) c"; simp)
  apply (frule propagate_all_frontier_c_imp_correctness[where loc=loc])
       apply assumption+
     apply auto
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (subst propagate_all_preserves_c_pts)
   apply auto
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

lemma zcount_zmset_gt_0:
  "(t, m) \<in> set xs \<Longrightarrow>
   0 < m \<Longrightarrow>
   (\<forall> m \<in> snd ` set xs. m \<ge> 0) \<Longrightarrow>
   0 < zcount (zmset xs) t"
  apply (simp add: zcount_zmset zcount_update_zmultiset split: prod.splits)
  apply (induct xs)
   apply auto
  apply (smt (verit) filter_is_subset subset_code(1) sum_list_0 sum_list_mono)
  done

lemma zmset_map_one_zmset_of:
  "zmset (map (\<lambda>cap. (f cap, 1)) caps) = zmset_of (mset (map f caps))"
  apply (induct caps)
   apply (auto simp add: zcount_update_zmultiset zcount_zmset zmultiset_eq_iff)
  done

lemma zmset_map_minus_one_zmset_of:
  "zmset (map (\<lambda>cap. (f cap, -1)) caps) = - zmset_of (mset (map f caps))"
  apply (induct caps)
   apply (auto simp add: zcount_update_zmultiset zcount_zmset zmultiset_eq_iff)
  done

lemma zmset_of_replicate_mset[simp]:
  "zmset_of (replicate_mset n (g a)) = Auxiliary.image_zmset g (zmset_of (replicate_mset n a))"
  apply (induct n)
   apply (auto simp add: zmultiset_eq_iff zcount_image_zmset update_zmultiset_replicate split: if_splits)
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

definition "changes_above_impl pts chgs = (\<forall>(l, t, d)\<in>set chgs. frontier_less_equal (dataflow_topology.implied_frontier_alt my_summ (+) pts l) t)"

definition "changes_non_zero chgs = (\<forall>d\<in>snd ` snd ` set chgs. d \<noteq> 0)"

definition "input_cap inps n = (if inps 0 = LNil then {#}\<^sub>z else {# n 0 #}\<^sub>z)"

(* FIXME: move me *)
lemma replicate_mset_length[simp]:
  "replicate_mset (length batch) (n 1) = {#n 1. x \<in># mset batch#}"
  unfolding replicate_mset_def
  by (induct batch) auto

lemma outpu_produce:
  "outpu (produce os1 (Cap t 1) (a # xs)) 1 = outpu os1 1 @ map (\<lambda> x. (x, t)) (a # xs)"
  unfolding produce_def
  apply auto
  done

definition "below_n A n = (\<forall> t. zcount A t > 0 \<longrightarrow> t \<le> n)"

lemma zmultiset_move_add_other_side:
  "(A :: _ zmultiset) + B = C \<longleftrightarrow> A = C - B"
  apply (simp add: zmultiset_eq_iff)
  apply auto
  apply (smt (verit))
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


lemma dataflow_topology_implied_frontier_alt_my_summ:
  "dataflow_topology.implied_frontier_alt my_summ (+) c loc =
   frontier (\<Sum>loc'\<in>UNIV. dataflow_topology.after_summary (+) (zmset_of (mset_set (set_antichain (frontier (c_pts c loc'))))) (graph.path_weight my_summ loc' loc))"
  apply (subst dataflow_topology.implied_frontier_alt_def)
   apply simp_all
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

lemma frontier_less_equal_trans:
  "frontier_less_equal A t' \<Longrightarrow>
   t' \<le> t \<Longrightarrow> 
   frontier_less_equal A t"
  unfolding frontier_less_equal_iff
  by (meson frontier_le_singletons order_trans_rules(23))

lemma le_frontier_frontier_less_equal:
  "\<forall> t \<in> fst ` set A. frontier_less_equal F t \<Longrightarrow>
   F \<le> frontier (zmset A)"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply auto
  subgoal for t
    apply transfer
    apply (auto simp add: zcount_zmset minimal_antichain_def)
    by (smt (verit, del_insts) case_prod_beta filter_empty_conv list.map(1) sum_list_simps(1))
  done


lemma frontier_less_equal_add_frontier_le:
  "\<forall> t \<in>#\<^sub>z X. frontier_less_equal (frontier A) t \<Longrightarrow>
   frontier A \<le> frontier (A + X)"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply auto
  subgoal for t
    by (metis add_diff_cancel order.refl order_trans_rules(23) trivial_dataflow_topology_interpretation.in_frontier_diff)
  done

lemma frontier_less_equal_add_frontier_le_alt:
  "\<forall> t \<in>#\<^sub>z X. frontier_less_equal (frontier A) t \<Longrightarrow>
   frontier A \<le> frontier B \<Longrightarrow>
   frontier A \<le> frontier (B + X)"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply auto
  subgoal for t
    by (metis add_diff_cancel order_trans_rules(23) trivial_dataflow_topology_interpretation.in_frontier_diff)
  done

lemma in_zmset_filter:
  "t \<in>#\<^sub>z zmset (map snd (filter (\<lambda>(l', t, d). l = l') A)) \<Longrightarrow> \<exists>m. (l, t, m) \<in> set A \<and> m \<noteq> 0"
  apply (induct A)
   apply simp
  apply (clarsimp  split: if_splits prod.splits)
  subgoal
    by (smt (verit, ccfv_SIG) not_in_iff_zmset zcount_update_zmultiset)
  subgoal
    by (smt (verit, ccfv_SIG) not_in_iff_zmset zcount_update_zmultiset)
  done

lemma frontier_less_equal_change_multiplicities:
  "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg) l) t) \<Longrightarrow>
   (\<forall> l. dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg) l \<le> dataflow_topology.implied_frontier_alt my_summ (+) (change_multiplicities my_summ A (pt_tr sg)) l)"
  unfolding dataflow_topology_implied_frontier_alt_my_summ extract_progress_def
  apply (simp add: change_multiplicities_append_comp c_pts_change_multiplicities comp_def)
  apply (intro conjI impI allI; simp?; hypsubst)
  subgoal
    apply (rule frontier_less_equal_add_frontier_le)
    apply auto
    subgoal for t
      apply (subgoal_tac "\<exists> m. (Loc 0 (Trg 1), t, m) \<in> set A")
       apply (elim exE)
      subgoal for m
        apply (drule bspec[of _ _ "(Loc 0 (Trg 1), t, m)"])
         apply simp
        apply simp
        done
      subgoal premises prems
        using prems(2) in_zmset_filter by fast
      done
    done
  subgoal
    apply (rule frontier_le_add)
     apply simp_all
    subgoal
      apply (rule frontier_less_equal_add_frontier_le_alt)
       apply auto
      subgoal for t
        apply (subgoal_tac "\<exists> m. (Loc 0 (Src 1), t, m) \<in> set A")
         apply (elim exE)
        subgoal for m
          apply (drule bspec[of _ _ "(Loc 0 (Src 1), t, m)"])
           apply simp
          apply simp
          unfolding frontier_less_equal_def
          done
        subgoal premises prems
          using prems(2) in_zmset_filter by fast
        done
      subgoal
        by (metis (no_types, lifting) frontier_below_eq_frontier_plus_pos frontier_idempotent zmset_of_mset_set_ge_zero)
      done
    subgoal
      apply (rule frontier_less_equal_add_frontier_le_alt)
       apply auto
      subgoal for t
        apply (subgoal_tac "\<exists> m. (Loc 0 (Trg 1), t, m) \<in> set A")
         apply (elim exE)
        subgoal for m
          apply (drule bspec[of _ _ "(Loc 0 (Trg 1), t, m)"])
           apply simp
          apply simp
          unfolding frontier_less_equal_def
          apply auto
          apply (smt (verit, del_insts) Groups.add_ac(2) frontier_idempotent in_frontier_in_frontier_add le_trans zcount_zmset_of_nonneg)
          done
        subgoal premises prems
          using prems(2) in_zmset_filter by fast
        done
      subgoal
        by (metis (no_types, lifting) add_diff_cancel_left' frontier_below_eq_frontier_minus frontier_idempotent zcount_zmset_of_nonneg)
      done
    done
  subgoal
    apply (rule frontier_le_add)
     apply simp_all
    subgoal
      apply (rule frontier_less_equal_add_frontier_le_alt)
       apply auto
      subgoal for t
        apply (subgoal_tac "\<exists> m. (Loc 0 (Src 1), t, m) \<in> set A")
         apply (elim exE)
        subgoal for m
          apply (drule bspec[of _ _ "(Loc 0 (Src 1), t, m)"])
           apply simp
          apply simp
          apply (rule frontier_less_equal_le_trans)
           apply assumption
          apply (smt (verit, ccfv_threshold) Groups.add_ac(1) frontier_below_eq_frontier_plus_pos zcount_union zcount_zmset_of_nonneg)
          done
        subgoal premises prems
          using prems(2) in_zmset_filter by fast
        done
      subgoal
        by (simp add: frontier_le_remove_l zero_compare_simps(3))
      done
    subgoal
      apply (rule frontier_le_add)
       apply simp_all
      subgoal
        apply (rule frontier_less_equal_add_frontier_le_alt)
         apply auto
        subgoal for t
          apply (subgoal_tac "\<exists> m. (Loc 0 (Trg 1), t, m) \<in> set A")
           apply (elim exE)
          subgoal for m
            apply (drule bspec[of _ _ "(Loc 0 (Trg 1), t, m)"])
             apply simp
            apply simp
            apply (rule frontier_less_equal_le_trans)
             apply assumption
            apply (smt (verit, best) add_diff_cancel_left' cancel_ab_semigroup_add_class.diff_right_commute diff_add_cancel dual_order.trans frontier_below_eq_frontier_minus frontier_idempotent zcount_zmset_of_nonneg)
            done
          subgoal premises prems
            using prems(2) in_zmset_filter by fast
          done
        subgoal premises
          by (smt (verit) Groups.add_ac(2) frontier_below_eq_frontier_plus_pos frontier_idempotent order_trans_rules(23) zcount_zmset_of_nonneg zmset_of_plus)
        done
      apply (rule frontier_le_add)
       apply simp_all
      subgoal
        apply (rule frontier_less_equal_add_frontier_le_alt)
         apply auto
        subgoal for t
          apply (subgoal_tac "\<exists> m. (Loc 1 (Src 1), t, m) \<in> set A")
           apply (elim exE)
          subgoal for m
            apply (drule bspec[of _ _ "(Loc 1 (Src 1), t, m)"])
             apply simp
            apply simp
            done
          subgoal premises prems
            using prems(2) in_zmset_filter by fast
          done
        subgoal premises
          by (smt (verit) Groups.add_ac(2) frontier_below_eq_frontier_plus_pos frontier_idempotent order_trans_rules(23) zcount_zmset_of_nonneg zmset_of_plus)
        done
      apply (rule frontier_less_equal_add_frontier_le_alt)
       apply auto
      subgoal for t
        apply (subgoal_tac "\<exists> m. (Loc 1 (Trg 1), t, m) \<in> set A")
         apply (elim exE)
        subgoal for m
          apply (drule bspec[of _ _ "(Loc 1 (Trg 1), t, m)"])
           apply simp
          apply simp
          apply (rule frontier_less_equal_le_trans)
           apply assumption
          apply (smt (verit, best) add_diff_cancel_left' cancel_ab_semigroup_add_class.diff_right_commute diff_add_cancel dual_order.trans frontier_below_eq_frontier_minus frontier_idempotent zcount_zmset_of_nonneg)
          done
        subgoal premises prems
          using prems(2) in_zmset_filter by fast
        done
      subgoal premises
        by (smt (verit) Groups.add_ac(2) frontier_below_eq_frontier_plus_pos frontier_idempotent order_trans_rules(23) zcount_zmset_of_nonneg)
      done
    done
  subgoal
    apply (rule frontier_le_add)
     apply simp_all
    subgoal
      apply (rule frontier_less_equal_add_frontier_le_alt)
       apply auto
      subgoal for t
        apply (subgoal_tac "\<exists> m. (Loc 0 (Src 1), t, m) \<in> set A")
         apply (elim exE)
        subgoal for m
          apply (drule bspec[of _ _ "(Loc 0 (Src 1), t, m)"])
           apply simp
          apply simp
          apply (rule frontier_less_equal_le_trans)
           apply assumption
          apply (smt (verit, ccfv_threshold) Groups.add_ac(1) frontier_below_eq_frontier_plus_pos zcount_union zcount_zmset_of_nonneg)
          done
        subgoal premises prems
          using prems(2) in_zmset_filter by fast
        done
      subgoal
        by (simp add: frontier_le_remove_l zero_compare_simps(3))
      done
    subgoal
      apply (rule frontier_le_add)
       apply simp_all
      subgoal
        apply (rule frontier_less_equal_add_frontier_le_alt)
         apply auto
        subgoal for t
          apply (subgoal_tac "\<exists> m. (Loc 0 (Trg 1), t, m) \<in> set A")
           apply (elim exE)
          subgoal for m
            apply (drule bspec[of _ _ "(Loc 0 (Trg 1), t, m)"])
             apply simp
            apply simp
            apply (rule frontier_less_equal_le_trans)
             apply assumption
            apply (smt (verit, best) add_diff_cancel_left' cancel_ab_semigroup_add_class.diff_right_commute diff_add_cancel dual_order.trans frontier_below_eq_frontier_minus frontier_idempotent zcount_zmset_of_nonneg)
            done
          subgoal premises prems
            using prems(2) in_zmset_filter by fast
          done
        subgoal premises
          by (smt (verit) Groups.add_ac(2) frontier_below_eq_frontier_plus_pos frontier_idempotent order_trans_rules(23) zcount_zmset_of_nonneg zmset_of_plus)
        done
      subgoal
        apply (rule frontier_less_equal_add_frontier_le_alt)
         apply auto
        subgoal for t
          apply (subgoal_tac "\<exists> m. (Loc 1 (Trg 1), t, m) \<in> set A")
           apply (elim exE)
          subgoal for m
            apply (drule bspec[of _ _ "(Loc 1 (Trg 1), t, m)"])
             apply simp
            apply simp
            done
          subgoal premises prems
            using prems(2) in_zmset_filter by fast
          done
        subgoal premises
          by (smt (verit) Groups.add_ac(2) frontier_below_eq_frontier_plus_pos frontier_idempotent order_trans_rules(23) zcount_zmset_of_nonneg)
        done
      done
    done
  done

lemma frontier_less_equal_change_multiplicities_alt:
  "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg) l) t) \<Longrightarrow>
   dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg) l \<le> dataflow_topology.implied_frontier_alt my_summ (+) (change_multiplicities my_summ A (pt_tr sg)) l"
  using frontier_less_equal_change_multiplicities by auto

(*
   (\<forall> t' p. Cap t' p \<in> set caps \<longrightarrow> t' < n 0) \<Longrightarrow>
   (\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). t < n 0) \<Longrightarrow>
   (\<forall> t\<ge>n 0. buf2 (Cap t 1) = []) \<Longrightarrow>
*)

lemma changes_above_impl_extend:
  "changes_above_impl F A \<Longrightarrow>
   changes_above_impl F B \<Longrightarrow>
   set C = set (A @ B) \<Longrightarrow>
   changes_above_impl F C"
  unfolding changes_above_impl_def
  apply auto
  done 

lemma changes_above_impl_elim:
  assumes  "changes_above_impl F (A @ B)"
  obtains "changes_above_impl F A \<and> changes_above_impl F B"
  using assms  apply atomize_elim
  unfolding changes_above_impl_def
  apply auto
  done 

lemma c_pts_change_multiplicities_gt_location:
  "(\<forall> l' \<in> fst ` set B. l < l') \<Longrightarrow>
   c_pts (change_multiplicities my_summ B c) l = c_pts c l"
  apply (induct B arbitrary: c)
   apply simp
  subgoal for a B c
    apply (cases a; simp)
    apply (subst change_multiplicities_simp_alt)
    apply (clarsimp simp add: split: location.splits prod.splits)
    done
  done

lemma c_pts_change_multiplicities_diff_location:
  "(\<forall> l' \<in> fst ` set B. l \<noteq> l') \<Longrightarrow>
   c_pts (change_multiplicities my_summ B c) l = c_pts c l"
  apply (induct B arbitrary: c)
   apply simp
  subgoal for a B c
    apply (cases a; simp)
    apply (subst change_multiplicities_simp_alt)
    apply (clarsimp simp add: split: location.splits prod.splits)
    done
  done

lemma l0_lt_l1[simp]:
  "Loc (0 :: 2) (p :: 1 port) < Loc 1 p'"
  apply (cases p; cases p'; simp)
     apply eval+
  done

lemma l0_eq_l1[simp]:
  "Loc (n :: 2) (p :: 1 port) < Loc n p' \<longleftrightarrow> p < p'"
  unfolding less_location_def
  apply (cases p; cases p'; simp)
  done

declare BAPPEND_BTL[simp del]

find_theorems "if ?buf2.1 ?p1 = [] then BTL ?p1 ?buf1.1 >> ?buf2.1 else ?buf1.1 >> BTL ?p1 ?buf2.1"

lemma changes_above_impl_change_multiplicities_lt:
  "changes_above_impl c A \<Longrightarrow>
   (\<forall> l \<in> fst ` set A. \<forall> l' \<in> fst ` set B. l < l') \<Longrightarrow>
   changes_above_impl (change_multiplicities my_summ B c) A"
  unfolding  dataflow_topology_implied_frontier_alt_my_summ changes_above_impl_def
  apply (simp split: prod.splits)
  apply (intro impI allI ballI conjI; simp?; hypsubst_thin?)
  subgoal 
    using c_pts_change_multiplicities_gt_location by force
  subgoal
    apply (drule bspec)
     apply simp
    apply (drule spec)+
    apply (elim disjE)
     apply blast
    apply simp
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply simp_all
     apply force
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply auto
    apply (metis (mono_tags, opaque_lifting) basic_trans_rules(20,22) l0_eq_l1 less_eq_port.elims(3) num1_eq1 prod.sel(1) verit_comp_simplify(3))
    done
  subgoal
    apply (drule bspec)
     apply simp
    apply (drule spec)+
    apply (elim disjE)
     apply blast
    apply simp
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply simp_all
     apply (metis basic_trans_rules(19) l0_lt_l1 prod.sel(1))
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply simp_all
    using dual_order.strict_trans apply fastforce
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply simp_all
     apply fastforce
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply simp_all
    apply (metis (mono_tags, opaque_lifting) basic_trans_rules(20,22) l0_eq_l1 less_eq_port.elims(3) num1_eq1 prod.sel(1) verit_comp_simplify(3))
    done
  subgoal
    apply (drule bspec)
     apply simp
    apply (drule spec)+
    apply (elim disjE)
     apply blast
    apply simp
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply simp_all
     apply (metis basic_trans_rules(19) l0_lt_l1 prod.sel(1))
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply simp_all
    using dual_order.strict_trans apply fastforce
    apply (subst (1) c_pts_change_multiplicities_gt_location)
     apply simp_all
    apply fastforce
    done
  subgoal
    by auto
  done

lemma frontier_add_gt:
  "frontier A \<le> frontier B \<Longrightarrow>
   (\<forall> t t'. t \<in>#\<^sub>z C \<longrightarrow> t' \<in>#\<^sub>z B \<longrightarrow> t' < t) \<Longrightarrow>
   frontier (A + C) \<le> frontier B"
  unfolding less_eq_antichain_def
  apply auto
  by (smt (verit, del_insts) diff_diff_eq2 in_diff_zcount in_frontier_iff order.strict_trans2 trivial_dataflow_topology_interpretation.in_frontier_diff zcount_eq_zero_iff zmultiset_nonemptyE)


lemma frontier_less_equal_add_gt:
  "\<forall>x\<in> fst ` snd ` set B. t < x \<Longrightarrow>
  frontier_less_equal (frontier (c_pts c l)) t \<Longrightarrow>
  frontier_less_equal (frontier (c_pts (change_multiplicities my_summ B c) l)) t"
  unfolding c_pts_change_multiplicities frontier_less_equal_iff
  apply (rule frontier_add_gt)
   apply simp
  apply safe
  subgoal for t' t''
    apply (subgoal_tac "t'' = t")
    subgoal
      apply hypsubst_thin
      apply (drule bspec[of _ _ t'])
      subgoal premises prems
        using prems(2) 
        by (meson img_fst img_snd in_zmset_filter prems(2))
      apply assumption
      done
    subgoal premises prems
      using prems(4) by (simp add: set_zmset_single)
    done
  done


lemma frontier_less_equal_iff2:
  "frontier_less_equal f t \<longleftrightarrow> (\<exists> t'. t' \<in>\<^sub>A f \<and> t' \<le> t)"
  unfolding frontier_less_equal_def
  apply (auto simp add: in_frontier_iff)
  done

lemma frontier_less_equal_addI:
  "frontier_less_equal (frontier A) t \<or> frontier_less_equal (frontier B) t \<Longrightarrow>
   (\<forall> t. zcount A t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier_less_equal (frontier (A + B)) t"
  unfolding frontier_less_equal_iff
  apply safe
  using frontier_le_remove_l apply blast
  using frontier_le_remove_left apply blast
  done


lemma frontier_less_equal_add_cases:
  "frontier_less_equal (frontier (A + B)) t \<Longrightarrow>
   frontier_less_equal (frontier A) t \<or> frontier_less_equal (frontier B) t"
  unfolding frontier_less_equal_iff2
  using in_frontier_addD order_trans_rules(23) by blast

lemma frontier_less_equal_zcount_pos:
  " 0 < zcount A x \<Longrightarrow>
    frontier_less_equal (frontier A) x"
  unfolding frontier_less_equal_iff
  by (metis dataflow_topology_from_tree.obtain_frontier_elem in_frontier_iff less_eq_antichain_def less_irrefl zcount_add_zmset zcount_empty)

lemma propagate_all_implied_frontier_alt:
  "propagate_all my_summ c = Some c' \<Longrightarrow>
   dataflow_topology.implied_frontier_alt my_summ trivial_dataflow_topology_interpretation.followed_by c = dataflow_topology.implied_frontier_alt my_summ trivial_dataflow_topology_interpretation.followed_by c'"
  apply (rule ext)+
  apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
  done

lemma frontier_less_equal_implied_frontier:
  "frontier_less_equal (frontier (c_pts c l')) t \<Longrightarrow>
   l' \<le> l \<Longrightarrow>
   frontier_less_equal
   (dataflow_topology.implied_frontier_alt my_summ trivial_dataflow_topology_interpretation.followed_by c l) t"
  unfolding dataflow_topology_implied_frontier_alt_my_summ frontier_less_equal_iff2
  apply (clarsimp simp del: set_antichain1 set_antichain2 strictD_simp mset_set.infinite)
  apply (intro conjI impI; simp?; hypsubst_thin?)
  subgoal
    using loc_2_1_cases[where l=l'] apply -
    apply (auto simp add: less_port_def)
    using l0_lt_l1 less_imp_not_less 
      apply (metis basic_trans_rules(17) l0_eq_l1 less_eq_port.simps(3))
    using l0_lt_l1 less_imp_not_less not_less apply blast+
    done
  subgoal for t'
    using loc_2_1_cases[where l=l'] apply -
    apply (auto simp add: less_port_def; hypsubst_thin?)
    using fronteier_lt_add_ex  
       apply (smt (verit) Groups.add_ac(2) frontier_idempotent zmset_of_mset_set_ge_zero)
    using fronteier_lt_add_ex  
      apply (metis (no_types, opaque_lifting) frontier_idempotent zcount_zmset_of_nonneg)
    using fronteier_lt_add_ex  
    using l0_lt_l1 leD apply blast+
    done
  subgoal for t'
    using loc_2_1_cases[where l=l'] apply -
    apply (auto simp add: less_port_def; hypsubst_thin?)
    subgoal
      apply (subst (asm) frontier_idempotent[symmetric])
      apply (drule fronteier_lt_add_ex[where B="zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 1 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 1 (Trg 1))))))"])
        apply assumption
       apply clarsimp
      apply (simp add: Groups.add_ac(1,3))
      done
    subgoal
      apply (subst (asm) frontier_idempotent[symmetric])
      apply (drule fronteier_lt_add_ex[where B="(zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Trg 1)))))) +
                    (zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 1 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 1 (Trg 1))))))))"])
        apply assumption
       apply auto
      done
    subgoal
      apply (subst (asm) frontier_idempotent[symmetric])
      apply (drule fronteier_lt_add_ex[where B="zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Src 1)))))) +
                   (zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Trg 1)))))) +
                    zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 1 (Trg 1)))))))"])
        apply assumption
       apply clarsimp
      apply (simp add: Groups.add_ac(3))
      done
    subgoal
      apply (subst (asm) frontier_idempotent[symmetric])
      apply (drule fronteier_lt_add_ex[where B="zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Src 1)))))) +
                   (zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Trg 1)))))) +
                    (zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 1 (Src 1))))))))"])
        apply assumption
       apply clarsimp
      apply (simp add: Groups.add_ac(2,3))
      done
    done
  subgoal for t'
    using loc_2_1_cases[where l=l'] apply -
    apply (auto simp add: less_port_def; hypsubst_thin?)
    subgoal
      apply (subst (asm) frontier_idempotent[symmetric])
      apply (drule fronteier_lt_add_ex[where B="zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Src 1)))))) +
                   (zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 1 (Trg 1)))))))"])
        apply assumption
       apply clarsimp+
      apply (smt (verit, del_insts) Groups.add_ac(3) add_empty_zmultiset(1))
      done
    subgoal
      apply (subst (asm) frontier_idempotent[symmetric])
      apply (drule fronteier_lt_add_ex[where B="(zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Trg 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 1 (Trg 1)))))))"])
        apply assumption
       apply clarsimp+
      done
    subgoal
      by (meson l0_eq_l1 less_eq_port.simps(4) verit_comp_simplify(3))
    subgoal
      apply (subst (asm) frontier_idempotent[symmetric])
      apply (drule fronteier_lt_add_ex[where B="zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Src 1)))))) +
                   (zmset_of (mset_set (set_antichain (frontier (c_pts c (Loc 0 (Trg 1)))))))"])
        apply assumption
       apply clarsimp+
      apply (metis (no_types, lifting) Groups.add_ac(2) ab_semigroup_add_class.add_ac(1))
      done
    done
  subgoal for t
    by (metis loc_2_1_cases)
  done

lemma zcount_gt_0_zmulset_diff:
  "A - B = C \<Longrightarrow>
   (\<forall> t. zcount C t \<ge> 0) \<Longrightarrow>
   zcount B t > 0 \<Longrightarrow>
   0 < zcount A t"
  unfolding zmultiset_eq_iff
  apply (drule spec[of _ t])
  apply clarsimp
  apply (smt (verit, ccfv_threshold))
  done

lemma zcount_zmset_ge_zero:
  "\<forall>x. x \<in> snd ` snd ` set xs \<longrightarrow> 0 \<le> x \<Longrightarrow> \<forall>t. 0 \<le> zcount (zmset (map snd xs)) t"
  apply (induct xs)
   apply (auto 0 0 simp add: zcount_update_zmultiset)
  done

lemma in_frontier_zcount:
  "zcount A t > 0 \<Longrightarrow> \<exists>t'. t' \<in>\<^sub>A frontier A \<and> t' \<le> t"
  apply transfer
  apply (auto simp add: minimal_antichain_def dest: order_zmset_exists_foundation)
  done


lemma in_frontier_zcount_alt:
  "zcount A t > 0 \<Longrightarrow> \<exists>t' \<le> t. t' \<in>\<^sub>A frontier A"
  apply transfer
  apply (auto simp add: minimal_antichain_def dest: order_zmset_exists_foundation)
  done

lemma in_frontier_zmset_of_snd_mset:
  "t \<in> snd ` set xs \<Longrightarrow> \<exists>t'. t' \<in>\<^sub>A frontier (zmset_of (snd `# mset xs)) \<and> t' \<le> t"
  apply (rule in_frontier_zcount)
  apply auto
  done

lemma insort_key_last:
  "\<forall> a \<in> set xs. f a \<le> f x \<Longrightarrow>
   sorted (map f xs) \<Longrightarrow>
   f x \<notin> f ` set xs \<Longrightarrow>
   insort_key f x xs = xs @ [x]"
  by (induct xs) auto

lemma sorted_map_rmdups[intro]:
  "sorted (map f xs) \<Longrightarrow> sorted (map f (rmdups A xs))"
  apply (induct xs arbitrary: A)
   apply auto
  done

lemma fst_fold_rmdups:
  "sorted (map time caps) \<Longrightarrow>
   sorted xs \<Longrightarrow>
   (\<forall> t \<in> time ` set caps. \<forall> t' \<in> set xs. t \<le> t') \<Longrightarrow>
   fst ((fold (\<lambda>t (caps, os). if Cap t (1 :: 1) \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, f os t))) xs (caps, os)) = caps @ rmdups (set caps) (map (\<lambda> t. Cap t 1) xs)"
  apply (induct xs arbitrary: os caps rule: rev_induct)
   apply simp_all
  subgoal premises prems for x xs' os' caps'
    using prems(1)[symmetric] prems(2-) apply -
    apply (auto simp add: sorted_wrt_append split_beta split: if_splits)
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    apply (drule meta_mp)
     apply simp_all
    apply (subst insort_key_last)
       apply simp_all
      apply force
    subgoal
      apply (auto simp add: sorted_append)
      subgoal premises prems2
        using prems2(3) sorted_map_rmdups 
        by (metis (no_types, lifting) capability.sel(1) sorted_map sorted_wrt_map_mono)
      done
    subgoal
      apply auto
      apply (metis (full_types) capability.exhaust capability.sel(1) num1_eq1)
      done
    done
  done

lemma fold_rmdups:
  "sorted (map time caps) \<Longrightarrow>
   sorted xs \<Longrightarrow>
   (\<forall> t \<in> time ` set caps. \<forall> t' \<in> set xs. t \<le> t') \<Longrightarrow>
   (fold (\<lambda>t (caps, os). if Cap t 1 \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, mint_cap os 0 t)) xs (caps, os)) =
   (caps @ rmdups (set caps) (map (\<lambda> t. Cap t (1 :: 1)) xs), os\<lparr> inter := inter os @ map (\<lambda> t. (0, t, 1)) (rmdups (time ` set caps) xs) \<rparr>)"
  apply (induct xs arbitrary: os caps )
   apply simp
  subgoal premises prems for x xs' os' caps'
    apply (cases "Cap x 1 \<in> set caps'")
    subgoal
      using prems(1)[symmetric] prems(2-) apply -
      apply (drule meta_spec[of _ caps'])
      apply (drule meta_spec[of _ os'])
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply (simp add: sorted_append)
      apply (drule meta_mp)
       apply force
      apply simp
      apply (auto simp add: image_iff order_antisym sorted_append split_beta insort_key_last)
      done
    subgoal
      using prems(1)[symmetric] prems(2-) apply -
      apply (drule meta_spec[of _ "caps' @ [Cap x 1]"])
      apply (drule meta_spec[of _ "os'\<lparr> inter := inter os' @ [(0, x, 1)]\<rparr>"])
      apply (drule meta_mp)
       apply (simp add: sorted_append_bigger)
      apply (drule meta_mp)
       apply (simp add: sorted_append)
      apply (drule meta_mp)
       apply force
      apply (auto simp add: image_iff order_antisym sorted_append split_beta insort_key_last)
       apply (metis capability.exhaust capability.sel(1) num1_eq1)
      done
    done
  done

lemma map_time_rmdups:
  "map time (rmdups A (map (\<lambda>x. Cap (f x) (1 :: 1)) xs)) = rmdups (time ` A) (map f xs)"
  apply (induct xs arbitrary: A)
   apply (auto simp add: rev_image_eqI)
  apply (metis capability.exhaust capability.sel(1) num1_eq1)
  done

lemma set_fold_caps[simp]:
  "set (fold (\<lambda>(n, t) buf. buf(Cap t 1 := buf (Cap t 1) @ [n])) xs buf x) = set (buf x) \<union> fst ` {y \<in> set xs. Cap (snd y) 1 = x}"
  by (induct xs arbitrary: buf) (auto split: if_splits)

lemma outpu_fold[simp]:
  "outpu (fold (\<lambda>t os. os\<lparr>consu := A t os\<rparr>) xs s) = outpu s"
  "outpu (fold (\<lambda>t os. os\<lparr>inter := B t os\<rparr>) xs s) = outpu s"
  "outpu (fold (\<lambda>t os. os\<lparr>produ := C t os\<rparr>) xs s) = outpu s"
    apply (induct xs arbitrary: s)
       apply auto
  done

lemma outpu_fold_snd[simp]:
  "outpu (snd (fold (\<lambda>t (caps, os). if Cap t 1 \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, mint_cap os 0 t)) xs (caps, os))) =
   outpu os"
  apply (induct xs arbitrary: os caps)
   apply auto
  done

lemma consu_fold_snd[simp]:
  "consu (snd (fold (\<lambda>t (caps, os). if Cap t 1 \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, mint_cap os 0 t)) xs (caps, os))) =
   consu os"
  apply (induct xs arbitrary: os caps)
   apply auto
  done

lemma set_inter_snd_fold[simp]:
  "set (inter (snd (fold (\<lambda>t (caps, os). if Cap t (1 :: 1) \<in> set caps then (caps, os) else (insort_key time (Cap t 0) caps, mint_cap os 0 t)) xs os))) = 
   set (inter (snd os)) \<union> ((\<lambda> t. (0 :: 1, t, 1)) ` set xs - (\<lambda> t. (0, t, 1)) ` time ` set (fst os))"
  apply (cases os)
  apply simp
  apply hypsubst_thin
  subgoal for caps os
    apply (induct xs arbitrary: caps os)
     apply (auto simp add: image_iff set_insort_key split_beta split: if_splits)
     apply fastforce
    subgoal for xs caps os c
      apply (cases c)
      apply auto
      done
    done
  done

lemma consu_fold[simp]:
  "consu (fold (\<lambda>t os. os\<lparr>consu := consu os @ [(1, t, 1)]\<rparr>) xs os) = consu os @ map (\<lambda> t. (1, t, 1)) xs"
  by (induct xs arbitrary: os) auto

lemma inter_fold_consu[simp]:
  "inter (fold (\<lambda>t os. os\<lparr>consu := consu os @ [(1, t, 1)]\<rparr>) xs os) = inter os"
  by (induct xs arbitrary: os) auto

lemma filter_mset_False_alt:
  "(\<forall> y \<in># M. \<not> P y) \<Longrightarrow> {#y \<in># M. P y#} = {#}"
  using filter_mset_empty_conv by blast

lemma fold_Cap_eq_Nil:
  "buf (Cap t p) = [] \<Longrightarrow>
   (\<forall> t' \<in> snd ` set xs. t' \<noteq> t) \<Longrightarrow>
   fold (\<lambda>(n, t) buf. buf(Cap t p := buf (Cap t p) @ [n])) xs buf (Cap t p) = []"
  by (induct xs arbitrary: buf) auto

lemma lappend_to_lshift:
  "lfinite xs \<Longrightarrow>
   \<exists> xs'. lappend xs lxs  = xs' @@- lxs \<and> xs = llist_of xs'"
  by (metis lappend_llist_of llist_of_list_of)

lemma lmap_lshift_conv:
  "lmap f lxs = ys @@- lys \<longleftrightarrow> (\<exists> zs lzs. lxs = zs @@- lzs \<and> map f zs = ys \<and> lmap f lzs = lys)"
  apply (induct ys arbitrary: lys lxs)
   apply simp
  subgoal for a ys lys lxs
    apply simp
    apply (cases lxs)
     apply force
    apply simp
    apply auto
     apply hypsubst_thin
     apply (metis list.map(2) lshift.simps(2))
    apply auto
    done
  done

lemma ltake_lshift:
  "n \<le> length xs \<Longrightarrow> ltake n (xs @@- lxs) = llist_of (take n xs)"
  apply (induct n arbitrary: xs)
   apply (auto simp add: enat_0)
  subgoal for n xs
    apply (cases xs; simp)
    apply (auto simp flip: eSuc_enat)
    done
  done

lemma ldropn_lshift:
  "n \<le> length xs \<Longrightarrow> ldropn n (xs @@- lxs) = (drop n xs) @@- lxs"
  apply (induct n arbitrary: xs)
   apply (auto simp add: enat_0)
  subgoal for n xs
    apply (cases xs; simp)
    done
  done


lemma lzip_lshift_D:
  "lzip lxs lys = zs @@- lzs \<Longrightarrow> (\<exists> xs ys lxs' lys'. zs = zip xs ys \<and> length xs = length ys \<and> lzs = lzip lxs' lys' \<and> lxs = xs @@- lxs' \<and> lys = ys @@- lys')"
  apply (subst (asm) lappend_llist_of[symmetric])
  apply (drule lzip_eq_lappend_conv)
  apply safe
  subgoal for xs' xs'' ys' ys''
    apply (subgoal_tac "lfinite xs' \<and> lfinite ys'")
    subgoal
      using lappend_to_lshift 
      by (smt (verit, ccfv_threshold) enat.simps(1) list_of_llist_of llength_llist_of lzip_llist_of)
    subgoal
      by (metis lfinite_llength_enat lfinite_llist_of lfinite_lzip llength_eq_enat_lfiniteD)
    done
  done

lemma lconcat_eq_LCons_conv:
  "(lconcat xss = LCons x xs) =
   (\<exists>xs' xss' xss''. xss = xss' @@- (LCons (x # xs') xss'') \<and> xs = xs' @@- (lconcat xss'') \<and> set xss' \<subseteq> {xs. xs = []})"
  apply (subst lconcat_correct)
  apply (subst lconcat_eq_LCons_conv)
  apply (rule iffI)
  subgoal
    apply (elim exE conjE)
    subgoal for xs' xss' xss''
      apply (auto simp add: lmap_lshift_conv lappend_llist_of lmap_eq_LCons_conv)
      apply hypsubst_thin
      subgoal for zs ys ys'
        apply (rule exI[of _ "list_of xs'"])
        apply (rule exI[of _ "zs"])
        apply (rule exI[of _ "ys'"])
        apply (intro conjI)
        subgoal
          apply (rule arg_cong2[where f=lshift])
           apply simp
          apply (metis list_of_llist_of llist_of_eq_LCons_conv)
          done
        subgoal
          by (metis lappend_llist_of lconcat_correct lfinite_code(2) lfinite_llist_of llist_of_list_of)
        subgoal
          by auto
        done
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for xs' xss' xss''
      apply hypsubst_thin
      apply (rule exI[of _ "llist_of xs'"])
      apply (rule exI[of _ "map llist_of xss'"])
      apply (rule exI[of _ "lmap llist_of xss''"])
      apply (auto simp add: lappend_llist_of lconcat_correct)
      apply (metis llist.simps(13) llist_of.simps(2) lmap_lshift_conv)
      done
    done
  done

lemma lshift_ltake_ldrop:
  "lys = xs @@- lxs \<longleftrightarrow> (xs = list_of (ltake (length xs) lys) \<and> lxs = ldrop (length xs) lys)"
  apply (induct xs arbitrary: lxs)
   apply (simp add: enat_0)
   apply blast
  subgoal for a xs lxs
    apply (auto simp add: ldrop_enat ldropn_lshift ltake_lshift simp flip: eSuc_enat)
    apply (metis eSuc_enat_iff enat.simps(3) enat_ord_simps(4) lappend_llist_of lappend_ltake_ldrop lfinite_ltake llist_of_list_of lshift_simps(2))
    done
  done

lemma filter_True_False:
  "\<forall>x\<in>set xs. \<not> P x \<Longrightarrow> filter (\<lambda> x. \<not> P x) xs = xs"
  by auto

lemma rmdups_NilD:
  "rmdups S xs = [] \<Longrightarrow> set xs \<subseteq> S"
  by (induct xs arbitrary: S) (auto split: if_splits)


lemma zmset_map_snd_concat:
  "zmset (map snd (concat (map (\<lambda>t'. [(1, t', - 1), (1, Suc t', 1)]) xs))) =
   - zmset (map (\<lambda> t. (t, 1)) xs) + zmset (map (\<lambda> t. (Suc t, 1)) xs)"
  apply (induct xs rule: rev_induct)
   apply simp_all
  apply (smt (verit, del_insts) Executable.update_zmultiset_plus ab_group_add_class.ab_diff_conv_add_uminus diff_add_eq_diff_diff_swap right_minus_eq update_zmultiset_plus_comm)
  done

lemma zmset_of_image_mset:
  "zmset_of (f `# mset_set A) = image_zmset f (zmset_of (mset_set A))"
  unfolding zmultiset_eq_iff
  apply (clarsimp simp add: count_image_mset zcount_image_zmset)
  apply (metis (no_types, lifting) Collect_cong Int_def mem_zmset_of)
  done


lemma zmset_of_Suc_minus:
  "zmset_of (Suc `# mset_set {n..n + m}) - zmset_of (mset_set {n..n + m}) + {#n#}\<^sub>z =
   {#Suc (n + m)#}\<^sub>z"
  unfolding zmultiset_eq_iff
  apply (auto simp add:  count_mset_set_finite_iff vimage_Suc_insert_Suc count_image_mset)
  apply (subst Int_absorb2)
   apply clarsimp
  apply (metis card_1_singleton_iff list_decode.cases order_antisym vimage_Suc_insert_Suc vimage_empty zero_order(1))
  done

lemma zmset_of_Suc_minus_empty:
  "zmset_of (Suc `# mset_set {n..<n + m}) - zmset_of (mset_set {n..n + m}) + {#n#}\<^sub>z = {#}\<^sub>z"
  unfolding zmultiset_eq_iff
  apply (auto simp add:  count_mset_set_finite_iff vimage_Suc_insert_Suc count_image_mset)
  apply (subst Int_absorb2)
   apply clarsimp
  apply (metis card_1_singleton_iff list_decode.cases order_antisym vimage_Suc_insert_Suc vimage_empty zero_order(1))
  done


lemma add_zmset_zmset_map_Suc_minus:
  "add_zmset n (zmset (map (\<lambda>t. (Suc t, 1)) [n..< n + m]) - zmset (map (\<lambda>t. (t, 1)) [n..< n + m])) = {#n + m#}\<^sub>z"
  apply (induct m arbitrary: n)
   apply simp_all
  apply (metis (no_types, lifting) Groups.add_ac(2) diff_add_zmset_swap eq_diff_eq update_zmultiset_singleton(2))
  done

lemma dataflow_op_inp_m_top_source_op_aux:
  \<open>summ sg = my_summ \<Longrightarrow>
   edges sg = (\<lambda> l. if l = Loc 0 (Src 1) then [Loc 1 (Trg 1)] else []) \<Longrightarrow>
   consu os1 = [] \<Longrightarrow>
   xs 0 = outpu os2 0 \<Longrightarrow>
   ys 0 = max_from_buf caps buf2 ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0) \<Longrightarrow>
   (\<forall> x \<in> set (buf1 (Inr (1, 0))). isr x) \<Longrightarrow>
   sorted (map time caps) \<Longrightarrow>
   (\<forall>m \<in> snd ` snd ` set (consu os2). m \<ge> 0) \<Longrightarrow>

   obtain_progress os1 = (a, st1) \<Longrightarrow>
   obtain_progress os2 = (b, st2) \<Longrightarrow>
   c = change_multiplicities (summ sg) (extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2) (pt_tr sg) \<Longrightarrow>
   c_pts c (Loc 1 (Trg 0)) = zmset_of (mset (map snd ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0))) \<Longrightarrow>
   c_pts c (Loc 0 (Src 0)) = input_cap inps n \<Longrightarrow>
   c_pts c (Loc 0 (Trg 1)) = {#}\<^sub>z \<Longrightarrow>
   c_pts c (Loc 1 (Src 0)) = zmset_of (mset (map time caps)) \<Longrightarrow>

   front os2 0 \<le> frontier (c_imp (pt_tr sg) (Loc 1 (Trg 0))) \<Longrightarrow>
   (\<forall> l. frontier (c_imp (pt_tr sg) l) \<le> dataflow_topology.implied_frontier_alt my_summ (+) (pt_tr sg) l) \<Longrightarrow>

   (\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). frontier_less_equal (dataflow_topology.implied_frontier_alt my_summ (+) c (Loc 1 (Trg 0))) t) \<Longrightarrow>

   dataflow_topology.inv_imps_work_sum (summ sg) (-+-) (pt_tr sg) \<Longrightarrow>
   dataflow_topology.inv_implications_nonneg (pt_tr sg) \<Longrightarrow>
   dataflow_topology.inv_imp_plus_work_nonneg (pt_tr sg) \<Longrightarrow>
   changes_non_zero (extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2) \<Longrightarrow>
   changes_above_impl (pt_tr sg) (extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2) \<Longrightarrow>
   changes_above_impl (change_multiplicities (summ sg) (extract_progress 1 (edges sg) st2) (pt_tr sg)) (extract_progress 0 (edges sg) st1) \<Longrightarrow>
   changes_above_impl (change_multiplicities (summ sg) (extract_progress 0 (edges sg) st1) (pt_tr sg)) (extract_progress 1 (edges sg) st2) \<Longrightarrow>

   (\<forall> t m. (1, t, m) \<in> set (inter os2) \<longrightarrow> 0 \<le> zcount (zmset (map snd (inter os2))) t \<longrightarrow>  (\<exists> m. (1, t, m) \<in> set (consu os2))) \<Longrightarrow>
   (\<forall> t. zcount (c_pts (pt_tr sg) (Loc 1 (Src 1))) t \<ge> 0) \<Longrightarrow>

   (\<forall> cap \<in> set caps. time cap < n 0) \<Longrightarrow>
   (\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). t < n 0) \<Longrightarrow>
   (\<forall> t\<ge>n 0. buf2 (Cap t 1) = []) \<Longrightarrow>

   (\<forall> t m. (1, t, m) \<in> set (produ os1) \<union> set (inter os1) \<longrightarrow> (\<exists> t' \<le> t. zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) t' > 0)) \<Longrightarrow>

   (\<forall> (x, t) \<in> projr ` set (buf1 (Inr (1, 1))) \<union> set (outpu os1 0). \<forall> cap \<in> set caps. time cap \<le> t) \<Longrightarrow>
   (sorted (map snd ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0))) \<Longrightarrow>

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
        using prems(34) apply -
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
            apply (clarsimp simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            subgoal premises
              apply (induct caps)
              apply auto
              apply (metis Num.of_nat_simps(1) One_nat_def insert_Diff_zmset int_ops(2) semiring_norm(52) union_zmset_add_zmset_right update_zmultiset_simps(1,3))
              done
            done
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(1,10,9,2,3,9,10,11,12,13,14,15,18)
            by (clarsimp simp del:  simp add: dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(19) by simp
          subgoal using prems(20) by simp
          subgoal using prems(21) by simp
          subgoal using prems(1,2,3,9,10,11,12,13,14,15,22) apply -
            apply auto
            unfolding changes_non_zero_def extract_progress_def comp_def
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply force
            done
          subgoal using prems(2,9,10,23,11) prems(15)[symmetric] apply -
            unfolding  extract_progress_def comp_def
            apply (auto simp add: dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply (rule changes_above_impl_extend[where B="map (\<lambda>x. (Loc 1 (Src 1), time x, - 1)) (filter (\<lambda>cap. \<not> frontier_less_equal (front os2 1) (time cap)) caps)"])
            apply assumption
            apply simp_all
            subgoal premises prems2
              apply (auto simp add: changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              subgoal for t
                using prems2(5) apply -
                apply (drule zmset_of_eq_add[simplified])
                apply fast
                apply (elim disjE)
                subgoal
                  using frontier_less_equal_zcount_pos  
                  by (smt (verit) Groups.add_ac(3) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_le_trans zcount_zmset_of_nonneg zmset_of_plus)
                subgoal
                  using prems2(4) apply -     
                  apply (subgoal_tac "\<exists> m.(Loc 1 (Src 1), time t, m) \<in> (\<lambda>(p, y). (Loc 1 (Src 1), y)) ` set (operator_state.inter os2)")
                  subgoal
                    apply (auto simp add: changes_above_impl_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    apply (drule bspec[of _ _ "(Loc 1 (Src 1), time t, _)"])
                    apply simp
                    apply fast
                    apply (auto simp add: changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    done
                  subgoal
                    by (meson pair_imageI zcount_gt_0_in_set_2)
                  done
                done
              done
            done
          subgoal premises prems2
            apply simp
            using  prems(15)[symmetric] prems(1,2,9,10,11,24) apply -
            unfolding  extract_progress_def comp_def
            apply (auto simp add: dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply (rule changes_above_impl_change_multiplicities_lt)
            apply assumption
            apply (auto simp add: less_port_def split: prod.splits)
            done
          subgoal premises prems2
            apply simp
            using  prems(15)[symmetric] prems(1,2,9,10,11,25) apply -
            unfolding  extract_progress_def comp_def
            apply (auto simp add: dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply (rule changes_above_impl_extend[where B="map (\<lambda>x. (Loc 1 (Src 1), time x, - 1)) (filter (\<lambda>cap. \<not> frontier_less_equal (front os2 1) (time cap)) caps)"])
            apply assumption
            apply simp_all
            subgoal premises prems2
              apply (auto simp add: changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              subgoal for t
                using prems2(1) apply -
                apply (drule zmset_of_eq_add[simplified])
                apply fast
                apply (elim disjE)
                subgoal
                  using frontier_less_equal_zcount_pos  
                  by (smt (verit) Groups.add_ac(3) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_le_trans zcount_zmset_of_nonneg zmset_of_plus)
                subgoal
                  using prems2(4) apply -     
                  apply (subgoal_tac "\<exists> m.(Loc 1 (Src 1), time t, m) \<in> (\<lambda>(p, y). (Loc 1 (Src 1), y)) ` set (operator_state.inter os2)")
                  subgoal
                    apply (auto simp add: changes_above_impl_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    apply (drule bspec[of _ _ "(Loc 1 (Src 1), time t, _)"])
                    apply simp
                    apply fast
                    apply (auto simp add: changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    done
                  subgoal
                    by (meson pair_imageI zcount_gt_0_in_set_2)
                  done
                done
              done
            done
          subgoal
            using prems(26) apply -
            apply simp
            apply (intro allI impI)
            apply (elim disjE conjE exE)
            subgoal for t m
              apply (drule spec)+
              apply (drule mp)
              apply blast
              apply (drule mp)
              apply (subgoal_tac "zcount (zmset (map (snd \<circ> (\<lambda>cap. (1 :: 1, time cap, - 1))) (filter (\<lambda>cap. \<not> frontier_less_equal (front os2 1) (time cap)) caps))) t \<le> 0")
              subgoal
                by linarith
              subgoal premises
                by (induct caps) (auto simp add: zcount_update_zmultiset)
              apply auto
              done
            subgoal for t m
              apply auto
              apply hypsubst_thin
              using prems(1,2,11,9,10,15) apply -
              unfolding extract_progress_def
              apply (auto simp add: c_pts_change_multiplicities zmultiset_eq_iff)
              apply hypsubst_thin
              subgoal for x
                apply (drule spec[of _ "time x"])+
                apply (drule mp)
                subgoal premises prems2
                  using prems2(3,4,5) apply -
                  unfolding comp_def
                  apply (simp add: zmset_map_minus_one_zmset_of count_image_mset)
                  apply (subgoal_tac "int (count (mset caps) x) \<le> zcount (zmset (map snd (operator_state.inter os2))) (time x)")
                  subgoal
                    by (smt (z3) count_mset_0_iff int_zle_neg zcount_gt_0_in_set_2)
                  subgoal
                    apply (erule order.trans[rotated])
                    apply (rule member_le_sum)
                    apply auto
                    done
                  done
                apply (drule mp)
                subgoal
                  unfolding comp_def
                  apply (simp add: zmset_map_minus_one_zmset_of count_image_mset)
                  apply (subgoal_tac "int (count (mset caps) x) \<le> zcount (zmset (map snd (operator_state.inter os2))) (time x)")
                  subgoal
                    by (smt (z3) count_mset_0_iff int_zle_neg zcount_gt_0_in_set_2)
                  subgoal
                    apply (erule order.trans[rotated])
                    apply (rule member_le_sum)
                    apply auto
                    done
                  done
                apply assumption
                done
              done
            done
          subgoal
            using prems(27) by simp
          subgoal
            using prems(28) by auto
          subgoal
            using prems(29) by simp
          subgoal
            using prems(30) by simp
          subgoal
            using prems(31) by simp
          subgoal
            using prems(32) by simp
          subgoal
            using prems(33) by simp
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
                          subgoal for a b c
                            using prems(18) apply -
                            apply (drule spec[of _ "(a, b)"])
                            apply (drule mp)
                            apply force                            
                            apply (auto split: prod.splits)
                            apply hypsubst_thin
                            apply (rule frontier_less_equal_le_trans)
                            apply assumption
                            apply (rule order.trans)
                            using prems(16) apply simp
                            using prems(11) apply simp
                            apply (rule order.trans)
                            using prems(17) apply -
                            apply (drule spec)
                            apply assumption
                            using prems(1) apply simp
                            apply (rule frontier_less_equal_change_multiplicities_alt)
                            using prems(23)[unfolded changes_above_impl_def] apply blast
                            done
                          subgoal for a b
                            using prems(18) apply -
                            apply (drule spec[of _ "(a, b)"])
                            apply (drule mp)
                            apply force                            
                            apply (auto split: prod.splits)
                            apply hypsubst_thin
                            apply (rule frontier_less_equal_le_trans)
                            apply assumption
                            apply (rule order.trans)
                            using prems(16) apply simp
                            using prems(11) apply simp
                            apply (rule order.trans)
                            using prems(17) apply -
                            apply (drule spec)
                            apply assumption
                            using prems(1) apply simp
                            apply (rule frontier_less_equal_change_multiplicities_alt)
                            using prems(23)[unfolded changes_above_impl_def] apply blast
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
                          subgoal for a b c
                            using prems(18) apply -
                            apply (drule spec[of _ "(a, b)"])
                            apply (drule mp)
                            apply force                            
                            apply (auto split: prod.splits)
                            apply (rule frontier_less_equal_le_trans)
                            apply assumption
                            apply (rule order.trans)
                            using prems(16) apply simp
                            using prems(11) apply simp
                            apply (rule order.trans)
                            using prems(17) apply -
                            apply (drule spec)
                            apply assumption
                            using prems(1) apply simp
                            apply (rule frontier_less_equal_change_multiplicities_alt)
                            using prems(23)[unfolded changes_above_impl_def] apply blast
                            done
                          subgoal for a b
                            using prems(18) apply -
                            apply (drule spec[of _ "(a, b)"])
                            apply (drule mp)
                            apply force                            
                            apply (auto split: prod.splits)
                            apply (rule frontier_less_equal_le_trans)
                            apply assumption
                            apply (rule order.trans)
                            using prems(16) apply simp
                            using prems(11) apply simp
                            apply (rule order.trans)
                            using prems(17) apply -
                            apply (drule spec)
                            apply assumption
                            using prems(1) apply simp
                            apply (rule frontier_less_equal_change_multiplicities_alt)
                            using prems(23)[unfolded changes_above_impl_def] apply blast
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
                      subgoal for a b c
                        using prems(18) apply -
                        apply (drule spec[of _ "(a, b)"])
                        apply (drule mp)
                        apply force                            
                        apply (auto split: prod.splits)
                        apply (rule frontier_less_equal_le_trans)
                        apply assumption
                        apply (rule order.trans)
                        using prems(16) apply simp
                        using prems(11) apply simp
                        apply (rule order.trans)
                        using prems(17) apply -
                        apply (drule spec)
                        apply assumption
                        using prems(1) apply simp
                        apply (rule frontier_less_equal_change_multiplicities_alt)
                        using prems(23)[unfolded changes_above_impl_def] apply blast
                        done
                      subgoal for a b
                        using prems(18) apply -
                        apply (drule spec[of _ "(a, b)"])
                        apply (drule mp)
                        apply force                            
                        apply (auto split: prod.splits)
                        apply (rule frontier_less_equal_le_trans)
                        apply assumption
                        apply (rule order.trans)
                        using prems(16) apply simp
                        using prems(11) apply simp
                        apply (rule order.trans)
                        using prems(17) apply -
                        apply (drule spec)
                        apply assumption
                        using prems(1) apply simp
                        apply (rule frontier_less_equal_change_multiplicities_alt)
                        using prems(23)[unfolded changes_above_impl_def] apply blast
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
                      subgoal for a b c
                        using prems(18) apply -
                        apply (drule spec[of _ "(a, b)"])
                        apply (drule mp)
                        apply force                            
                        apply (auto split: prod.splits)
                        apply (rule frontier_less_equal_le_trans)
                        apply assumption
                        apply (rule order.trans)
                        using prems(16) apply simp
                        using prems(11) apply simp
                        apply (rule order.trans)
                        using prems(17) apply -
                        apply (drule spec)
                        apply assumption
                        using prems(1) apply simp
                        apply (rule frontier_less_equal_change_multiplicities_alt)
                        using prems(23)[unfolded changes_above_impl_def] apply blast
                        done
                      subgoal for a b
                        using prems(18) apply -
                        apply (drule spec[of _ "(a, b)"])
                        apply (drule mp)
                        apply force                            
                        apply (auto split: prod.splits)
                        apply (rule frontier_less_equal_le_trans)
                        apply assumption
                        apply (rule order.trans)
                        using prems(16) apply simp
                        using prems(11) apply simp
                        apply (rule order.trans)
                        using prems(17) apply -
                        apply (drule spec)
                        apply assumption
                        using prems(1) apply simp
                        apply (rule frontier_less_equal_change_multiplicities_alt)
                        using prems(23)[unfolded changes_above_impl_def] apply blast
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
                      subgoal for a b c
                        using prems(18) apply -
                        apply (drule spec[of _ "(a, b)"])
                        apply (drule mp)
                        apply force                            
                        apply (auto split: prod.splits)
                        apply (rule frontier_less_equal_le_trans)
                        apply assumption
                        apply (rule order.trans)
                        using prems(16) apply simp
                        using prems(11) apply simp
                        apply (rule order.trans)
                        using prems(17) apply -
                        apply (drule spec)
                        apply assumption
                        using prems(1) apply simp
                        apply (rule frontier_less_equal_change_multiplicities_alt)
                        using prems(23)[unfolded changes_above_impl_def] apply blast
                        done
                      subgoal for a b
                        using prems(18) apply -
                        apply (drule spec[of _ "(a, b)"])
                        apply (drule mp)
                        apply force                            
                        apply (auto split: prod.splits)
                        apply (rule frontier_less_equal_le_trans)
                        apply assumption
                        apply (rule order.trans)
                        using prems(16) apply simp
                        using prems(11) apply simp
                        apply (rule order.trans)
                        using prems(17) apply -
                        apply (drule spec)
                        apply assumption
                        using prems(1) apply simp
                        apply (rule frontier_less_equal_change_multiplicities_alt)
                        using prems(23)[unfolded changes_above_impl_def] apply blast
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
                      subgoal for a b c
                        using prems(18) apply -
                        apply (drule spec[of _ "(a, b)"])
                        apply (drule mp)
                        apply force                            
                        apply (auto split: prod.splits)
                        apply (rule frontier_less_equal_le_trans)
                        apply assumption
                        apply (rule order.trans)
                        using prems(16) apply simp
                        using prems(11) apply simp
                        apply (rule order.trans)
                        using prems(17) apply -
                        apply (drule spec)
                        apply assumption
                        using prems(1) apply simp
                        apply (rule frontier_less_equal_change_multiplicities_alt)
                        using prems(23)[unfolded changes_above_impl_def] apply blast
                        done
                      subgoal for a b
                        using prems(18) apply -
                        apply (drule spec[of _ "(a, b)"])
                        apply (drule mp)
                        apply force                            
                        apply (auto split: prod.splits)
                        apply (rule frontier_less_equal_le_trans)
                        apply assumption
                        apply (rule order.trans)
                        using prems(16) apply simp
                        using prems(11) apply simp
                        apply (rule order.trans)
                        using prems(17) apply -
                        apply (drule spec)
                        apply assumption
                        using prems(1) apply simp
                        apply (rule frontier_less_equal_change_multiplicities_alt)
                        using prems(23)[unfolded changes_above_impl_def] apply blast
                        done
                      done
                    done
                  done
                done
              done
            done
          done
        prefer 10
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
              using prems(19-) apply simp_all 
              done
            done
          subgoal using prems(1,2,3,9,10,11,12,18)
            by (clarsimp simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
          subgoal using prems(1,2,3,9,10,11,12,19) apply -
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply (drule propagate_all_frontier_c_imp_correctness[])
              using prems(19-) by auto
            done
          subgoal using prems(1,2,3,9,10,11,12,19) apply -
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply (drule propagate_all_frontier_c_imp_correctness[])
              using prems(19-) by auto
            done
          subgoal using prems(1,2,3,9,10,11,12,19) apply -
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply (drule propagate_all_frontier_c_imp_correctness[])
              using prems(19-) by auto
            done
          subgoal using prems(1,2,3,9,10,11,12,19) apply -
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply (drule propagate_all_frontier_c_imp_correctness[])
              using prems(19-) by auto
            done
          subgoal premises 
            using prems(1,2,9,10,23) apply -
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply (drule propagate_all_implied_frontier_alt)
              unfolding changes_above_impl_def
              apply simp
              done
            done
          subgoal premises
            using prems(1,2,3,9,10,24) apply -    
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply (drule propagate_all_preserves_c_pts)
              unfolding changes_above_impl_def extract_progress_def 
              apply auto
              subgoal
                apply (drule bspec)
                apply blast
                apply auto
                subgoal
                  unfolding dataflow_topology_implied_frontier_alt_my_summ 
                  apply simp
                  apply (metis (no_types, lifting) c_pts_change_multiplicities_cong)
                  done
                done
              subgoal
                apply (drule bspec)
                apply blast
                apply auto
                subgoal
                  unfolding dataflow_topology_implied_frontier_alt_my_summ 
                  apply simp
                  apply (metis (no_types, lifting) c_pts_change_multiplicities_cong)
                  done
                done
              done
            done
          subgoal premises
            using prems(1,2,3,9,10,25) apply -    
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply (drule propagate_all_preserves_c_pts)
              unfolding changes_above_impl_def extract_progress_def 
              apply auto
              subgoal
                apply (drule bspec)
                apply blast
                apply auto
                subgoal
                  unfolding dataflow_topology_implied_frontier_alt_my_summ 
                  apply simp
                  apply (metis (no_types, lifting) c_pts_change_multiplicities_cong)
                  done
                done
              subgoal
                apply (drule bspec)
                apply blast
                apply auto
                subgoal
                  unfolding dataflow_topology_implied_frontier_alt_my_summ 
                  apply simp
                  apply (smt (verit, best) c_pts_change_multiplicities_cong)
                  done
                done
              done
            done
          subgoal
            apply simp
            using prems(26) apply auto
            done
          subgoal
            apply simp
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply auto
              apply (drule propagate_all_preserves_c_pts)
              using prems(27) apply auto
              done
            done
          subgoal
            using prems(28) by simp
          subgoal
            using prems(29) by simp
          subgoal
            using prems(30) by simp
          subgoal
            apply simp
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp)
            subgoal for c
              apply (drule propagate_all_preserves_c_pts)
              using prems(1,2,9,10,11,31) apply -
              apply auto
              done
            done
          subgoal
            apply simp
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp?)
            subgoal for c
              apply (drule propagate_all_preserves_c_pts)
              using prems(1,2,9,10,11,32) apply -
              apply auto
              done
            done
          subgoal
            apply simp
            apply (cases "propagate_all (summ sg) (pt_tr sg)"; simp?)
            subgoal for c
              apply (drule propagate_all_preserves_c_pts)
              using prems(1,2,9,10,11,33) apply -
              apply auto
              done
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
                done
              done
            subgoal
              by (auto simp add: comp_def)
            done
          done
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
          subgoal using prems(9,2,3,9,10,11,12) apply -
            by (auto simp add: diff_add_eq extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13)
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14,15) apply -
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) apply -
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            subgoal for l
              apply (drule spec[of _ l])
              apply (rule Orderings.preorder_class.order_trans)
              apply assumption
              subgoal premises prems2
                using prems(1,2,9,10,11,12,13,14,23) prems(15)[symmetric] apply -
                unfolding dataflow_topology_implied_frontier_alt_my_summ
                apply simp
                apply (intro allI impI conjI)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  apply (auto 0 0 simp flip: add.assoc simp add: dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                  apply (intro frontier_le_add)
                  apply (meson frontier_below_eq_frontier_plus_pos frontier_le_remove_l zcount_zmset_of_nonneg)
                  apply (metis (no_types, lifting) add.commute frontier_below_eq_frontier_plus_pos frontier_le_remove_l zcount_zmset_of_nonneg)
                  apply simp
                  apply (intro frontier_le_add)
                  apply (smt (verit, ccfv_threshold) add.commute frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_remove_l zcount_union zcount_zmset_of_nonneg)
                  subgoal
                    apply (elim changes_above_impl_elim conjE)
                    apply (rule le_frontier_frontier_less_equal)
                    unfolding changes_above_impl_def
                    apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ split_beta)
                    apply (smt (z3) Groups.add_ac(2) group_cancel.add2 split_pairs2)
                    done
                  subgoal
                    apply simp
                    apply (rule frontier_le_minus_gen)
                    apply (simp add: frontier_le_remove_left)   
                    subgoal premises
                      using prems(8) zcount_zmset_ge_zero by blast
                    done
                  done
                subgoal
                  apply (auto 0 0 simp flip: add.assoc simp add: dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                  apply (intro frontier_le_add)
                  apply (meson frontier_below_eq_frontier_plus_pos frontier_le_remove_l zcount_zmset_of_nonneg)
                  apply (metis (no_types, lifting) add.commute frontier_below_eq_frontier_plus_pos frontier_le_remove_l zcount_zmset_of_nonneg)
                  apply simp
                  apply (rule frontier_le_minus_gen)
                  apply (simp add: frontier_le_remove_left)   
                  subgoal premises
                    using prems(8) zcount_zmset_ge_zero by blast
                  done
                done
              done
            done
          subgoal premises
            using prems(1,2,11,10,9,18) apply -
            apply clarsimp
            subgoal for a b
              apply (drule spec[of _ a])
              apply (drule spec[of _ b])
              apply (auto 0 0 simp flip: add.assoc simp add: dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              apply (metis zmset_subset_eq_zmultiset_union_diff_commute)+
              done
            done
          subgoal premises
            using prems(1,19) apply -
            apply simp
            using change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ] apply -
            apply (drule meta_spec)+
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (elim conjE)
            apply assumption
            prefer 3
            apply (rule refl)
            subgoal
              using prems(2,9,10,22,23) apply -
              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              done
            subgoal
              apply safe
              subgoal for l t x
                using prems(2,9,10,17,23) apply -
                apply (drule spec[of _ l])
                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                done
              done
            done
          subgoal premises
            using prems(1,20) apply -
            apply simp
            using change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ] apply -
            apply (drule meta_spec)+
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (elim conjE)
            apply assumption
            prefer 3
            apply (rule refl)
            subgoal
              using prems(2,9,10,22,23) apply -
              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              done
            subgoal
              apply safe
              subgoal for l t x
                using prems(2,9,10,17,23) apply -
                apply (drule spec[of _ l])
                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                done
              done
            done
          subgoal premises
            using prems(1,21) apply -
            apply simp
            using change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ] apply -
            apply (drule meta_spec)+
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (elim conjE)
            apply assumption
            prefer 3
            apply (rule refl)
            subgoal
              using prems(2,9,10,22,23) apply -
              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              done
            subgoal
              apply safe
              subgoal for l t x
                using prems(2,9,10,17,23) apply -
                apply (drule spec[of _ l])
                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                done
              done
            done
          subgoal premises
            using prems(1,22) apply -
            unfolding changes_non_zero_def
            apply simp
            using prems(2,9,10,22,23) apply -
            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          subgoal premises
            using prems(1,2,9,10,24) 
            by (auto simp add: extract_progress_def)
          subgoal premises
            using prems(1,2,9,10,24) by (auto simp add: extract_progress_def)
          subgoal premises
            by (auto simp add: extract_progress_def changes_above_impl_def)
          subgoal
            using prems(26) by auto
          subgoal
            apply simp
            using prems(1,2,27,15,11,9,10) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
            done
          subgoal
            using prems(28) by simp
          subgoal
            using prems(29) by simp
          subgoal
            using prems(30) by simp
          subgoal
            using prems(1,2,31) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
            done
          subgoal
            using prems(1,2,32) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
            done
          subgoal
            using prems(1,2,33) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
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
                done
              done
            subgoal
              by (auto simp add: comp_def)
            done
          done
        prefer 7
        subgoal for batch lxs
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
          subgoal using prems(3) by (simp add: produce_def)
          apply (rule refl)+
          subgoal using prems(6) by simp
          subgoal using prems(7) apply -
            using sorted_filter by blast
          subgoal using prems(8) by simp
          subgoal using prems(9,2,3,9,10,11,12)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13) apply -
            apply (auto simp add: ac_simps update_zmultiset_replicate input_cap_def zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply (metis arith_simps(49) diff_add_zmset zmultiset_move_add_other_side)
            done
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14,15) 
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal 
            using prems(1,6,10,9,2,3,9,10,11,18,13,14,12) apply -
            apply (auto 0 0 simp add: ac_simps split_beta input_cap_def update_zmultiset_replicate  produce_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            subgoal for x t
              apply (drule spec[of _ x])
              apply (drule spec[of _ t])
              apply auto
              subgoal
                unfolding frontier_less_equal_iff2
                apply auto
                subgoal premises prems4
                  using prems4(13) apply -
                  apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier
                  (zmset_of (mset_set (set_antichain (frontier (zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#})))))) \<and> t' \<le> t")
                  subgoal
                    using fronteier_lt_add_ex zmset_of_mset_set_ge_zero by blast
                  subgoal
                    apply simp
                    apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (zmset_of (snd `# mset (outpu os1 1))) \<and> t' \<le> t")
                    subgoal
                      apply safe
                      subgoal for t'
                        apply (simp add: zmset_of_plus)
                        apply (rule in_frontier_in_frontier_add_alt[of t'])
                        apply auto
                        done
                      done
                    subgoal
                      by (auto intro: in_frontier_zmset_of_snd_mset)
                    done
                  done
                done
              subgoal
                unfolding frontier_less_equal_iff2
                apply auto
                subgoal premises prems4
                  using prems4(13) apply -
                  apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier
                  (zmset_of (mset_set (set_antichain (frontier (zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#})))))) \<and> t' \<le> t")
                  subgoal
                    using fronteier_lt_add_ex zmset_of_mset_set_ge_zero by blast
                  subgoal
                    apply simp
                    apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (zmset_of (snd `# mset (outpu os1 1))) \<and> t' \<le> t")
                    subgoal
                      apply safe
                      subgoal for t'
                        apply (simp add: zmset_of_plus)
                        apply (rule in_frontier_in_frontier_add_alt[of t'])
                        apply auto
                        done
                      done
                    subgoal
                      by (auto intro: in_frontier_zmset_of_snd_mset)
                    done
                  done
                done
              done
            subgoal for a t x
              unfolding frontier_less_equal_iff2
              apply (cases x; simp; hypsubst_thin)
              apply force
              subgoal premises prems4 for b
                using prems4(14) apply -
                apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier
                  (zmset_of (mset_set (set_antichain (frontier (zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#})))))) \<and> t' \<le> t")
                subgoal
                  using fronteier_lt_add_ex zmset_of_mset_set_ge_zero by blast
                subgoal
                  apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (zmset_of (mset_set (set_antichain (frontier (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#})))))) \<and> t' \<le> t")
                  subgoal
                    apply simp
                    apply safe
                    subgoal for t'
                      apply (simp add: zmset_of_plus)
                      apply (smt (verit, del_insts) in_frontier_in_frontier_add_alt union_ac(2) zcount_zmset_of_nonneg zmset_of_plus)
                      done
                    done
                  subgoal
                    apply simp
                    apply (rule in_frontier_zcount)
                    apply force
                    done
                  done
                done
              done
            subgoal for x t
              apply (drule spec[of _ x])
              apply (drule spec[of _ t])
              apply auto
              subgoal
                unfolding frontier_less_equal_iff2
                apply (subst (5) add.commute)
                apply (subst (2) add.assoc[symmetric])
                apply simp
                apply (subst (1) add.assoc[symmetric])
                apply (auto simp add: ac_simps)
                subgoal premises prems4
                  using prems4(14) apply -
                  apply (subgoal_tac "\<exists>t'\<le>t. t' \<in>\<^sub>A frontier (zmset_of (mset_set (set_antichain (frontier (zmset_of {#n 1. x \<in># mset batch#} + zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#}))))))")
                  subgoal
                    apply (subst (2) add.commute)
                    apply (meson fronteier_lt_add_ex zmset_of_mset_set_ge_zero)
                    done
                  subgoal
                    apply simp
                    apply (rule in_frontier_zcount_alt)
                    apply auto
                    apply (smt (verit, del_insts) count_image_mset_ge_count count_mset_gt_0 int_zle_neg not_less of_nat_less_0_iff prod.sel(2))
                    done
                  done
                done
              subgoal
                unfolding frontier_less_equal_iff2
                apply (subst (5) add.commute)
                apply (subst (2) add.assoc[symmetric])
                apply simp
                apply (subst (1) add.assoc[symmetric])
                apply (auto simp add: ac_simps)
                subgoal premises prems4
                  using prems4(14) apply -
                  apply (subgoal_tac "\<exists>t'\<le>t. t' \<in>\<^sub>A frontier (zmset_of (mset_set (set_antichain (frontier (zmset_of {#n 1. x \<in># mset batch#} + zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#}))))))")
                  subgoal
                    apply (subst (2) add.commute)
                    apply (meson fronteier_lt_add_ex zmset_of_mset_set_ge_zero)
                    done
                  subgoal
                    apply simp
                    apply (rule in_frontier_zcount_alt)
                    apply auto
                    apply (smt (verit, del_insts) count_image_mset_ge_count count_mset_gt_0 int_zle_neg not_less of_nat_less_0_iff prod.sel(2))
                    done
                  done
                done
              done
            subgoal for x
              unfolding frontier_less_equal_iff2
              apply (subst (5) add.commute)
              apply (subst (2) add.assoc[symmetric])
              apply simp
              apply (subst (1) add.assoc[symmetric])
              apply (auto simp add: ac_simps)
              subgoal premises prems4
                apply (subgoal_tac "\<exists>t'\<le>n 1. t' \<in>\<^sub>A frontier (zmset_of (mset_set (set_antichain (frontier (zmset_of {#n 1. x \<in># mset batch#} + zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#}))))))")
                subgoal
                  apply (subst (2) add.commute)
                  apply (meson fronteier_lt_add_ex zmset_of_mset_set_ge_zero)
                  done
                subgoal
                  apply simp
                  apply (rule in_frontier_zcount_alt)
                  apply auto
                  using prems4(14)
                  apply (metis (lifting) count_image_mset_ge_count count_mset_gt_0 int_plus neq0_conv not_add_less1 of_nat_0_less_iff prems4(15) verit_comp_simplify(3))
                  done
                done
              done
            subgoal for a t x             
              apply (cases x; simp; hypsubst_thin)
              apply force
              subgoal for t'
                unfolding frontier_less_equal_iff2
                apply (subst (5) add.commute)
                apply (subst (2) add.assoc[symmetric])
                apply simp
                apply (subst (1) add.assoc[symmetric])
                apply (auto 0 0 simp add: ac_simps)
                apply (subst (2) add.commute)
                apply (subgoal_tac "\<exists>t'\<le>t. t' \<in>\<^sub>A frontier
                (zmset_of (mset_set (set_antichain (frontier (zmset_of {#n 1. x \<in># mset batch#} + zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#}))))))")
                subgoal
                  apply simp
                  apply (smt (z3) fronteier_lt_add_ex frontier_idempotent zcount_zmset_of_nonneg)
                  done
                subgoal
                  apply simp
                  apply (rule in_frontier_zcount_alt)
                  apply (subgoal_tac "0 < int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t)")
                  subgoal
                    by (smt (verit, ccfv_threshold) zcount_of_mset zcount_union zcount_zmset_of_nonneg zmset_of_plus)
                  subgoal
                    apply clarsimp
                    apply (rule image_eqI[rotated])
                    apply assumption
                    apply auto
                    done
                  done
                done
              done
            done
          subgoal using prems(19) by simp
          subgoal using prems(20) by simp
          subgoal using prems(21) by simp
          subgoal using prems(1,2,3,9,10,11,12,13,14,15,22) apply -
            apply auto
            unfolding changes_non_zero_def extract_progress_def comp_def
            apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          subgoal premises prems2
            unfolding produce_def
            apply auto
            defer
            subgoal
              using prems(2,9,10,23,11) prems(13)[symmetric] prems2(2) apply -
              unfolding extract_progress_def comp_def input_cap_def
              apply auto
              apply hypsubst_thin
              apply (rule changes_above_impl_extend[where B="[(Loc 0 (Src 1), n 1, - 1), (Loc 0 (Src 1), Suc (n 1), 1),(Loc 1 (Trg 1), n 1, int (length batch))]"])
              apply assumption
              apply (simp_all add: c_pts_change_multiplicities)
              subgoal premises prems3
                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or>  zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
                defer
                subgoal
                  using prems3(4) by (smt (verit) zcount_single zcount_union)
                subgoal
                  apply (elim disjE)
                  subgoal
                    unfolding changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ
                    apply auto
                    subgoal 
                      by (metis frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                    subgoal 
                      by (metis (no_types, opaque_lifting)
                          \<open>0 < zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) \<Longrightarrow> frontier_less_equal (frontier (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))))) (n 1)\<close>
                          frontier_le_singletons frontier_less_equal_iff frontier_less_equal_le_trans semiring_norm(174) trivial_dataflow_topology_interpretation.le_plus(1))
                    subgoal 
                      by (metis (no_types, opaque_lifting) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_le_trans frontier_less_equal_zcount_pos zcount_zmset_of_nonneg zmset_of_plus)       
                    done
                  subgoal
                    using prems3(3) apply -
                    unfolding changes_above_impl_def
                    apply (clarsimp split: prod.splits)
                    apply (intro conjI ballI)
                    subgoal
                      apply (subgoal_tac "\<exists> m. (1, n 1, m) \<in> set (operator_state.inter os1) \<and> m > 0")
                      subgoal
                        apply (elim exE conjE)
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply fast
                          apply simp
                          done
                        done
                      subgoal
                        by (meson zcount_gt_0_in_set_2)
                      done
                    subgoal
                      apply (subgoal_tac "\<exists> m. (1, n 1, m) \<in> set (operator_state.inter os1) \<and> m > 0")
                      subgoal
                        apply (elim exE conjE)
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply fast
                          apply simp
                          using frontier_less_equal_trans apply force
                          done
                        done
                      subgoal
                        by (meson zcount_gt_0_in_set_2)
                      done
                    subgoal
                      apply (subgoal_tac "\<exists> m. (1, n 1, m) \<in> set (operator_state.inter os1) \<and> m > 0")
                      subgoal
                        apply (elim exE conjE)
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply fast
                          apply simp
                          unfolding frontier_less_equal_iff dataflow_topology_implied_frontier_alt_my_summ
                          apply simp
                          apply (rule order.trans[rotated])
                          apply assumption
                          apply (metis (no_types, opaque_lifting) Groups.add_ac(1) frontier_below_eq_frontier_plus_pos zcount_zmset_of_nonneg)
                          done
                        done
                      subgoal
                        by (meson zcount_gt_0_in_set_2)
                      done
                    done
                  done
                done
              done
            subgoal
              using prems(2,9,10,23,11) prems(13)[symmetric] prems2(2) apply -
              unfolding extract_progress_def comp_def input_cap_def
              apply auto
              apply hypsubst_thin
              apply (rule changes_above_impl_extend[where B="[(Loc 0 (Src 1), n 1, - 1), (Loc 0 (Src 1), Suc (n 1), 1)]"])
              apply assumption
              apply (simp_all add: c_pts_change_multiplicities)
              subgoal premises prems3
                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or>  zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
                defer
                subgoal
                  using prems3 by (smt (verit) zcount_single zcount_union)
                subgoal
                  apply (elim disjE)
                  subgoal
                    unfolding changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ
                    apply auto
                    subgoal
                      by (metis (no_types, opaque_lifting) Suc_n_not_le_n frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_le_trans frontier_less_equal_trans frontier_less_equal_zcount_pos linorder_linear zcount_zmset_of_nonneg)
                    subgoal 
                      using
                        \<open>0 < zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) \<Longrightarrow> frontier_less_equal (frontier (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))))) (n 1)\<close>
                        frontier_less_equal_trans le_SucI by blast
                    done
                  subgoal
                    using prems3 apply -
                    unfolding changes_above_impl_def
                    apply (clarsimp split: prod.splits)
                    apply (intro conjI ballI)
                    subgoal
                      apply (subgoal_tac "\<exists> m. (1, n 1, m) \<in> set (operator_state.inter os1) \<and> m > 0")
                      subgoal
                        apply (elim exE conjE)
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply fast
                          apply simp
                          done
                        done
                      subgoal
                        by (meson zcount_gt_0_in_set_2)
                      done
                    subgoal
                      apply (subgoal_tac "\<exists> m. (1, n 1, m) \<in> set (operator_state.inter os1) \<and> m > 0")
                      subgoal
                        apply (elim exE conjE)
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply fast
                          apply simp
                          unfolding frontier_less_equal_iff dataflow_topology_implied_frontier_alt_my_summ
                          apply simp
                          by (metis (no_types, lifting) basic_trans_rules(23) frontier_le_singletons le_add_same_cancel2 plus_1_eq_Suc zero_less_one_class.zero_le_one)
                        done
                      subgoal
                        by (meson zcount_gt_0_in_set_2)
                      done
                    done
                  done
                done
              done
            done
          subgoal premises prems2
            unfolding produce_def
            apply auto
            subgoal
              using prems(1,2,9,10,24,11) prems(13) prems2(2) apply -
              unfolding extract_progress_def
              apply (auto simp add: produce_def input_cap_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              apply (rule changes_above_impl_extend[where B="(Loc 0 (Src 1), n 1, - 1) # (Loc 0 (Src 1), Suc (n 1), 1) # []"])
              apply assumption
              apply auto
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
              subgoal
                apply (elim disjE)
                subgoal premises prems3
                  using prems3(6) apply -
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; (simp add: split_beta)?)
                  subgoal
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 0 (Src 1)"])
                    apply simp_all
                    apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    unfolding frontier_less_equal_iff2
                    using in_frontier_zcount apply blast
                    done
                  subgoal
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 0 (Src 1)"])
                    apply simp_all
                    apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    unfolding frontier_less_equal_iff2
                    apply (meson dataflow_topology_from_tree.obtain_frontier_elem le_SucI)
                    done
                  done
                subgoal premises prems3
                  using prems3(3,6) apply -
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; (simp add: split_beta)?)
                  subgoal
                    apply (drule zcount_gt_0_in_set_2)
                    apply (elim exE)
                    subgoal for m
                      apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                      apply simp
                      apply (rule disjI2)
                      apply (rule image_eqI[rotated])
                      apply auto
                      done
                    done
                  subgoal
                    apply (drule zcount_gt_0_in_set_2)
                    apply (elim exE)
                    subgoal for m
                      apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                      apply simp
                      apply (rule disjI2)
                      apply (rule image_eqI[rotated])
                      apply auto
                      unfolding frontier_less_equal_def
                      apply auto
                      done
                    done
                  done
                done
              subgoal
                by (smt (verit, del_insts) zcount_add_zmset zcount_empty zcount_union)
              done
            subgoal
              using prems(1,2,9,10,24,11) prems(13) prems2(2) apply -
              unfolding extract_progress_def
              apply (auto simp add: produce_def input_cap_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              apply (rule changes_above_impl_extend[where B="(Loc 0 (Src 1), n 1, - 1) # (Loc 0 (Src 1), Suc (n 1), 1) # [(Loc 1 (Trg 1), n 1, int (length batch))]"])
              apply assumption
              apply auto
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
              subgoal
                apply (elim disjE)
                subgoal premises prems3
                  using prems3(7) apply -
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; (simp add: split_beta)?)
                  subgoal
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 0 (Src 1)"])
                    apply simp_all
                    apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    unfolding frontier_less_equal_iff2
                    using in_frontier_zcount apply blast
                    done
                  subgoal
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 0 (Src 1)"])
                    apply simp_all
                    apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    unfolding frontier_less_equal_iff2
                    apply (meson dataflow_topology_from_tree.obtain_frontier_elem le_SucI)
                    done
                  subgoal
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 0 (Src 1)"])
                    apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    unfolding frontier_less_equal_iff2
                    using in_frontier_zcount apply blast
                    using l0_lt_l1 le_less apply blast
                    done
                  done
                subgoal premises prems3
                  using prems3(4,7) apply -
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; (simp add: split_beta)?)
                  subgoal
                    apply (drule zcount_gt_0_in_set_2)
                    apply (elim exE)
                    subgoal for m
                      apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                      apply simp
                      apply (rule disjI2)
                      apply (rule image_eqI[rotated])
                      apply auto
                      done
                    done
                  subgoal
                    apply (drule zcount_gt_0_in_set_2)
                    apply (elim exE)
                    subgoal for m
                      apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                      apply simp
                      apply (rule disjI2)
                      apply (rule image_eqI[rotated])
                      apply auto
                      unfolding frontier_less_equal_def
                      apply auto
                      done
                    done
                  subgoal
                    apply (drule zcount_gt_0_in_set_2)
                    apply (elim exE)
                    subgoal for m
                      apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                      apply simp
                      apply force
                      apply auto
                      unfolding frontier_less_equal_iff
                      apply (rule order.trans[rotated])
                      apply assumption
                      apply (auto simp add: dataflow_topology_implied_frontier_alt_my_summ produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                      apply (metis (mono_tags, lifting) add.assoc frontier_below_eq_frontier_plus_pos zmset_of_mset_set_ge_zero)
                      done
                    done
                  done
                done
              subgoal
                by (smt (verit, del_insts) zcount_add_zmset zcount_empty zcount_union)
              done
            done
          subgoal premises prems2
            using prems2(2) apply -
            unfolding produce_def
            apply auto
            subgoal
              using prems(1,2,3,9,10,25,11,14) prems(13) apply -
              apply simp
              unfolding extract_progress_def input_cap_def
              apply auto
              apply hypsubst_thin
              apply (auto 0 0 simp add: add.assoc dataflow_topology_implied_frontier_alt_my_summ update_zmultiset_replicate c_pts_change_multiplicities)
              apply (subgoal_tac 
                  "change_multiplicities my_summ
       (map (\<lambda>(p, y). (Loc 0 (Src 1), y)) (operator_state.inter os1) @ (Loc 0 (Src 1), n 1, - 1) # (Loc 0 (Src 1), Suc (n 1), 1) # concat (map (\<lambda>(p, t, m). [(Loc 1 (Trg 1), t, m)]) (produ os1)))
       (pt_tr sg) = 
   change_multiplicities my_summ [(Loc 0 (Src 1), n 1, - 1), (Loc 0 (Src 1), Suc (n 1), 1)] (change_multiplicities my_summ (map (\<lambda>(p, y). (Loc 0 (Src 1), y)) (operator_state.inter os1) @ concat (map (\<lambda>(p, t, m). [(Loc 1 (Trg 1), t, m)]) (produ os1))) (pt_tr sg))")
              defer
              subgoal premises
                apply (simp flip: change_multiplicities_append_alt)
                apply (rule fun_cong[where x="(pt_tr sg)"])
                apply (rule change_multiplicities_appen_cong)
                apply (rule ext)
                using change_multiplicities_comm 
                apply (metis (no_types, lifting) append_Cons empty_append_eq_id)
                done
              subgoal premises prems3
                apply (simp add: prems3(8))
                using prems3(5) apply -
                subgoal
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; simp)
                  apply (elim disjE exE)
                  subgoal for x l t a
                    apply auto
                    apply hypsubst_thin
                    apply (drule bspec)
                    apply blast
                    apply simp
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Trg 1)"])
                    apply (simp_all add: c_pts_change_multiplicities)
                    subgoal premises prems4 for m
                      using prems4(1) apply -
                      using prems(1,2,12,11,9,10,22) apply -
                      unfolding extract_progress_def input_cap_def changes_non_zero_def
                      apply (auto simp add: c_pts_change_multiplicities)
                      apply hypsubst_thin
                      apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
                      subgoal
                        unfolding frontier_less_equal_iff2
                        by (meson trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                      subgoal
                        apply (rule zcount_gt_0_zmulset_diff[where B="zmset (map snd (consu os2))" and C="zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1))"])
                        apply (simp add: add_diff_eq)
                        apply simp_all
                        subgoal premises prems5
                          using prems5(1,5) apply -
                          apply (rule zcount_zmset_gt_0[where m=m])
                          apply force
                          apply simp_all
                          using prems(8) apply force
                          using prems(8) apply auto
                          done
                        done
                      done
                    done
                  subgoal for x l t m
                    apply auto
                    apply hypsubst_thin
                    apply (drule bspec)
                    apply blast
                    apply simp      
                    subgoal
                      apply (cases "zcount (zmset (map snd (operator_state.inter os2))) t < 0")
                      subgoal
                        apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Src 1)"])
                        using prems(2,15,11,9,10) apply -
                        unfolding extract_progress_def input_cap_def
                        apply (auto 0 0 simp add: add.assoc dataflow_topology_implied_frontier_alt_my_summ update_zmultiset_replicate c_pts_change_multiplicities)
                        apply hypsubst_thin
                        apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Src 1))) t > 0")
                        subgoal
                          unfolding frontier_less_equal_iff2
                          by (meson trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                        subgoal
                          unfolding zmultiset_eq_iff
                          apply (drule spec[of _ t])
                          apply simp
                          done
                        done
                      subgoal
                        unfolding not_less
                        using prems(26,27) apply -
                        apply (drule spec[of _ t])+
                        apply (drule spec)
                        apply (drule mp)
                        apply simp
                        apply (drule mp)
                        apply simp
                        apply auto
                        subgoal for m'
                          apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Trg 1)"])
                          apply (simp_all add: c_pts_change_multiplicities)
                          subgoal premises prems4
                            using prems4(5) apply -
                            using prems(1,2,12,11,9,10,22) apply -
                            unfolding extract_progress_def input_cap_def changes_non_zero_def
                            apply (auto simp add: c_pts_change_multiplicities)
                            apply hypsubst_thin
                            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
                            subgoal
                              unfolding frontier_less_equal_iff2
                              by (meson trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                            subgoal
                              apply (rule zcount_gt_0_zmulset_diff[where B="zmset (map snd (consu os2))" and C="zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1))"])
                              apply (simp add: add_diff_eq)
                              apply simp_all
                              subgoal premises prems5
                                using prems5(1,5) apply -
                                apply (rule zcount_zmset_gt_0[where m=m'])
                                apply force
                                apply simp_all
                                using prems(8) apply force
                                using prems(8) apply auto
                                done
                              done
                            done
                          subgoal
                            apply (rule order.strict_implies_order)
                            apply auto
                            using less_eq_port.simps(3,4) less_port_def apply blast
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done
            subgoal
              using prems(1,2,3,9,10,25,11,14) prems(13) apply -
              apply simp
              unfolding extract_progress_def input_cap_def
              apply auto
              apply hypsubst_thin
              apply (auto 0 0 simp add: add.assoc dataflow_topology_implied_frontier_alt_my_summ update_zmultiset_replicate c_pts_change_multiplicities)
              apply (subgoal_tac 
                  "change_multiplicities my_summ
       (map (\<lambda>(p, y). (Loc 0 (Src 1), y)) (operator_state.inter os1) @ (Loc 0 (Src 1), n 1, - 1) # (Loc 0 (Src 1), Suc (n 1), 1) # concat (map (\<lambda>(p, t, m). [(Loc 1 (Trg 1), t, m)]) (produ os1)))
       (pt_tr sg) = 
   change_multiplicities my_summ [(Loc 0 (Src 1), n 1, - 1), (Loc 0 (Src 1), Suc (n 1), 1)] (change_multiplicities my_summ (map (\<lambda>(p, y). (Loc 0 (Src 1), y)) (operator_state.inter os1) @ concat (map (\<lambda>(p, t, m). [(Loc 1 (Trg 1), t, m)]) (produ os1))) (pt_tr sg))")
              defer
              subgoal premises
                apply (simp flip: change_multiplicities_append_alt)
                apply (rule fun_cong[where x="(pt_tr sg)"])
                apply (rule change_multiplicities_appen_cong)
                apply (rule ext)
                using change_multiplicities_comm 
                apply (metis (no_types, lifting) append_Cons empty_append_eq_id)
                done
              subgoal premises prems3
                using prems3(5) prems3(9) apply -
                subgoal
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; simp)
                  apply (elim disjE exE)
                  subgoal for x l t a
                    apply auto
                    apply hypsubst_thin
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Trg 1)"])
                    apply (simp_all add: c_pts_change_multiplicities)
                    subgoal premises prems4 for m
                      using prems4(3) apply -
                      using prems(1,2,12,11,9,10,22) apply -
                      unfolding extract_progress_def input_cap_def changes_non_zero_def
                      apply (auto simp add: c_pts_change_multiplicities)
                      apply hypsubst_thin
                      apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
                      subgoal
                        unfolding frontier_less_equal_iff2
                        apply (subgoal_tac "\<forall> t. zcount (zmset_of {#n 1. x \<in># mset batch#}) t \<ge> 0")
                        subgoal
                          apply (erule trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                          apply auto
                          apply (smt (verit, best) Groups.add_ac(1) in_frontier_in_frontier_add_alt zcount_zmset_of_nonneg)
                          done
                        subgoal
                          by auto
                        done
                      subgoal
                        apply (rule zcount_gt_0_zmulset_diff[where B="zmset (map snd (consu os2))" and C="zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1))"])
                        apply (simp add: add_diff_eq)
                        apply simp_all
                        subgoal premises prems5
                          using prems5(1,5) apply -
                          apply (rule zcount_zmset_gt_0[where m=m])
                          apply force
                          apply simp_all
                          using prems(8) apply force
                          using prems(8) apply auto
                          done
                        done
                      done
                    done
                  subgoal for x l t m
                    apply auto
                    apply hypsubst_thin    
                    subgoal
                      apply (cases "zcount (zmset (map snd (operator_state.inter os2))) t < 0")
                      subgoal
                        apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Src 1)"])
                        using prems(2,15,11,9,10) apply -
                        unfolding extract_progress_def input_cap_def
                        apply (auto 0 0 simp add: add.assoc dataflow_topology_implied_frontier_alt_my_summ update_zmultiset_replicate c_pts_change_multiplicities)
                        apply hypsubst_thin
                        apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Src 1))) t > 0")
                        subgoal
                          unfolding frontier_less_equal_iff2
                          by (meson trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                        subgoal
                          unfolding zmultiset_eq_iff
                          apply (drule spec[of _ t])
                          apply simp
                          done
                        done
                      subgoal
                        unfolding not_less
                        using prems(26,27) apply -
                        apply (drule spec[of _ t])+
                        apply (drule spec)
                        apply (drule mp)
                        apply simp
                        apply (drule mp)
                        apply simp
                        apply auto
                        subgoal for m'
                          apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Trg 1)"])
                          apply (simp_all add: c_pts_change_multiplicities)
                          subgoal premises prems4
                            using prems4(6) apply -
                            using prems(1,2,12,11,9,10,22) apply -
                            unfolding extract_progress_def input_cap_def changes_non_zero_def
                            apply (auto simp add: c_pts_change_multiplicities)
                            apply hypsubst_thin
                            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
                            subgoal
                              unfolding frontier_less_equal_iff2
                              apply (subgoal_tac "\<forall> t. zcount (zmset_of {#n 1. x \<in># mset batch#}) t \<ge> 0")
                              subgoal
                                apply (erule trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                                apply auto
                                apply (smt (verit, best) Groups.add_ac(1) in_frontier_in_frontier_add_alt zcount_zmset_of_nonneg)
                                done
                              subgoal
                                by auto
                              done
                            subgoal
                              apply (rule zcount_gt_0_zmulset_diff[where B="zmset (map snd (consu os2))" and C="zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1))"])
                              apply (simp add: add_diff_eq)
                              apply simp_all
                              subgoal
                                apply (rule zcount_zmset_gt_0[where m=m'])
                                apply force
                                apply simp_all
                                using prems(8) apply force
                                using prems(8) apply auto
                                done
                              done
                            done
                          subgoal
                            apply (rule order.strict_implies_order)
                            apply auto
                            using less_eq_port.simps(3,4) less_port_def apply blast
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
            using prems(26) by simp
          subgoal
            using prems(27) by simp
          subgoal
            using prems(28) by auto
          subgoal
            using prems(29) apply -
            unfolding produce_def 
            apply force
            done
          subgoal
            using prems(30) by simp
          subgoal premises prems2
            using prems(1,2,13,31,9,10,11) prems2(2) apply -
            unfolding produce_def input_cap_def extract_progress_def
            apply (clarsimp simp add: c_pts_change_multiplicities split: if_splits)
            apply hypsubst_thin
            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
            subgoal
              apply auto
              apply (meson le_eq_less_or_eq lessI)
              apply (meson le_eq_less_or_eq lessI)
              apply (meson zcount_gt_0_in_set_2)
              apply (meson le_SucI zcount_gt_0_in_set_2)+
              done
            subgoal
              by (simp add: sum_gt_zeroD zmultiset_eq_iff)
            done
          subgoal
            using prems(4,32) apply -
            unfolding produce_def 
            apply clarsimp
            apply (metis SIM1(4)
                \<open>1 \<notin> defaults \<Longrightarrow> inps 1 = LCons batch lxs \<Longrightarrow> lxs \<noteq> LNil \<Longrightarrow> xs 0 = outpu os2 0 \<Longrightarrow> ys 0 = max_from_buf caps buf2 ((map projr \<circ> buf1 \<circ> Inr \<circ>\<circ> Pair) 1 0 @ outpu os1 0) \<Longrightarrow> \<forall>cap. cap \<in> set caps \<longrightarrow> time cap < map_entry 1 Suc n 1\<close>
                array_rules(3) nat_in_between_eq(2) nat_le_linear prems(5))
            done
          subgoal
            using prems(4,33,29) apply -
            unfolding produce_def
            apply (auto simp add: sorted_append comp_def)
            using sorted_map apply fastforce
            using sorted_map apply fastforce
            apply (metis imageI nat_less_le old.prod.exhaust snd_conv)
            done
          subgoal
            apply (rule rtranclp_intros_1)
            apply (rule arg_cong3[where f=map_op])
            apply simp
            apply simp_all
            apply (subst iterates.code)
            apply (auto split: list.splits)
            subgoal
              apply (rule arg_cong[where f=source_op])
              apply (rule ext)
              apply (rule arg_cong2[where f=lshift])
              apply simp
              apply (rule arg_cong2[where f=lshift])
              apply simp_all
              apply (rule arg_cong2[where f=max_from_caps_buf])
              apply (auto simp add: produce_def comp_def)
              done
            subgoal for x xs
              apply (rule arg_cong[where f=source_op])
              apply (rule ext)
              apply (rule arg_cong2[where f=lshift])
              apply simp
              apply (simp add: comp_def flip: snoc_shift)
              apply (rule arg_cong2[where f=lshift])
              apply simp_all
              unfolding outpu_produce
              subgoal premises prems3
                unfolding max_from_caps_buf_append
                apply (simp only: list.simps list_to_buf_def)
                unfolding max_from_caps_buf_def map_append append_assoc
                apply (intro arg_cong2[where f=append])
                subgoal
                  using prems(28) apply -
                  unfolding list_to_buf_def BULK_BENQ_def
                  apply auto
                  done
                subgoal
                  apply (auto 0 0)
                  apply (rule Max_eq_if)
                  using prems(6,28,29) apply -
                  unfolding list_to_buf_def BULK_BENQ_def
                  apply (auto simp add: split_beta split: sum.splits)
                  subgoal for x'
                    apply (cases x'; simp)
                    apply fastforce
                    subgoal for a
                      apply (cases a)
                      apply (auto simp add: split_beta split: sum.splits; hypsubst_thin)
                      subgoal for a
                        apply (rule bexI[of _ a])
                        using image_iff apply fastforce+
                        done
                      done
                    done
                  subgoal for x' a
                    apply (cases x'; simp)
                    apply fastforce
                    using prems(6,28,29,30) apply -
                    unfolding list_to_buf_def BULK_BENQ_def
                    apply (auto simp add: split_beta split: sum.splits)       
                    using image_iff apply fastforce
                    done
                  done
                subgoal
                  using prems(6,28,29,30) apply -
                  unfolding rmdups_append BULK_BENQ_def
                  apply (rule sym)
                  apply (auto simp add: comp_def split_beta split: sum.splits; hypsubst_thin?)
                  apply (metis (no_types, opaque_lifting) imageI less_irrefl_nat prod.exhaust snd_conv)
                  apply (metis (no_types, opaque_lifting) less_irrefl_nat)
                  apply (metis (no_types, opaque_lifting) less_irrefl_nat)
                  apply (metis (no_types, opaque_lifting) less_irrefl_nat)
                  subgoal
                    apply (rule Max_eq_if)
                    apply simp_all
                    subgoal
                      apply (auto simp add: comp_def split_beta split: sum.splits; hypsubst_thin?)
                      apply (metis (lifting) image_iff)
                      apply blast
                      done
                    subgoal
                      apply (auto simp add: comp_def split_beta split: sum.splits; hypsubst_thin?)
                      apply blast
                      done
                    done
                  subgoal
                    apply (rule rmdups_NilI)
                    apply auto
                    done
                  done
                done
              done
            done
          done
        subgoal for x xs
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
          subgoal using prems(3) by (simp add: produce_def)
          apply (rule refl)+
          subgoal using prems(6) by simp
          subgoal using prems(7) apply -
            using sorted_filter by blast
          subgoal using prems(8) by simp
          subgoal using prems(9,2,3,9,10,11,12)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13) by
              (auto simp add: ac_simps update_zmultiset_replicate input_cap_def zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14,15) 
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(1,2,3,9,10,11,12,18)
            by (clarsimp simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
          subgoal
            using prems(19) by simp
          subgoal
            using prems(20) by simp
          subgoal
            using prems(21) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,22) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,23) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,24) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,25) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,26) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,27) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,28) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,29) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,30) by simp
          subgoal
            using prems(31) by simp
          subgoal
            using prems(32) by simp
          subgoal
            using prems(33) by simp
          subgoal 
            apply simp
            apply (rule step_wstep)
            apply (rule step_map_op)
            apply (rule step_source_op_Out_intro[where p=0])
            apply (rule refl)
            apply (auto simp add: comp_def defaults_num1_def)
            done
          done
        subgoal for x xs'
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
          subgoal using prems(3) by (simp add: produce_def)
          apply (rule refl)+
          subgoal using prems(6) by simp
          subgoal using prems(7) apply -
            using sorted_filter by blast
          subgoal using prems(8) by simp
          subgoal using prems(9,2,3,9,10,11,12)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13) by
              (auto simp add: ac_simps update_zmultiset_replicate input_cap_def zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14,15) 
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(1,2,3,9,10,11,12,18)
            by (clarsimp simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
          subgoal
            using prems(19) by simp
          subgoal
            using prems(20) by simp
          subgoal
            using prems(21) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,22) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,23) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,24) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,25) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,26) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,27) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,28) by simp
          subgoal
            using prems(1,2,3,9,10,11,12,29) by auto
          subgoal
            using prems(1,2,3,9,10,11,12,30) by simp
          subgoal
            using prems(31) by simp
          subgoal
            using prems(32) by auto
          subgoal
            using prems(33) by auto
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
            apply simp_all
            subgoal
              apply (auto split: prod.splits)
              subgoal
                apply (rule arg_cong2[where f=max_from_caps_buf])
                apply (auto simp add: insert_absorb comp_def BULK_BENQ_def list_to_buf_def)
                done
              subgoal for x1 a x1a x2a
                using prems(6) apply -
                apply (cases a; simp; hypsubst_thin?)
                apply fastforce
                apply (rule arg_cong2[where f=max_from_caps_buf])
                apply (auto simp add: split_beta insert_absorb comp_def BULK_BENQ_def list_to_buf_def split: sum.splits)
                apply (smt (verit, best) Un_insert_right image_iff insert_absorb split_pairs2 sum.sel(2))
                done
              subgoal for b a
                apply (rule arg_cong2[where f=max_from_caps_buf])
                apply (auto simp add: split_beta insert_absorb comp_def BULK_BENQ_def list_to_buf_def split: sum.splits)
                done
              done
            done
          done
        subgoal
          using prems(6) unfolding BHD_def by auto
        subgoal for n t
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
          subgoal using prems(3) by (simp add: produce_def)
          apply (rule refl)+
          subgoal premises
            using prems(6) apply -
            unfolding BTL_def apply clarsimp
            apply (meson in_set_tlD)
            done
          subgoal using prems(7) 
            using sorted_sort_key by blast
          subgoal using prems(8) by simp
          subgoal 
            using prems(9,2,3,9,10,11,12) apply -
            unfolding BTL_def BHD_def
            apply (cases "buf1 (Inr (1, 1))"; simp)
            subgoal for a as
              apply (cases a; simp)
              apply (simp add: group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: sum.splits option.splits; hypsubst_thin?)
              apply (auto simp add: zmultiset_eq_iff zcount_update_zmultiset)
              done
            done
          subgoal using prems(10,9,2,3,9,10,11,12,13) by
              (auto simp add: ac_simps update_zmultiset_replicate input_cap_def zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14,15) 
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal premises prems2
            using prems2(1,2,3,4) prems(1,2,3,9,10,11,6,18,15) prems(12) apply -
            unfolding BTL_def BHD_def
            apply (cases "buf1 (Inr (1, 1))"; simp)
            subgoal for a as
              apply (cases a; simp)
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              subgoal for a t' x
                apply (cases x; simp; hypsubst_thin?)
                apply fastforce
                subgoal for b'
                  apply (simp add: update_zmultiset_singleton frontier_less_equal_iff)
                  apply (subgoal_tac "frontier (zmset_of ({#snd (projr x). x \<in># mset as#} + snd `# mset (outpu os1 1))) \<le> frontier {#t'#}\<^sub>z")
                  subgoal
                    apply (rule order.trans[rotated])
                    apply assumption
                    apply (simp add: Groups.add_ac(2) frontier_le_remove_left)
                    done
                  subgoal premises prems3
                    unfolding frontier_less_equal_iff[symmetric]
                    unfolding frontier_less_equal_iff2
                    apply (rule in_frontier_zcount)
                    using prems3(10) apply -
                    apply (simp flip: mset_map)
                    using count_mset_gt_0 
                    apply (smt (verit, best) map_in_setD of_nat_0_less_iff of_nat_less_0_iff snd_conv sum.sel(2))
                    done
                  done
                done
              subgoal for a t'
                apply (simp add: update_zmultiset_singleton frontier_less_equal_iff)
                apply (subgoal_tac "frontier (zmset_of ({#snd (projr x). x \<in># mset as#} + snd `# mset (outpu os1 1))) \<le> frontier {#t'#}\<^sub>z")
                subgoal
                  apply (rule order.trans[rotated])
                  apply assumption
                  apply (simp add: Groups.add_ac(2) frontier_le_remove_left)
                  done
                subgoal premises prems3
                  unfolding frontier_less_equal_iff[symmetric]
                  unfolding frontier_less_equal_iff2
                  apply (rule in_frontier_zcount)
                  using prems3(10) apply -
                  apply (simp flip: mset_map)
                  using count_mset_gt_0 
                  apply (smt (verit, best) map_in_setD of_nat_0_less_iff of_nat_less_0_iff snd_conv sum.sel(2))
                  done
                done
              done
            done
          subgoal
            using prems(19) by simp
          subgoal
            using prems(20) by simp
          subgoal
            using prems(21) by simp
          subgoal premises prems2
            using prems(1,2,3,9,10,22) apply -
            unfolding changes_non_zero_def extract_progress_def
            apply (auto simp add: split_beta)
            apply force+
            done
          subgoal premises prems2
            using prems(1,2,3,9,10,14,12,11,23) prems2(1,2,3) apply -
            unfolding changes_above_impl_def extract_progress_def
            apply (auto simp add: split_beta; hypsubst_thin?)  
            subgoal
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
              defer
              subgoal premises prems3
                using prems3(5,7,8,9) prems(8) apply -
                unfolding zmultiset_eq_iff
                apply (drule spec[of _ t])
                apply simp
                apply (subgoal_tac "count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t > 0")
                subgoal
                  by (metis add_pos_nonneg diff_add_cancel of_nat_0_le_iff of_nat_0_less_iff sum_gt_zeroD zcount_zmset_ge_zero)
                subgoal
                  unfolding BHD_def
                  apply (cases "buf1 (Inr (1, 1))")
                  apply (auto simp add: split_beta split: prod.splits)
                  apply (metis prod.sel(2))
                  done
                done
              apply (elim disjE)
              subgoal premises prems3
                using prems3(10) apply -
                unfolding frontier_less_equal_iff2
                apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))) \<and> t' \<le> t")
                subgoal
                  by (metis (no_types, opaque_lifting) Groups.add_ac(2) fronteier_lt_add_ex frontier_idempotent zmset_of_mset_set_ge_zero)
                subgoal
                  using in_frontier_zcount by blast
                done
              subgoal
                apply (drule zcount_gt_0_in_set_2)
                apply (elim exE conjE)
                subgoal for m
                  apply (drule bspec)
                  apply simp
                  apply (rule disjI2)
                  apply (rule disjI1)
                  apply (rule bexI[of _ "(_, _, m)"])
                  apply simp
                  apply assumption
                  apply simp
                  done
                done
              done
            subgoal for t' m
              by force
            subgoal
              by force
            done
          subgoal premises prems2
            using prems(1,2,3,9,10,11,12,14,24) using prems2(1,2,3) apply -
            unfolding changes_above_impl_def extract_progress_def
            apply (auto simp add: split_beta; hypsubst_thin?)  
            subgoal for m t'
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              apply force
              done
            subgoal for m t'
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              apply (drule bspec[of _ _ "(_, t', m)"])
              apply simp 
              apply (rule disjI2)
              apply force
              apply simp
              apply (drule frontier_less_equal_add_cases)
              apply (elim disjE)
              subgoal
                apply (rule frontier_less_equal_addI)
                apply simp_all
                done
              subgoal
                apply (rule frontier_less_equal_addI)
                apply (simp_all add: update_zmultiset_singleton)
                apply (rule disjI1)
                unfolding BHD_def
                apply (cases "buf1 (Inr (1, 1))"; simp)
                subgoal for a as
                  apply (cases a; simp)
                  apply hypsubst_thin
                  using prems(31) apply -
                  apply (drule spec2)
                  apply (drule mp)
                  apply blast
                  apply simp
                  unfolding frontier_less_equal_iff2
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_trans trivial_dataflow_topology_interpretation.obtain_frontier_elem)
                  done
                done
              done
            done
          subgoal premises prems2
            using prems(1,2,3,8,9,10,11,12,14,25) using prems2(1,2,3) apply -
            unfolding changes_above_impl_def extract_progress_def
            apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            subgoal
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
              subgoal
                apply (subgoal_tac 
                    "frontier_less_equal (frontier (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)))))))) t")
                subgoal
                  by (meson frontier_less_equal_addI zcount_zmset_of_nonneg)
                subgoal
                  by (simp add: frontier_less_equal_zcount_pos)
                done
              subgoal
                unfolding BHD_def
                apply (cases "buf1 (Inr (1, 1))"; simp)
                subgoal for a as
                  apply (cases a; simp)
                  apply (simp add: zmultiset_eq_iff)
                  apply (drule spec[of _ t])                
                  apply auto
                  apply (smt (z3) not_int_zless_negative zcount_zmset_ge_zero)
                  done
                done
              done
            subgoal
              apply (drule bspec)
              apply auto
              done
            subgoal
              apply (drule bspec)
              apply auto
              done
            done
          subgoal
            using prems(1,2,3,9,10,11,12,26) by auto
          subgoal
            using prems(1,2,3,9,10,11,12,27) by auto
          subgoal
            using prems(1,2,3,9,10,11,12,28) by simp
          subgoal
            using prems(29) apply -
            unfolding BTL_def
            apply (auto simp add: split_beta)
            subgoal for a b x
              apply (drule spec[of _ a])
              apply (drule spec[of _ b])
              apply (elim conjE)
              apply (drule mp)
              apply (rule image_eqI[rotated])
              apply (drule in_set_tlD)
              apply assumption
              apply auto
              done
            done
          subgoal
            using prems(28,30) apply -
            unfolding BENQ_def BHD_def
            apply auto
            done
          subgoal
            using prems(31) by auto
          subgoal
            using prems(32) apply -
            unfolding BENQ_def BHD_def BTL_def
            apply clarsimp
            apply (metis imageI in_set_tlD)
            done
          subgoal
            using prems(33) apply -
            unfolding BENQ_def BHD_def BTL_def
            apply clarsimp
            apply (metis (no_types, lifting) list.sel(2) map_tl sorted_tl tl_append_if)
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
            apply simp_all
            subgoal
              unfolding max_from_caps_buf_def BENQ_def BTL_def comp_def list_to_buf_def BULK_BENQ_def BHD_def
              apply (auto simp add: split_beta)
              subgoal
                apply (cases "buf1 (Inr (1, 1))"; simp)
                subgoal for a as
                  apply (cases a)
                  apply simp_all
                  apply (rule Max_eq_if)
                  apply simp_all
                  subgoal
                    by (auto simp add:  split_beta split: sum.splits; hypsubst_thin?)
                  subgoal
                    apply auto
                    apply (metis (mono_tags, lifting) Un_iff img_fst mem_Collect_eq nle_le split_pairs2)
                    done
                  done
                done
              subgoal
                apply (cases "buf1 (Inr (1, 1))"; simp)
                subgoal for a as
                  apply (cases a)
                  apply simp_all
                  apply (rule Max_eq_if)
                  apply simp_all
                  subgoal
                    apply (auto simp add:  split_beta split: sum.splits; hypsubst_thin?)
                    apply (metis (full_types) capability.exhaust capability.sel(1) num1_eq1)
                    done
                  subgoal
                    by auto
                  done
                done
              subgoal
                apply (cases "buf1 (Inr (1, 1))"; simp)
                apply auto
                subgoal
                  by (metis (no_types, opaque_lifting))
                subgoal
                  apply (rule map_cong)
                  apply (auto simp add: insert_absorb)
                  apply (metis (no_types, opaque_lifting))
                  done
                subgoal 
                  by (metis snd_conv)
                done
              done
            done
          done
        prefer 3
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
          subgoal
            using prems(17) apply -
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            subgoal for l
              apply (drule spec[of _ l])
              apply (rule order.trans)
              apply assumption
              subgoal premises prems2
                using prems(1,2,9,10,11,12,13,14,23) prems(15)[symmetric] apply -
                unfolding dataflow_topology_implied_frontier_alt_my_summ
                apply simp
                apply (intro allI impI conjI)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  by (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  apply (auto 0 0 simp add: input_cap_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                  apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
                  subgoal
                    apply (elim disjE)
                    subgoal
                      unfolding frontier_less_equal_iff[symmetric]
                      unfolding frontier_less_equal_iff2
                      apply (metis (no_types, opaque_lifting) fronteier_lt_add_ex frontier_idempotent trivial_dataflow_topology_interpretation.obtain_frontier_elem zmset_of_mset_set_ge_zero)
                      done
                    subgoal
                      unfolding changes_above_impl_def
                      apply (drule zcount_gt_0_in_set_2)
                      apply safe
                      subgoal for m
                        apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                        apply auto
                        unfolding frontier_less_equal_iff[symmetric]
                        unfolding frontier_less_equal_iff2 dataflow_topology_implied_frontier_alt_my_summ
                        apply auto
                        done
                      done
                    done
                  subgoal
                    unfolding zmultiset_eq_iff
                    apply (drule spec[of _ "n 1"])+
                    apply auto
                    done
                  done
                subgoal
                  apply (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                  apply (intro frontier_le_add)
                  subgoal
                    apply (auto 0 0 simp add: input_cap_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
                    subgoal
                      apply (elim disjE)
                      subgoal
                        apply (rule frontier_le_remove_l)
                        apply simp_all
                        using frontier_less_equal_iff frontier_less_equal_zcount_pos apply blast
                        done
                      subgoal
                        unfolding changes_above_impl_def
                        apply (drule zcount_gt_0_in_set_2)
                        apply safe
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply auto
                          unfolding frontier_less_equal_iff[symmetric]
                          unfolding dataflow_topology_implied_frontier_alt_my_summ
                          apply clarsimp
                          apply (metis (no_types, opaque_lifting) frontier_less_equal_addI frontier_less_equal_add_cases zcount_zmset_of_nonneg zmset_of_plus)
                          done
                        done
                      done
                    subgoal
                      unfolding zmultiset_eq_iff
                      apply (drule spec[of _ "n 1"])+
                      apply auto
                      done
                    done
                  subgoal
                    apply clarsimp
                    apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_remove_left zcount_zmset_of_nonneg)
                    done
                  subgoal
                    apply clarsimp
                    apply (intro frontier_le_add)
                    subgoal
                      by (smt (verit, best) add_diff_cancel_left' dual_order.trans frontier_below_eq_frontier_minus frontier_idempotent zcount_zmset_of_nonneg)
                    subgoal
                      apply (elim changes_above_impl_elim conjE)
                      subgoal premises prems3
                        using prems3(9) apply -
                        unfolding changes_above_impl_def
                        apply simp
                        apply (rule le_frontier_frontier_less_equal)
                        unfolding dataflow_topology_implied_frontier_alt_my_summ
                        apply (auto simp add: Groups.add_ac(3) frontier_less_equal_addI)
                        done
                      done
                    done
                  done
                subgoal
                  apply (auto 0 0 simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                  apply (intro frontier_le_add)
                  subgoal
                    apply (auto 0 0 simp add: input_cap_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
                    subgoal
                      apply (elim disjE)
                      subgoal
                        apply (rule frontier_le_remove_l)
                        apply simp_all
                        using frontier_less_equal_iff frontier_less_equal_zcount_pos apply blast
                        done
                      subgoal
                        unfolding changes_above_impl_def
                        apply (drule zcount_gt_0_in_set_2)
                        apply safe
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply auto
                          unfolding frontier_less_equal_iff[symmetric]
                          unfolding dataflow_topology_implied_frontier_alt_my_summ
                          apply clarsimp
                          apply (metis (no_types, opaque_lifting) frontier_less_equal_addI frontier_less_equal_add_cases zcount_zmset_of_nonneg zmset_of_plus)
                          done
                        done
                      done
                    subgoal
                      unfolding zmultiset_eq_iff
                      apply (drule spec[of _ "n 1"])+
                      apply auto
                      done
                    done
                  subgoal
                    apply clarsimp
                    apply (intro frontier_le_add)
                    subgoal
                      by (smt (verit, best) add_diff_cancel_left' dual_order.trans frontier_below_eq_frontier_minus frontier_idempotent zcount_zmset_of_nonneg)
                    subgoal
                      apply (elim changes_above_impl_elim conjE)
                      subgoal premises prems3
                        using prems3(9) apply -
                        unfolding changes_above_impl_def
                        apply simp
                        apply (rule le_frontier_frontier_less_equal)
                        unfolding dataflow_topology_implied_frontier_alt_my_summ
                        apply (auto simp add: Groups.add_ac(3) frontier_less_equal_addI)
                        done
                      done
                    done
                  done
                done
              done
            done
          subgoal premises
            using prems(1,2,11,10,9,18) apply -
            apply clarsimp
            subgoal for a b
              apply (drule spec[of _ a])
              apply (drule spec[of _ b])
              apply (auto 0 0 simp flip: add.assoc simp add: dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              done
            done
          subgoal premises
            using prems(1,19) apply -
            apply simp
            using change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ] apply -
            apply (drule meta_spec)+
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (elim conjE)
            apply assumption
            prefer 3
            apply (rule refl)
            subgoal
              using prems(2,9,10,22,23) apply -
              apply (auto simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              subgoal
                apply (drule bspec)
                apply auto
                done
              done
            subgoal
              apply safe
              subgoal for l t x
                using prems(2,9,10,17,23) apply -
                apply (drule spec[of _ l])
                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                done
              done
            done
          subgoal premises
            using prems(1,20) apply -
            apply simp
            using change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ] apply -
            apply (drule meta_spec)+
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (elim conjE)
            apply assumption
            prefer 3
            apply (rule refl)
            subgoal
              using prems(2,9,10,22,23) apply -
              apply (auto  simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              subgoal
                apply (drule bspec)
                apply auto
                done
              done
            subgoal
              apply safe
              subgoal for l t x
                using prems(2,9,10,17,23) apply -
                apply (drule spec[of _ l])
                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                done
              done
            done
          subgoal premises
            using prems(1,21) apply -
            apply simp
            using change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ] apply -
            apply (drule meta_spec)+
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (drule meta_mp)
            defer
            apply (elim conjE)
            apply assumption
            prefer 3
            apply (rule refl)
            subgoal
              using prems(2,9,10,22,23) apply -
              apply (auto simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              subgoal
                apply (drule bspec)
                apply auto
                done
              done
            subgoal
              apply safe
              subgoal for l t x
                using prems(2,9,10,17,23) apply -
                apply (drule spec[of _ l])
                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                subgoal
                  apply (drule bspec)
                  apply blast
                  apply simp
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                  done
                done
              done
            done
          subgoal premises
            using prems(1,22) apply -
            unfolding changes_non_zero_def
            apply simp
            using prems(2,9,10,22,23) apply -
            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          subgoal premises
            using prems(1,2,9,10,24,25) by (auto simp add: extract_progress_def)
          subgoal premises
            using prems(1,2,9,10,24,25,26) by (auto simp add: extract_progress_def changes_above_impl_def)
          subgoal premises
            apply simp
            using prems(1,2,25,15,11,9,10) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
            done
          subgoal
            using prems(26) by simp
          subgoal
            apply simp
            using prems(1,2,27,15,11,9,10) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
            done
          subgoal
            using prems(28) by simp
          subgoal
            using prems(29) by simp
          subgoal
            using prems(30) by simp
          subgoal
            using prems(1,2,31) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
            done
          subgoal
            using prems(1,2,32) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
            done
          subgoal
            using prems(1,2,33) apply -
            apply (auto simp add: extract_progress_def c_pts_change_multiplicities)
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
                done
              done
            subgoal
              by (auto simp add: comp_def)
            done
          done

        subgoal for n' t
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
          subgoal using prems(3) by (simp add: produce_def)
          apply (rule refl)+
          subgoal premises
            using prems(6) apply -
            unfolding BTL_def apply clarsimp
            apply (meson in_set_tlD)
            done
          subgoal using prems(7) 
            by (meson sorted_insort_key)
          subgoal using prems(8) by simp
          subgoal 
            using prems(9,2,3,9,10,11,12) apply -
            unfolding BTL_def BHD_def
            apply (cases "buf1 (Inr (1, 1))"; simp)
            subgoal for a as
              apply (cases a; simp)
              apply (simp add: group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: sum.splits option.splits; hypsubst_thin?)
              apply (auto simp add: zmultiset_eq_iff zcount_update_zmultiset)
              done
            done
          subgoal using prems(10,9,2,3,9,10,11,12,13) by
              (auto simp add: ac_simps update_zmultiset_replicate input_cap_def zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal
            using prems(10,9,2,3,9,10,11,12,13,14,15) apply -
            apply (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply (metis add_zmset_add_single union_zmset_add_zmset_right update_zmultiset_singleton(2))
            done
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal premises prems2
            using prems2(1,2,3,4) prems(1,2,3,9,10,11,6,18,15) prems(12) apply -
            unfolding BTL_def BHD_def
            apply (cases "buf1 (Inr (1, 1))"; simp)
            subgoal for a as
              apply (cases a; simp)
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              subgoal for a t' x
                apply (cases x; simp; hypsubst_thin?)
                apply fastforce
                subgoal for b'
                  apply (simp add: update_zmultiset_singleton frontier_less_equal_iff)
                  apply (subgoal_tac "frontier (zmset_of ({#snd (projr x). x \<in># mset as#} + snd `# mset (outpu os1 1))) \<le> frontier {#t'#}\<^sub>z")
                  subgoal
                    apply (rule order.trans[rotated])
                    apply assumption
                    apply (simp add: Groups.add_ac(2) frontier_le_remove_left)
                    done
                  subgoal premises prems3
                    unfolding frontier_less_equal_iff[symmetric]
                    unfolding frontier_less_equal_iff2
                    apply (rule in_frontier_zcount)
                    using prems3(10) apply -
                    apply (simp flip: mset_map)
                    using count_mset_gt_0 
                    apply (smt (verit, best) map_in_setD of_nat_0_less_iff of_nat_less_0_iff snd_conv sum.sel(2))
                    done
                  done
                done
              subgoal for a t'
                apply (simp add: update_zmultiset_singleton frontier_less_equal_iff)
                apply (subgoal_tac "frontier (zmset_of ({#snd (projr x). x \<in># mset as#} + snd `# mset (outpu os1 1))) \<le> frontier {#t'#}\<^sub>z")
                subgoal
                  apply (rule order.trans[rotated])
                  apply assumption
                  apply (simp add: Groups.add_ac(2) frontier_le_remove_left)
                  done
                subgoal premises prems3
                  unfolding frontier_less_equal_iff[symmetric]
                  unfolding frontier_less_equal_iff2
                  apply (rule in_frontier_zcount)
                  using prems3(10) apply -
                  apply (simp flip: mset_map)
                  using count_mset_gt_0 
                  apply (smt (verit, best) map_in_setD of_nat_0_less_iff of_nat_less_0_iff snd_conv sum.sel(2))
                  done
                done
              done
            done
          subgoal
            using prems(19) by simp
          subgoal
            using prems(20) by simp
          subgoal
            using prems(21) by simp
          subgoal premises prems2
            using prems(1,2,3,9,10,22) apply -
            unfolding changes_non_zero_def extract_progress_def
            apply (auto simp add: split_beta)
            apply force+
            done
          subgoal premises prems2
            using prems(1,2,3,9,10,14,12,11,23) prems2(1,2,3) apply -
            unfolding changes_above_impl_def extract_progress_def
            apply (auto simp add: split_beta; hypsubst_thin?)  
            subgoal
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
              defer
              subgoal premises prems3
                using prems3(5,7,8,9) prems(8) apply -
                unfolding zmultiset_eq_iff
                apply (drule spec[of _ t])
                apply simp
                apply (subgoal_tac "count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t > 0")
                subgoal
                  by (metis add_pos_nonneg diff_add_cancel of_nat_0_le_iff of_nat_0_less_iff sum_gt_zeroD zcount_zmset_ge_zero)
                subgoal
                  unfolding BHD_def
                  apply (cases "buf1 (Inr (1, 1))")
                  apply (auto simp add: split_beta split: prod.splits)
                  apply (metis prod.sel(2))
                  done
                done
              apply (elim disjE)
              subgoal premises prems3
                using prems3(10) apply -
                unfolding frontier_less_equal_iff2
                apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))) \<and> t' \<le> t")
                subgoal
                  by (metis (no_types, opaque_lifting) Groups.add_ac(2) fronteier_lt_add_ex frontier_idempotent zmset_of_mset_set_ge_zero)
                subgoal
                  using in_frontier_zcount by blast
                done
              subgoal
                apply (drule zcount_gt_0_in_set_2)
                apply (elim exE conjE)
                subgoal for m
                  apply (drule bspec)
                  apply simp
                  apply (rule disjI2)
                  apply (rule disjI1)
                  apply (rule bexI[of _ "(_, _, m)"])
                  apply simp
                  apply assumption
                  apply simp
                  done
                done
              done
            subgoal
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
              defer
              subgoal premises prems3
                using prems3(5,7,8,9) prems(8) apply -
                unfolding zmultiset_eq_iff
                apply (drule spec[of _ t])
                apply simp
                apply (subgoal_tac "count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t > 0")
                subgoal
                  by (metis add_pos_nonneg diff_add_cancel of_nat_0_le_iff of_nat_0_less_iff sum_gt_zeroD zcount_zmset_ge_zero)
                subgoal
                  unfolding BHD_def
                  apply (cases "buf1 (Inr (1, 1))")
                  apply (auto simp add: split_beta split: prod.splits)
                  apply (metis prod.sel(2))
                  done
                done
              apply (elim disjE)
              subgoal premises prems3
                using prems3(10) apply -
                apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))) \<and> t' \<le> t")
                subgoal
                  by (metis frontier_idempotent frontier_less_equal_addI frontier_less_equal_iff2 zcount_zmset_of_nonneg zmset_of_plus)
                subgoal
                  using in_frontier_zcount by blast
                done
              subgoal
                apply (drule zcount_gt_0_in_set_2)
                apply (elim exE conjE)
                subgoal for m
                  apply (drule bspec)
                  apply simp
                  apply (rule disjI2)
                  apply (rule disjI1)
                  apply (rule bexI[of _ "(_, _, m)"])
                  apply simp
                  apply assumption
                  apply simp
                  apply (metis (no_types, opaque_lifting) frontier_less_equal_addI group_cancel.add2 zcount_zmset_of_nonneg zmset_of_plus)
                  done
                done
              done
            subgoal
              by force
            subgoal
              by force
            done
          subgoal premises prems2
            using prems(1,2,3,9,10,11,12,14,24) using prems2(1,2,3) apply -
            unfolding changes_above_impl_def extract_progress_def
            apply (auto simp add: split_beta; hypsubst_thin?)  
            subgoal for m t'
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              apply force
              done
            subgoal for m t'
              apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
              apply (drule bspec[of _ _ "(_, t', m)"])
              apply simp 
              apply (rule disjI2)
              apply force
              apply simp
              apply (drule frontier_less_equal_add_cases)
              apply (elim disjE)
              subgoal
                apply (rule frontier_less_equal_addI)
                apply simp_all
                done
              subgoal
                apply (rule frontier_less_equal_addI)
                apply (simp_all add: update_zmultiset_singleton)
                apply (rule disjI1)
                unfolding BHD_def
                apply (cases "buf1 (Inr (1, 1))"; simp)
                subgoal for a as
                  apply (cases a; simp)
                  apply hypsubst_thin
                  using prems(31) apply -
                  apply (drule spec2)
                  apply (drule mp)
                  apply blast
                  apply simp
                  unfolding frontier_less_equal_iff2
                  apply (meson frontier_less_equal_iff2 frontier_less_equal_trans trivial_dataflow_topology_interpretation.obtain_frontier_elem)
                  done
                done
              done
            done
          subgoal premises prems2
            using prems(1,2,3,8,9,10,11,12,14,25) using prems2(1,2,3) apply -
            unfolding changes_above_impl_def extract_progress_def
            apply (auto 0 0 simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            subgoal
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
              subgoal
                apply (subgoal_tac 
                    "frontier_less_equal (frontier (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)))))))) t")
                subgoal
                  by (meson frontier_less_equal_addI zcount_zmset_of_nonneg)
                subgoal
                  by (simp add: frontier_less_equal_zcount_pos)
                done
              subgoal
                unfolding BHD_def
                apply (cases "buf1 (Inr (1, 1))"; simp)
                subgoal for a as
                  apply (cases a; simp)
                  apply (simp add: zmultiset_eq_iff)
                  apply (drule spec[of _ t])                
                  apply auto
                  apply (smt (z3) not_int_zless_negative zcount_zmset_ge_zero)
                  done
                done
              done
            subgoal
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
              subgoal
                apply (subgoal_tac 
                    "frontier_less_equal (frontier (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)))))))) t")
                subgoal
                  by (simp add: frontier_le_remove_left frontier_less_equal_le_trans)
                subgoal
                  by (simp add: frontier_less_equal_zcount_pos)
                done
              subgoal
                unfolding BHD_def
                apply (cases "buf1 (Inr (1, 1))"; simp)
                subgoal for a as
                  apply (cases a; simp)
                  apply (simp add: zmultiset_eq_iff)
                  apply (drule spec[of _ t])                
                  apply auto
                  apply (smt (z3) not_int_zless_negative zcount_zmset_ge_zero)
                  done
                done
              done
            subgoal
              apply (drule bspec)
              apply auto
              done
            subgoal
              apply (drule bspec)
              apply auto
              done
            done
          subgoal
            using prems(1,2,3,9,10,11,12,26,25) apply -
            apply auto
            apply (smt (z3) comm_monoid_add_class.add_0 zcount_union zcount_update_zmultiset)
            done
          subgoal
            using prems(1,2,3,9,10,11,12,27) by auto
          subgoal
            using prems(1,2,3,9,10,11,12,28,29) apply -
            unfolding BHD_def
            apply (cases "buf1 (Inr (1, 1))")
            apply (auto simp add: split_beta)
            subgoal for a as
              apply (cases a; simp)
              apply (metis capability.sel(1) insert_iff set_insort_key)
              done
            done
          subgoal
            using prems(29) apply -
            unfolding BTL_def
            apply (auto simp add: split_beta)
            subgoal for a b x
              apply (drule spec[of _ a])
              apply (drule spec[of _ b])
              apply (elim conjE)
              apply (drule mp)
              apply (rule image_eqI[rotated])
              apply (drule in_set_tlD)
              apply assumption
              apply auto
              done
            done
          subgoal
            using prems(4,28,29,30) apply -
            unfolding BENQ_def BHD_def
            apply (cases "buf1 (Inr (1, 1))")
            apply (auto simp add: split_beta split: if_splits)
            apply (metis prod.sel(2))
            subgoal for a as
              apply (cases a; simp)
              subgoal for p
                apply (cases p)
                apply auto
                done
              done
            done
          subgoal
            using prems(31) by auto
          subgoal premises prems2
            using prems2(1,2,3,4) prems(32,33) apply -
            unfolding BTL_def BHD_def
            apply (cases "buf1 (Inr (1, 1))")
            apply (auto simp add: set_insort_key dest: in_set_tlD)
            apply (metis (no_types, lifting) UnCI image_iff snd_conv)+
            done
          subgoal premises prems2
            using prems2(1,2,3,4) prems(32,33) apply -
            unfolding BTL_def BHD_def
            apply (cases "buf1 (Inr (1, 1))")
            apply (auto dest: in_set_tlD)
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
            apply simp_all
            subgoal
              unfolding max_from_caps_buf_def BENQ_def BTL_def comp_def list_to_buf_def BULK_BENQ_def BHD_def
              apply (auto simp add: split_beta)
              subgoal
                apply (cases "buf1 (Inr (1, 1))"; auto)
                subgoal for a as
                  apply (cases a; simp)
                  done
                subgoal for a as
                  apply (cases a; simp add: set_insort_key)
                  subgoal premises prems2
                    subgoal
                      apply (subgoal_tac 
                          "map (\<lambda>cap. (Max (set (if cap = Cap t 1 then buf2 (Cap t 1) @ [n'] else buf2 cap) \<union> (fst ` {x \<in> projr ` set as. snd x = time cap} \<union> fst ` {x \<in> set (outpu os1 1). snd x = time cap})),
                 time cap))  (insort_key time (Cap t 1) caps) = 
  map (\<lambda>cap. (Max (set (buf2 cap) \<union> (fst ` {x. (x = (n', t) \<or> x \<in> projr ` set as) \<and> snd x = time cap} \<union> fst ` {x \<in> set (outpu os1 1). snd x = time cap})), time cap)) caps @
    [(Max (set (buf2 (Cap t 1)) \<union> (fst ` {x. (x = (n', t) \<or> x \<in> projr ` set as) \<and> snd x = t} \<union> fst ` {x \<in> set (outpu os1 1). snd x = t})), t)]")
                      subgoal
                        apply (auto simp add: )
                        subgoal 
                          by (metis (no_types, opaque_lifting) prod.sel(2))
                        subgoal
                          by (metis (mono_tags, lifting) sndE)
                        done
                      subgoal
                        apply auto
                        apply (subgoal_tac "insort_key time (Cap t 1) caps = caps @ [Cap t 1]")
                        subgoal
                          apply (auto 0 0)
                          subgoal
                            apply (rule Max_eq_if)
                            apply simp_all
                            using prems2(1) apply force+
                            done
                          subgoal
                            using prems2(1) apply -
                            apply (rule Max_eq_if)
                            apply simp_all
                            apply blast
                            apply auto
                            apply (metis capability.exhaust capability.sel(1) num1_eq1)
                            done
                          subgoal
                            apply (rule Max_eq_if)
                            apply simp_all
                            subgoal
                              apply auto
                              apply (metis (mono_tags, lifting) UnCI img_fst mem_Collect_eq nle_le split_pairs2)
                              done
                            subgoal
                              apply auto
                              done
                            done
                          done
                        subgoal
                          apply (subgoal_tac "\<forall> cap \<in> set caps. time cap \<le> t")
                          subgoal
                            using prems(7,32) apply -
                            apply auto
                            apply (rule insort_key_last)
                            using prems2(1) apply auto
                            subgoal for x
                              apply (cases x; simp)
                              done
                            done
                          subgoal
                            using prems2(4-) prems(7,32) apply -
                            apply auto
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
        subgoal for batch
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
          subgoal using prems(3) by (simp add: produce_def)
          apply (rule refl)+
          subgoal using prems(6) by simp
          subgoal using prems(7) apply -
            using sorted_filter by blast
          subgoal using prems(8) by simp
          subgoal using prems(9,2,3,9,10,11,12)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13) apply -
            apply (auto simp add: ac_simps update_zmultiset_replicate input_cap_def zmset_of_plus group_cancel.sub1 produce_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            apply (metis arith_simps(49) diff_add_zmset zmultiset_move_add_other_side)
            done
          subgoal using prems(10,9,2,3,9,10,11,12,13,14)
            by (auto simp add: zmset_of_plus group_cancel.sub1 produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(10,9,2,3,9,10,11,12,13,14,15) 
            by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(16) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal using prems(17) by (auto simp add:  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
          subgoal 
            using prems(1,6,10,9,2,3,9,10,11,18,13,14,12) apply -
            apply (auto 0 0 simp add: ac_simps split_beta input_cap_def update_zmultiset_replicate  produce_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            subgoal for x t
              apply (drule spec[of _ x])
              apply (drule spec[of _ t])
              apply auto
              subgoal
                unfolding frontier_less_equal_iff2
                apply auto
                subgoal premises prems4
                  using prems4(13) apply -
                  apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier
                  (zmset_of (mset_set (set_antichain (frontier (zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#})))))) \<and> t' \<le> t")
                  subgoal
                    by (simp add: add.commute add_diff_eq prems4(9))
                  subgoal
                    apply simp
                    apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (zmset_of (snd `# mset (outpu os1 1))) \<and> t' \<le> t")
                    subgoal
                      apply safe
                      subgoal for t'
                        apply (simp add: zmset_of_plus)
                        apply (rule in_frontier_in_frontier_add_alt[of t'])
                        apply auto
                        done
                      done
                    subgoal
                      by (meson img_snd in_frontier_zmset_of_snd_mset prems4(12))
                    done
                  done
                done
              subgoal
                unfolding frontier_less_equal_iff2
                apply auto
                subgoal premises prems4
                  using prems4(13) apply -
                  apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier
                  (zmset_of (mset_set (set_antichain (frontier (zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#})))))) \<and> t' \<le> t")
                  subgoal
                    by (simp add: add.commute add_diff_eq prems4(9))
                  subgoal
                    apply simp
                    apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (zmset_of (snd `# mset (outpu os1 1))) \<and> t' \<le> t")
                    subgoal
                      apply safe
                      subgoal for t'
                        apply (simp add: zmset_of_plus)
                        apply (rule in_frontier_in_frontier_add_alt[of t'])
                        apply auto
                        done
                      done
                    subgoal
                      by (meson img_snd in_frontier_zmset_of_snd_mset prems4(12))
                    done
                  done
                done
              done
            subgoal for a t x
              unfolding frontier_less_equal_iff2
              apply (cases x; simp; hypsubst_thin)
              apply force
              subgoal premises prems4 for b
                using prems4(13) apply -
                apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier
                  (zmset_of (mset_set (set_antichain (frontier (zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#})))))) \<and> t' \<le> t")
                subgoal
                  by (simp add: add.commute add_diff_eq prems4(10))
                subgoal
                  apply (subgoal_tac "\<exists>t'. t' \<in>\<^sub>A frontier (zmset_of (mset_set (set_antichain (frontier (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#})))))) \<and> t' \<le> t")
                  subgoal
                    apply simp
                    apply safe
                    subgoal for t'
                      apply (simp add: zmset_of_plus)
                      apply (smt (verit, del_insts) in_frontier_in_frontier_add_alt union_ac(2) zcount_zmset_of_nonneg zmset_of_plus)
                      done
                    done
                  subgoal
                    apply simp
                    apply (rule in_frontier_zcount)
                    apply force
                    done
                  done
                done
              done
            subgoal for x t
              apply (drule spec[of _ x])
              apply (drule spec[of _ t])
              apply auto
              subgoal
                unfolding frontier_less_equal_iff2
                apply (subst (5) add.commute)
                apply (subst (2) add.assoc[symmetric])
                apply simp
                apply (subst (1) add.assoc[symmetric])
                apply (auto simp add: ac_simps)
                subgoal premises prems4
                  using prems4(14) apply -
                  apply (subgoal_tac "\<exists>t'\<le>t. t' \<in>\<^sub>A frontier (zmset_of (mset_set (set_antichain (frontier (zmset_of {#n 1. x \<in># mset batch#} + zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#}))))))")
                  subgoal
                    apply (subst (2) add.commute)
                    apply (meson fronteier_lt_add_ex zmset_of_mset_set_ge_zero)
                    done
                  subgoal
                    apply simp
                    apply (rule in_frontier_zcount_alt)
                    apply auto
                    apply (smt (z3) count_image_mset_ge_count count_mset_gt_0 negative_zle of_nat_le_0_iff prems4(13) prod.sel(2) verit_comp_simplify1(3))
                    done
                  done
                done
              subgoal
                unfolding frontier_less_equal_iff2
                apply (subst (5) add.commute)
                apply (subst (2) add.assoc[symmetric])
                apply simp
                apply (subst (1) add.assoc[symmetric])
                apply (auto simp add: ac_simps)
                subgoal premises prems4
                  using prems4(14) apply -
                  apply (subgoal_tac "\<exists>t'\<le>t. t' \<in>\<^sub>A frontier (zmset_of (mset_set (set_antichain (frontier (zmset_of {#n 1. x \<in># mset batch#} + zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#}))))))")
                  subgoal
                    apply (subst (2) add.commute)
                    apply (meson fronteier_lt_add_ex zmset_of_mset_set_ge_zero)
                    done
                  subgoal
                    apply simp
                    apply (rule in_frontier_zcount_alt)
                    apply auto
                    apply (smt (z3) count_image_mset_ge_count count_mset_gt_0 negative_zle of_nat_le_0_iff prems4(13) prod.sel(2) verit_comp_simplify1(3))
                    done
                  done
                done
              done
            subgoal for x
              unfolding frontier_less_equal_iff2
              apply (subst (5) add.commute)
              apply (subst (2) add.assoc[symmetric])
              apply simp
              apply (subst (1) add.assoc[symmetric])
              apply (auto simp add: ac_simps)
              subgoal premises prems4
                apply (subgoal_tac "\<exists>t'\<le>n 1. t' \<in>\<^sub>A frontier (zmset_of (mset_set (set_antichain (frontier (zmset_of {#n 1. x \<in># mset batch#} + zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#}))))))")
                subgoal
                  apply (subst (2) add.commute)
                  apply (meson fronteier_lt_add_ex zmset_of_mset_set_ge_zero)
                  done
                subgoal
                  apply simp
                  apply (rule in_frontier_zcount_alt)
                  apply auto
                  using prems4(14)
                  apply (metis (lifting) count_image_mset_ge_count count_mset_gt_0 int_plus neq0_conv not_add_less1 of_nat_0_less_iff prems4(14) verit_comp_simplify(3))
                  done
                done
              done
            subgoal for a t x             
              apply (cases x; simp; hypsubst_thin)
              apply force
              subgoal for t'
                unfolding frontier_less_equal_iff2
                apply (subst (5) add.commute)
                apply (subst (2) add.assoc[symmetric])
                apply simp
                apply (subst (1) add.assoc[symmetric])
                apply (auto 0 0 simp add: ac_simps)
                apply (subst (2) add.commute)
                apply (subgoal_tac "\<exists>t'\<le>t. t' \<in>\<^sub>A frontier
                (zmset_of (mset_set (set_antichain (frontier (zmset_of {#n 1. x \<in># mset batch#} + zmset_of (snd `# mset (outpu os1 1) + {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#}))))))")
                subgoal
                  apply simp
                  apply (smt (z3) fronteier_lt_add_ex frontier_idempotent zcount_zmset_of_nonneg)
                  done
                subgoal
                  apply simp
                  apply (rule in_frontier_zcount_alt)
                  apply (subgoal_tac "0 < int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t)")
                  subgoal
                    by (smt (verit, ccfv_threshold) zcount_of_mset zcount_union zcount_zmset_of_nonneg zmset_of_plus)
                  subgoal
                    apply clarsimp
                    apply (rule image_eqI[rotated])
                    apply assumption
                    apply auto
                    done
                  done
                done
              done
            done
          subgoal using prems(19) by simp
          subgoal using prems(20) by simp
          subgoal using prems(21) by simp
          subgoal using prems(1,2,3,9,10,11,12,13,14,15,22) apply -
            apply auto
            unfolding changes_non_zero_def extract_progress_def comp_def
            apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
            done
          subgoal premises prems2
            unfolding produce_def
            apply auto
            defer
            subgoal
              using prems(2,9,10,23,11) prems(13)[symmetric] prems2(2) apply -
              unfolding extract_progress_def comp_def input_cap_def
              apply auto
              apply hypsubst_thin
              apply (rule changes_above_impl_extend[where B="[(Loc 0 (Src 1), n 1, - 1),(Loc 1 (Trg 1), n 1, int (length batch))]"])
              apply assumption
              apply (simp_all add: c_pts_change_multiplicities)
              subgoal premises prems3
                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or>  zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
                defer
                subgoal
                  using prems3(4) by (smt (verit) zcount_single zcount_union)
                subgoal
                  apply (elim disjE)
                  subgoal
                    unfolding changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ
                    apply auto
                    subgoal 
                      by (metis frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                    subgoal 
                      by (simp add: Groups.add_ac(2,3)
                          \<open>0 < zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) \<Longrightarrow> frontier_less_equal (frontier (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))))) (n 1)\<close>
                          frontier_less_equal_addI)
                    done
                  subgoal
                    using prems3(3) apply -
                    unfolding changes_above_impl_def
                    apply (clarsimp split: prod.splits)
                    apply (intro conjI ballI)
                    subgoal
                      apply (subgoal_tac "\<exists> m. (1, n 1, m) \<in> set (operator_state.inter os1) \<and> m > 0")
                      subgoal
                        apply (elim exE conjE)
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply fast
                          apply simp
                          done
                        done
                      subgoal
                        by (meson zcount_gt_0_in_set_2)
                      done
                    subgoal
                      apply (subgoal_tac "\<exists> m. (1, n 1, m) \<in> set (operator_state.inter os1) \<and> m > 0")
                      subgoal
                        apply (elim exE conjE)
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply fast
                          apply simp
                          unfolding frontier_less_equal_iff dataflow_topology_implied_frontier_alt_my_summ
                          apply simp
                          apply (rule order.trans[rotated])
                          apply assumption
                          apply (metis (no_types, opaque_lifting) Groups.add_ac(1) frontier_below_eq_frontier_plus_pos zcount_zmset_of_nonneg)
                          done
                        done
                      subgoal
                        by (meson zcount_gt_0_in_set_2)
                      done
                    done
                  done
                done
              done
            subgoal
              using prems(2,9,10,23,11) prems(13)[symmetric] prems2(2) apply -
              unfolding extract_progress_def comp_def input_cap_def
              apply auto
              apply hypsubst_thin
              apply (rule changes_above_impl_extend[where B="[(Loc 0 (Src 1), n 1, - 1)]"])
              apply assumption
              apply (simp_all add: c_pts_change_multiplicities)
              subgoal premises prems3
                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or>  zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
                defer
                subgoal
                  using prems3 by (smt (verit) zcount_single zcount_union)
                subgoal
                  apply (elim disjE)
                  subgoal
                    unfolding changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ
                    apply auto
                    subgoal
                      by (metis (no_types, opaque_lifting) Suc_n_not_le_n frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_le_trans frontier_less_equal_trans frontier_less_equal_zcount_pos linorder_linear zcount_zmset_of_nonneg)
                    done
                  subgoal
                    using prems3 apply -
                    unfolding changes_above_impl_def
                    apply (clarsimp split: prod.splits)
                    subgoal
                      apply (subgoal_tac "\<exists> m. (1, n 1, m) \<in> set (operator_state.inter os1) \<and> m > 0")
                      subgoal
                        apply (elim exE conjE)
                        subgoal for m
                          apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                          apply fast
                          apply simp
                          done
                        done
                      subgoal
                        by (meson zcount_gt_0_in_set_2)
                      done
                    done
                  done
                done
              done
            done
          subgoal premises prems2
            unfolding produce_def
            apply auto
            subgoal
              using prems(1,2,9,10,24,11) prems(13) prems2(2) apply -
              unfolding extract_progress_def
              apply (auto simp add: produce_def input_cap_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              apply (rule changes_above_impl_extend[where B="(Loc 0 (Src 1), n 1, - 1) # []"])
              apply assumption
              apply auto
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
              subgoal
                apply (elim disjE)
                subgoal premises prems3
                  using prems3(6) apply -
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply ((intro ballI impI conjI allI)?; (simp add: split_beta)?)
                  subgoal
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 0 (Src 1)"])
                    apply simp_all
                    apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    unfolding frontier_less_equal_iff2
                    using in_frontier_zcount apply blast
                    done
                  done
                subgoal premises prems3
                  using prems3(3,6) apply -
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply ((intro ballI impI conjI allI)?; (simp add: split_beta)?)
                  subgoal
                    apply (drule zcount_gt_0_in_set_2)
                    apply (elim exE)
                    subgoal for m
                      apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                      apply simp
                      apply (rule disjI2)
                      apply (rule image_eqI[rotated])
                      apply auto
                      done
                    done
                  done
                done
              subgoal
                by (smt (verit, del_insts) zcount_add_zmset zcount_empty zcount_union)
              done
            subgoal
              using prems(1,2,9,10,24,11) prems(13) prems2(2) apply -
              unfolding extract_progress_def
              apply (auto simp add: produce_def input_cap_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
              apply (rule changes_above_impl_extend[where B="(Loc 0 (Src 1), n 1, - 1) # [(Loc 1 (Trg 1), n 1, int (length batch))]"])
              apply assumption
              apply auto
              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
              subgoal
                apply (elim disjE)
                subgoal premises prems3
                  using prems3(7) apply -
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; (simp add: split_beta)?)
                  subgoal
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 0 (Src 1)"])
                    apply simp_all
                    apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    unfolding frontier_less_equal_iff2
                    using in_frontier_zcount apply blast
                    done
                  subgoal
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 0 (Src 1)"])
                    apply (auto simp add: produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                    unfolding frontier_less_equal_iff2
                    using in_frontier_zcount apply blast
                    using l0_lt_l1 le_less apply blast
                    done
                  done
                subgoal premises prems3
                  using prems3(4,7) apply -
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; (simp add: split_beta)?)
                  subgoal
                    apply (drule zcount_gt_0_in_set_2)
                    apply (elim exE)
                    subgoal for m
                      apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                      apply simp
                      apply (rule disjI2)
                      apply (rule image_eqI[rotated])
                      apply auto
                      done
                    done
                  subgoal
                    apply (drule zcount_gt_0_in_set_2)
                    apply (elim exE)
                    subgoal for m
                      apply (drule bspec[of _ _ "(Loc 0 (Src 1), n 1, m)"])
                      apply simp
                      apply force
                      apply auto
                      unfolding frontier_less_equal_iff
                      apply (rule order.trans[rotated])
                      apply assumption
                      apply (auto simp add: dataflow_topology_implied_frontier_alt_my_summ produce_def  extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                      apply (metis (mono_tags, lifting) add.assoc frontier_below_eq_frontier_plus_pos zmset_of_mset_set_ge_zero)
                      done
                    done
                  done
                done
              subgoal
                by (smt (verit, del_insts) zcount_add_zmset zcount_empty zcount_union)
              done
            done
          subgoal premises prems2
            using prems2(2) apply -
            unfolding produce_def
            apply auto
            subgoal
              using prems(1,2,3,9,10,25,11,14) prems(13) apply -
              apply simp
              unfolding extract_progress_def input_cap_def
              apply auto
              apply hypsubst_thin
              apply (auto 0 0 simp add: add.assoc dataflow_topology_implied_frontier_alt_my_summ update_zmultiset_replicate c_pts_change_multiplicities)
              apply (subgoal_tac 
                  "change_multiplicities my_summ
       (map (\<lambda>(p, y). (Loc 0 (Src 1), y)) (operator_state.inter os1) @ (Loc 0 (Src 1), n 1, - 1) # concat (map (\<lambda>(p, t, m). [(Loc 1 (Trg 1), t, m)]) (produ os1)))
       (pt_tr sg) = 
   change_multiplicities my_summ [(Loc 0 (Src 1), n 1, - 1)] (change_multiplicities my_summ (map (\<lambda>(p, y). (Loc 0 (Src 1), y)) (operator_state.inter os1) @ concat (map (\<lambda>(p, t, m). [(Loc 1 (Trg 1), t, m)]) (produ os1))) (pt_tr sg))")
              defer
              subgoal premises
                apply (simp flip: change_multiplicities_append_alt)
                apply (rule fun_cong[where x="(pt_tr sg)"])
                apply (rule change_multiplicities_appen_cong)
                apply (rule ext)
                using change_multiplicities_comm 
                apply (metis (no_types, lifting) append_Cons empty_append_eq_id)
                done
              subgoal premises prems3
                apply (simp add: prems3(8))
                using prems3(5) apply -
                subgoal
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; simp)
                  apply (elim disjE exE)
                  subgoal for x l t a
                    apply auto
                    apply hypsubst_thin
                    apply (drule bspec)
                    apply blast
                    apply simp
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Trg 1)"])
                    apply (simp_all add: c_pts_change_multiplicities)
                    subgoal premises prems4 for m
                      using prems4(1) apply -
                      using prems(1,2,12,11,9,10,22) apply -
                      unfolding extract_progress_def input_cap_def changes_non_zero_def
                      apply (auto simp add: c_pts_change_multiplicities)
                      apply hypsubst_thin
                      apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
                      subgoal
                        unfolding frontier_less_equal_iff2
                        by (meson trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                      subgoal
                        apply (rule zcount_gt_0_zmulset_diff[where B="zmset (map snd (consu os2))" and C="zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1))"])
                        apply (simp add: add_diff_eq)
                        apply simp_all
                        subgoal premises prems5
                          using prems5(1,5) apply -
                          apply (rule zcount_zmset_gt_0[where m=m])
                          apply force
                          apply simp_all
                          using prems(8) apply force
                          using prems(8) apply auto
                          done
                        done
                      done
                    done
                  subgoal for x l t m
                    apply auto
                    apply hypsubst_thin
                    apply (drule bspec)
                    apply blast
                    apply simp      
                    subgoal
                      apply (cases "zcount (zmset (map snd (operator_state.inter os2))) t < 0")
                      subgoal
                        apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Src 1)"])
                        using prems(2,15,11,9,10) apply -
                        unfolding extract_progress_def input_cap_def
                        apply (auto 0 0 simp add: add.assoc dataflow_topology_implied_frontier_alt_my_summ update_zmultiset_replicate c_pts_change_multiplicities)
                        apply hypsubst_thin
                        apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Src 1))) t > 0")
                        subgoal
                          unfolding frontier_less_equal_iff2
                          by (meson trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                        subgoal
                          unfolding zmultiset_eq_iff
                          apply (drule spec[of _ t])
                          apply simp
                          done
                        done
                      subgoal
                        unfolding not_less
                        using prems(26,27) apply -
                        apply (drule spec[of _ t])+
                        apply (drule spec)
                        apply (drule mp)
                        apply simp
                        apply (drule mp)
                        apply simp
                        apply auto
                        subgoal for m'
                          apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Trg 1)"])
                          apply (simp_all add: c_pts_change_multiplicities)
                          subgoal premises prems4
                            using prems4(5) apply -
                            using prems(1,2,12,11,9,10,22) apply -
                            unfolding extract_progress_def input_cap_def changes_non_zero_def
                            apply (auto simp add: c_pts_change_multiplicities)
                            apply hypsubst_thin
                            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
                            subgoal
                              unfolding frontier_less_equal_iff2
                              by (meson trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                            subgoal
                              apply (rule zcount_gt_0_zmulset_diff[where B="zmset (map snd (consu os2))" and C="zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1))"])
                              apply (simp add: add_diff_eq)
                              apply simp_all
                              subgoal premises prems5
                                using prems5(1,5) apply -
                                apply (rule zcount_zmset_gt_0[where m=m'])
                                apply force
                                apply simp_all
                                using prems(8) apply force
                                using prems(8) apply auto
                                done
                              done
                            done
                          subgoal
                            apply (rule order.strict_implies_order)
                            apply auto
                            using less_eq_port.simps(3,4) less_port_def apply blast
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done
            subgoal
              using prems(1,2,3,9,10,25,11,14) prems(13) apply -
              apply simp
              unfolding extract_progress_def input_cap_def
              apply auto
              apply hypsubst_thin
              apply (auto 0 0 simp add: add.assoc dataflow_topology_implied_frontier_alt_my_summ update_zmultiset_replicate c_pts_change_multiplicities)
              apply (subgoal_tac 
                  "change_multiplicities my_summ
       (map (\<lambda>(p, y). (Loc 0 (Src 1), y)) (operator_state.inter os1) @ (Loc 0 (Src 1), n 1, - 1) # concat (map (\<lambda>(p, t, m). [(Loc 1 (Trg 1), t, m)]) (produ os1)))
       (pt_tr sg) = 
   change_multiplicities my_summ [(Loc 0 (Src 1), n 1, - 1)] (change_multiplicities my_summ (map (\<lambda>(p, y). (Loc 0 (Src 1), y)) (operator_state.inter os1) @ concat (map (\<lambda>(p, t, m). [(Loc 1 (Trg 1), t, m)]) (produ os1))) (pt_tr sg))")
              defer
              subgoal premises
                apply (simp flip: change_multiplicities_append_alt)
                apply (rule fun_cong[where x="(pt_tr sg)"])
                apply (rule change_multiplicities_appen_cong)
                apply (rule ext)
                using change_multiplicities_comm 
                apply (metis (no_types, lifting) append_Cons empty_append_eq_id)
                done
              subgoal premises prems3
                using prems3(5) prems3(9) apply -
                subgoal
                  unfolding changes_above_impl_def
                  apply (simp split: prod.splits)
                  apply (intro ballI impI conjI allI; simp)
                  apply (elim disjE exE)
                  subgoal for x l t a
                    apply auto
                    apply hypsubst_thin
                    apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Trg 1)"])
                    apply (simp_all add: c_pts_change_multiplicities)
                    subgoal premises prems4 for m
                      using prems4(3) apply -
                      using prems(1,2,12,11,9,10,22) apply -
                      unfolding extract_progress_def input_cap_def changes_non_zero_def
                      apply (auto simp add: c_pts_change_multiplicities)
                      apply hypsubst_thin
                      apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
                      subgoal
                        unfolding frontier_less_equal_iff2
                        apply (subgoal_tac "\<forall> t. zcount (zmset_of {#n 1. x \<in># mset batch#}) t \<ge> 0")
                        subgoal
                          apply (erule trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                          apply auto
                          apply (smt (verit, best) Groups.add_ac(1) in_frontier_in_frontier_add_alt zcount_zmset_of_nonneg)
                          done
                        subgoal
                          by auto
                        done
                      subgoal
                        apply (rule zcount_gt_0_zmulset_diff[where B="zmset (map snd (consu os2))" and C="zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1))"])
                        apply (simp add: add_diff_eq)
                        apply simp_all
                        subgoal premises prems5
                          using prems5(1,5) apply -
                          apply (rule zcount_zmset_gt_0[where m=m])
                          apply force
                          apply simp_all
                          using prems(8) apply force
                          using prems(8) apply auto
                          done
                        done
                      done
                    done
                  subgoal for x l t m
                    apply auto
                    apply hypsubst_thin    
                    subgoal
                      apply (cases "zcount (zmset (map snd (operator_state.inter os2))) t < 0")
                      subgoal
                        apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Src 1)"])
                        using prems(2,15,11,9,10) apply -
                        unfolding extract_progress_def input_cap_def
                        apply (auto 0 0 simp add: add.assoc dataflow_topology_implied_frontier_alt_my_summ update_zmultiset_replicate c_pts_change_multiplicities)
                        apply hypsubst_thin
                        apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Src 1))) t > 0")
                        subgoal
                          unfolding frontier_less_equal_iff2
                          by (meson trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                        subgoal
                          unfolding zmultiset_eq_iff
                          apply (drule spec[of _ t])
                          apply simp
                          done
                        done
                      subgoal
                        unfolding not_less
                        using prems(26,27) apply -
                        apply (drule spec[of _ t])+
                        apply (drule spec)
                        apply (drule mp)
                        apply simp
                        apply (drule mp)
                        apply simp
                        apply auto
                        subgoal for m'
                          apply (rule frontier_less_equal_implied_frontier[of _ "Loc 1 (Trg 1)"])
                          apply (simp_all add: c_pts_change_multiplicities)
                          subgoal premises prems4
                            using prems4(6) apply -
                            using prems(1,2,12,11,9,10,22) apply -
                            unfolding extract_progress_def input_cap_def changes_non_zero_def
                            apply (auto simp add: c_pts_change_multiplicities)
                            apply hypsubst_thin
                            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1))) t > 0")
                            subgoal
                              unfolding frontier_less_equal_iff2
                              apply (subgoal_tac "\<forall> t. zcount (zmset_of {#n 1. x \<in># mset batch#}) t \<ge> 0")
                              subgoal
                                apply (erule trivial_dataflow_topology_interpretation.obtain_elem_frontier)
                                apply auto
                                apply (smt (verit, best) Groups.add_ac(1) in_frontier_in_frontier_add_alt zcount_zmset_of_nonneg)
                                done
                              subgoal
                                by auto
                              done
                            subgoal
                              apply (rule zcount_gt_0_zmulset_diff[where B="zmset (map snd (consu os2))" and C="zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1))"])
                              apply (simp add: add_diff_eq)
                              apply simp_all
                              subgoal
                                apply (rule zcount_zmset_gt_0[where m=m'])
                                apply force
                                apply simp_all
                                using prems(8) apply force
                                using prems(8) apply auto
                                done
                              done
                            done
                          subgoal
                            apply (rule order.strict_implies_order)
                            apply auto
                            using less_eq_port.simps(3,4) less_port_def apply blast
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
            using prems(26) by simp
          subgoal
            using prems(27) by simp
          subgoal
            using prems(28) by auto
          subgoal
            using prems(29) apply -
            unfolding produce_def 
            apply force
            done
          subgoal
            using prems(30) by simp
          subgoal premises prems2
            using prems(1,2,13,31,9,10,11) prems2(2) apply -
            unfolding produce_def input_cap_def extract_progress_def
            apply (clarsimp simp add: c_pts_change_multiplicities split: if_splits)
            apply hypsubst_thin
            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 1) > 0 \<or> zcount (zmset (map snd (operator_state.inter os1))) (n 1) > 0")
            subgoal
              apply auto
              apply (meson zcount_gt_0_in_set_2)
              apply (meson le_SucI zcount_gt_0_in_set_2)+
              done
            subgoal
              by (simp add: sum_gt_zeroD zmultiset_eq_iff)
            done
          subgoal
            using prems(4,32) apply -
            unfolding produce_def 
            apply clarsimp
            using
              \<open>1 \<notin> defaults \<Longrightarrow> inps 1 = LCons batch LNil \<Longrightarrow> xs 0 = outpu os2 0 \<Longrightarrow> ys 0 = max_from_buf caps buf2 ((map projr \<circ> buf1 \<circ> Inr \<circ>\<circ> Pair) 1 0 @ outpu os1 0) \<Longrightarrow> \<forall>cap. cap \<in> set caps \<longrightarrow> time cap < map_entry 1 Suc n 1\<close>
            apply auto
            done
          subgoal
            using prems(4,33,29) apply -
            unfolding produce_def
            apply (auto simp add: sorted_append comp_def)
            using sorted_map apply fastforce
            using sorted_map apply fastforce
            apply (metis imageI nat_less_le old.prod.exhaust snd_conv)
            done
          subgoal
            apply (rule rtranclp_intros_1)
            apply (rule arg_cong3[where f=map_op])
            apply simp
            apply simp_all
            apply (subst iterates.code)
            apply (auto split: list.splits)
            subgoal
              apply (rule arg_cong[where f=source_op])
              apply (rule ext)
              apply (rule arg_cong2[where f=lshift])
              apply simp
              apply simp_all
              apply (rule arg_cong2[where f=max_from_caps_buf])
              apply (auto simp add: produce_def comp_def)
              done
            subgoal for x xs
              apply (rule arg_cong[where f=source_op])
              apply (rule ext)
              apply (rule arg_cong2[where f=lshift])
              apply simp
              apply (simp add: comp_def flip: snoc_shift)
              unfolding outpu_produce
              subgoal premises prems3
                unfolding max_from_caps_buf_append
                apply (simp only: list.simps list_to_buf_def)
                unfolding max_from_caps_buf_def map_append append_assoc
                apply (intro arg_cong2[where f=append])
                subgoal
                  using prems(28) apply -
                  unfolding list_to_buf_def BULK_BENQ_def
                  apply auto
                  done
                subgoal
                  apply (auto 0 0)
                  apply (rule Max_eq_if)
                  using prems(6,28,29) apply -
                  unfolding list_to_buf_def BULK_BENQ_def
                  apply (auto simp add: split_beta split: sum.splits)
                  subgoal for x'
                    apply (cases x'; simp)
                    apply fastforce
                    subgoal for a
                      apply (cases a)
                      apply (auto simp add: split_beta split: sum.splits; hypsubst_thin)
                      subgoal for a
                        apply (rule bexI[of _ a])
                        using image_iff apply fastforce+
                        done
                      done
                    done
                  subgoal for x' a
                    apply (cases x'; simp)
                    apply fastforce
                    using prems(6,28,29,30) apply -
                    unfolding list_to_buf_def BULK_BENQ_def
                    apply (auto simp add: split_beta split: sum.splits)       
                    using image_iff apply fastforce
                    done
                  done
                subgoal
                  using prems(6,28,29,30) apply -
                  unfolding rmdups_append BULK_BENQ_def
                  apply (rule sym)
                  apply (auto simp add: comp_def split_beta split: sum.splits; hypsubst_thin?)
                  apply (metis (no_types, opaque_lifting) imageI less_irrefl_nat prod.exhaust snd_conv)
                  apply (metis (no_types, opaque_lifting) less_irrefl_nat)
                  apply (metis (no_types, opaque_lifting) less_irrefl_nat)
                  apply (metis (no_types, opaque_lifting) less_irrefl_nat)
                  subgoal
                    apply (rule Max_eq_if)
                    apply simp_all
                    subgoal
                      apply (auto simp add: comp_def split_beta split: sum.splits; hypsubst_thin?)
                      apply (metis (lifting) image_iff)
                      apply blast
                      done
                    subgoal
                      apply (auto simp add: comp_def split_beta split: sum.splits; hypsubst_thin?)
                      apply blast
                      done
                    done
                  subgoal
                    apply (rule rmdups_NilI)
                    apply auto
                    done
                  done
                done
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
    from SIM2 show ?thesis
      unfolding R_def[symmetric]
      apply -
      unfolding wsim_def
      apply (intro allI conjI impI)
      subgoal premises prems for io op1'
        using prems(34) apply -
        apply (elim step_map_op_elim step_source_op_elim conjE; simp split: if_splits; hypsubst_thin?)
        apply simp_all
        subgoal for x lxs
          apply (cases "xs 1")
          defer
          subgoal for a as
            apply clarsimp
            using prems(4,5) apply -
            apply hypsubst_thin
            apply (intro exI conjI[rotated])
            apply (intro relcomppI)
            apply (rule bisim_refl)
            defer
            apply (rule wbisim_refl)
            apply (rule step_wstep)
            apply (rule step_Out_dataflow_op_Out_Inr_intro)
            apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
            apply (rule step_map_op)
            apply (rule step_max_top'_Out_intro)
            apply (rule refl)
            apply (rule sym)
            apply simp_all
            unfolding R_def
            apply (rule wb_upto_b_sym)
            apply (rule wb_upto_b_base)
            apply simp
            apply (intro conjI exI; (rule refl)?; (simp add: prems)?)
            subgoal
              apply (rule arg_cong3[where f=map_op])
              apply (simp_all add: comp_def)
              apply (rule arg_cong[where f=source_op])
              apply (rule ext)+
              apply (clarsimp simp add: comp_def)
              done
            subgoal
              using prems(1,2,9,10,11,12) by (auto simp add: c_pts_change_multiplicities extract_progress_def)
            subgoal
              using prems(1,2,9,10,11,13) by (auto simp add: input_cap_def c_pts_change_multiplicities extract_progress_def)
            subgoal
              using prems(1,2,3,9,10,11,14) by (auto simp add: input_cap_def c_pts_change_multiplicities extract_progress_def; hypsubst_thin?)
            subgoal
              using prems(1,2,3,9,10,11,15) by (auto simp add: input_cap_def c_pts_change_multiplicities extract_progress_def; hypsubst_thin?)
            subgoal
              using prems(1,2,3,9,10,11,16) by (auto simp add: input_cap_def c_pts_change_multiplicities extract_progress_def; hypsubst_thin?)
            subgoal
              using prems(1,2,3,9,10,11,18) by (clarsimp simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            subgoal
              using prems(1,19) by auto
            subgoal
              using prems(1,2,9,10,22) by (force simp add: changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            subgoal premises prems2
              using prems(1,2,9,10,23) by (force simp add: changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            subgoal premises prems2
              using prems(1,2,9,10,24) by (force simp add: changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            subgoal premises prems2
              using prems(1,2,3,9,10,25) by (auto simp add: changes_above_impl_def dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
            subgoal
              using prems(26) by auto
            subgoal
              using prems(28) by auto
            subgoal
              using prems(29) by auto
            subgoal
              using prems(31) by auto
            subgoal
              using prems(32) by auto
            subgoal
              using prems(33) by auto
            done
          subgoal
            apply simp
            apply (cases "ys 1")
            subgoal
              apply (auto simp add: lconcat_eq_LCons_conv lmap_lshift_conv lmap_eq_LCons_conv lnull_def split: list.splits)
              subgoal
                apply (rule FalseE)
                by (meson list.exhaust)
              subgoal premises prems2 for zs batch t xs''

                apply (subgoal_tac "
       frontier (zmset_of
         (mset_set
           (set_antichain
             (frontier
               ({#n 0#}\<^sub>z +
                (zmset_of (Suc `# mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) - zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) +
                 update_zmultiset (update_zmultiset {#}\<^sub>z (Suc (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs))) 1) (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)) (- 1)))))) +
        zmset_of
         (mset_set
           (set_antichain
             (frontier
               (c_pts (pt_tr sg) (Loc 1 (Trg 1)) +
                (zmset (map snd (produ os1)) +
                 (Auxiliary.image_zmset (trivial_dataflow_topology_interpretation.followed_by (n 1)) (Auxiliary.image_zmset length (zmset_of (replicate_mset (length batch) zs))) +
                  (- zmset (map snd (consu os2)) - zmset_of {#t. x \<in># mset batch#})))))))) = frontier {#Suc (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs))#}\<^sub>z")
                defer
                subgoal premises
                  apply (subgoal_tac "
Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) + {#trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)#}\<^sub>z) +
                {#Suc (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs))#}\<^sub>z +
                {#n 1#}\<^sub>z =
Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                (zmset_of (mset_set {n 1..trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) +
                {#n 1#}\<^sub>z")
                  defer 
                  subgoal premises
                    apply (simp flip: atLeastLessThanSuc_atLeastAtMost)
                    apply (subst (1 2) atLeastLessThanSuc)
                    apply auto
                    done
                  subgoal
                    apply simp
                    apply (subgoal_tac "
add_zmset (n 1)
                 (Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                  zmset_of (mset_set {n 1..trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) =
{#Suc (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs))#}\<^sub>z")
                    defer
                    subgoal premises
                      apply (subst add_zmset_add_single)
                      apply (simp only: zmset_of_Suc_minus flip: zmset_of_image_mset)
                      done
                    apply simp
                    apply (subgoal_tac "
c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)) +
                Auxiliary.image_zmset (trivial_dataflow_topology_interpretation.followed_by (n 1)) (Auxiliary.image_zmset length (zmset_of (replicate_mset (length batch) zs))) +
                (- zmset (map snd (consu os2)) - zmset_of {#t. x \<in># mset batch#}) = {#}\<^sub>z")
                    subgoal
                      by (simp add: nat_arith.add1 update_zmultiset_one(1) update_zmultiset_singleton(2) zmset_of_image_mset)
                    subgoal premises prems5
                      using prems2(6) apply -
                      apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                      apply hypsubst_thin
                      apply (auto simp add: lshift_ltake_ldrop)
                      apply (drule sym[of "LCons (batch, t) xs''"])
                      apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                      apply hypsubst_thin
                      apply (subst (asm) (2) iterates)
                      apply auto
                      apply hypsubst_thin
                      subgoal premises prems6 for ys xs'
                        apply (auto simp flip: zmset_of_replicate_mset)
                        apply (subgoal_tac "min (length (list_of (ltake (enat (length ys)) (inps 1)))) (length ys) = length ys")
                        subgoal
                          apply (simp del: zmset_of_replicate_mset add: image_mset_const_eq)
                          apply (subgoal_tac "c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)) - zmset (map snd (consu os2)) = {#}\<^sub>z")
                          subgoal
                            apply (clarsimp simp del: zmset_of_replicate_mset)
                            using Suc_funpow numeral_nat(7) plus_1_eq_Suc apply presburger
                            done
                          subgoal premises prems6
                            using prems(1,2,5,9,10,11,12) prems2(3) apply -
                            unfolding max_from_caps_buf_def extract_progress_def
                            apply (auto simp add: zmultiset_move_add_other_side c_pts_change_multiplicities dest!: rmdups_NilD)
                            done
                          done
                        subgoal
                          by (simp add: prems6(1))
                        done
                      done
                    done
                  done
                apply (subgoal_tac "frontier
       (zmset_of
         (mset_set
           (set_antichain
             (frontier
               ({#n 0#}\<^sub>z +
                (zmset_of (Suc `# mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) - zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) +
                 update_zmultiset {#}\<^sub>z (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)) (- 1)))))) +
        zmset_of
         (mset_set
           (set_antichain
             (frontier
               (c_pts (pt_tr sg) (Loc 1 (Trg 1)) +
                (zmset (map snd (produ os1)) +
                 (Auxiliary.image_zmset (trivial_dataflow_topology_interpretation.followed_by (n 1)) (Auxiliary.image_zmset length (zmset_of (replicate_mset (length batch) zs))) +
                  (- zmset (map snd (consu os2)) - zmset_of {#t. x \<in># mset batch#})))))))) = {}\<^sub>A")
                defer
                subgoal
                  apply (simp add: update_zmultiset_one zmset_of_image_mset flip: add.assoc)
                  apply (subst (1 2) add_zmset_add_single)
                  apply (subgoal_tac "
Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) + {#trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)#}\<^sub>z) +
                {#n 1#}\<^sub>z =
Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                (zmset_of (mset_set {n 1..trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) +
                {#n 1#}\<^sub>z")
                  defer 
                  subgoal premises
                    apply (simp flip: atLeastLessThanSuc_atLeastAtMost)
                    apply (subst (1) atLeastLessThanSuc)
                    apply auto
                    done
                  subgoal
                    apply (simp only: )
                    apply (subgoal_tac "
Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                zmset_of (mset_set {n 1..trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) +
                {#n 1#}\<^sub>z =
{#}\<^sub>z")
                    defer
                    subgoal premises
                      by (simp only: zmset_of_Suc_minus_empty flip: zmset_of_image_mset)
                    apply simp
                    apply (subgoal_tac "
c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)) +
                Auxiliary.image_zmset (trivial_dataflow_topology_interpretation.followed_by (n 1)) (Auxiliary.image_zmset length (zmset_of (replicate_mset (length batch) zs))) +
                (- zmset (map snd (consu os2)) - zmset_of {#t. x \<in># mset batch#}) = {#}\<^sub>z")
                    subgoal
                      apply simp
                      done
                    subgoal premises prems5
                      using prems2(6) apply -
                      apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                      apply hypsubst_thin
                      apply (auto simp add: lshift_ltake_ldrop)
                      apply (drule sym[of "LCons (batch, t) xs''"])
                      apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                      apply hypsubst_thin
                      apply (subst (asm) (2) iterates)
                      apply auto
                      apply hypsubst_thin
                      subgoal premises prems6 for ys xs'
                        apply (auto simp flip: zmset_of_replicate_mset)
                        apply (subgoal_tac "min (length (list_of (ltake (enat (length ys)) (inps 1)))) (length ys) = length ys")
                        subgoal
                          apply (simp del: zmset_of_replicate_mset add: image_mset_const_eq)
                          apply (subgoal_tac "c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)) - zmset (map snd (consu os2)) = {#}\<^sub>z")
                          subgoal
                            apply (clarsimp simp del: zmset_of_replicate_mset)
                            using Suc_funpow numeral_nat(7) plus_1_eq_Suc apply presburger
                            done
                          subgoal premises prems6
                            using prems(1,2,5,9,10,11,12) prems2(3) apply -
                            unfolding max_from_caps_buf_def extract_progress_def
                            apply (auto simp add: zmultiset_move_add_other_side c_pts_change_multiplicities dest!: rmdups_NilD)
                            done
                          done
                        subgoal
                          by (simp add: prems6(1))
                        done
                      done
                    done
                  done
                subgoal  premises premsf2
                  apply (intro exI conjI[rotated])
                  apply (intro relcomppI)
                  apply (rule bisim_refl)
                  defer
                  apply (rule wbisim_refl)
                  apply (rule wstep_trans(1))
                  apply (rule relpowp_imp_rtranclp[where n="length zs + 1 + length batch + length batch + 1 + 1 + 1 + 1"])
                  apply (simp only: relpowp_add)
                  apply (intro relcomppI)
                  apply (rule step_tau_pow_dataflow_op)
                  apply (rule step_tau_pow_map_op)
                  apply (rule step_taus_L_pow_comp_op_steps_intro)
                  apply (rule step_tau_pow_map_op)
                  apply (rule step_pow_input_top_Tau[where p=1])
                  apply (simp add: defaults_num1_def)
                  defer
                  defer
                  apply (rule refl)+
                  apply (simp add: eq_OO)
                  apply (rule step_Tau_dataflow_op_Tau_intro)
                  apply (rule step_map_op)
                  apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                  apply (rule step_input_top_Tau_intro3[where p=1 and batch=batch and lxs="lmap fst xs''"])
                  apply simp
                  defer
                  apply (rule refl)+
                  apply (simp add: defaults_num1_def)
                  apply simp
                  apply (rule refl)+
                  apply simp
                  apply (rule step_tau_pow_dataflow_op)
                  apply (rule step_tau_pow_map_op)
                  apply (rule step_tau_Out_pow_comp_op_steps_intro[where xs="map Inr (map (\<lambda> x. (x, t)) batch)"])
                  apply (rule steps_map_op)
                  apply (rule refl)+
                  defer
                  apply (rule steps_input_top_Out[where p=1])
                  apply (simp add: defaults_num1_def)
                  apply (rule refl)+
                  apply simp
                  apply simp
                  apply (rule refl)+
                  apply (rule step_tau_pow_dataflow_op)
                  apply (rule step_tau_pow_map_op)
                  apply (rule step_tau_Inp_pow_comp_op_steps_intro[where xs="map Inr (map (\<lambda> x. (x, t)) batch)" ])
                  apply (rule steps_map_op)
                  apply (rule refl)+
                  defer
                  apply (rule steps_max_top'_Inp_Some_intro[where xs="map Inr (map (\<lambda> x. (x, t)) batch)"])
                  apply simp
                  apply (rule prod.collapse)
                  apply (rule refl)+
                  defer
                  defer
                  apply simp
                  defer
                  defer
                  apply (rule refl)+
                  apply (simp only: relpowp_1)
                  apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=0, rotated])
                  apply (rule refl)
                  apply (rule step_map_op)
                  apply (rule step_comp_op_L_Out)
                  apply (rule step_map_op)
                  apply (rule step_input_top_Out_None_intro[where p="1 :: 1"])
                  apply (rule refl)+
                  apply (simp add: defaults_num1_def)
                  apply simp
                  apply simp
                  apply (rule refl)+
                  apply simp
                  apply (simp only: relpowp_1)
                  apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=1, rotated])
                  apply (rule refl)
                  apply (rule step_map_op)
                  apply (rule step_comp_op_R_Out)
                  apply (rule step_map_op)
                  apply (rule step_max_top'_Out_None)
                  apply simp
                  apply (rule refl)+
                  apply simp
                  apply (rule refl)+
                  apply simp
                  apply (simp only: relpowp_1)
                  apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
                  apply (rule step_map_op)
                  apply (rule step_comp_op_R_Inp)
                  apply (rule step_map_op)
                  apply (rule step_max_top'Inp_None)
                  defer
                  defer
                  apply (rule refl)+
                  apply simp
                  apply simp
                  apply (rule refl)+
                  apply simp
                  apply (rule refl)+
                  apply (simp only: relpowp_1)
                  apply (rule step_Tau_dataflow_op_Tau_intro)
                  apply (rule step_map_op)
                  apply (rule step_comp_op_R_Tau)
                  apply (rule step_map_op)
                  apply (rule step_max_top'_Tau_output)
                  apply (rule refl)+
                  apply simp
                  apply (rule refl)+
                  apply simp
                  apply (rule step_Out_dataflow_op_Out_Inr_intro)
                  apply (rule step_map_op)
                  apply (rule step_comp_op_R_Out)
                  apply (rule step_map_op)
                  apply (rule step_max_top'_Out_intro[where xs=Nil])
                  apply (rule refl)+
                  defer
                  apply simp
                  apply (rule refl)+
                  apply simp
                  subgoal

(* here 2 *)

                    subgoal
                      unfolding propagate_invs_def[symmetric]
                      apply (subgoal_tac "propagate_invs my_summ
     (change_multiplicities my_summ
       (extract_progress 0 (\<lambda>l. if l = Loc 0 (Src 1) then [Loc 1 (Trg 1)] else [])
         \<lparr>cons =
            consu
             (produce (os1\<lparr>inter := operator_state.inter os1 @ concat (map (\<lambda>t'. [(1, t', - 1), (1, Suc t', 1)]) [n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)])\<rparr>)
               (Cap (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)) 1) batch),
            inte =
              operator_state.inter
               (produce (os1\<lparr>inter := operator_state.inter os1 @ concat (map (\<lambda>t'. [(1, t', - 1), (1, Suc t', 1)]) [n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)])\<rparr>)
                 (Cap (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)) 1) batch) @
              [(1, trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs), - 1), (1, Suc (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)), 1)],
            prod =
              produ
               (produce (os1\<lparr>inter := operator_state.inter os1 @ concat (map (\<lambda>t'. [(1, t', - 1), (1, Suc t', 1)]) [n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)])\<rparr>)
                 (Cap (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)) 1) batch)\<rparr> @
        extract_progress 1 (\<lambda>l. if l = Loc 0 (Src 1) then [Loc 1 (Trg 1)] else [])
         \<lparr>cons = consu os2 @ map (\<lambda>x. (1, t, 1)) batch, inte = operator_state.inter os2 @ map (\<lambda>t. (1, t, 1)) (rmdups (time ` set caps) (map (\<lambda>x. t) batch)),
            prod = produ (fold (\<lambda>t os. os\<lparr>consu := consu os @ [(1, t, 1)]\<rparr>) (map (\<lambda>x. t) batch) (os2\<lparr>inter := operator_state.inter os2 @ map (\<lambda>t. (1, t, 1)) (rmdups (time ` set caps) (map (\<lambda>x. t) batch))\<rparr>))\<rparr>)
       (pt_tr sg))")
                      defer
                      subgoal
                        unfolding propagate_invs_def
                        apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                        prefer 3
                        apply (rule refl)
                        subgoal
                          using prems(2,9,10,22,23) apply -
                          apply (auto 0 0 simp flip: add.assoc simp add: produce_def changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            apply (drule bspec)
                            by  (drule bspec) auto
                          subgoal
                            apply  (drule bspec)
                             apply blast
                            apply simp
                            done
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            apply  (drule bspec)
                             apply blast
                            apply simp
                            done
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            by  (drule bspec) auto
                          done

                        subgoal
                          apply safe
                          subgoal for l t' x
                            using prems(2,9,10,17,11,27,13,23,3,14) prems2(7) apply -
                            apply (drule spec[of _ l])
                            apply (auto 0 0 simp flip: add.assoc simp add: split_beta produce_def changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal premises prems3
                              using prems3(2,3,4,6,8) apply -
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (1) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  by (smt (verit, ccfv_SIG) dual_order.trans frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_singletons frontier_less_equal_iff frontier_less_equal_zcount_pos le_add1 prems3(6) zcount_zmset_of_nonneg zero_one)
                                subgoal
                                  using prems3(5,6) apply -
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  unfolding frontier_less_equal_iff[symmetric]
                                  unfolding frontier_less_equal_iff2
                                  using less_eq_antichain_def apply fastforce
                                  done
                                done
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              done

                            subgoal premises prems3
                              using prems3(2,3,4,6,8) apply -
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (1) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  by (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_singletons frontier_less_equal_iff frontier_less_equal_zcount_pos le_add1 le_add_same_cancel2 linordered_nonzero_semiring_class.zero_le_one
                                      order.trans plus_1_eq_Suc prems3(6) zero_one zmset_of_mset_set_ge_zero)
                                subgoal
                                  using prems3(5,6) apply -
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  unfolding frontier_less_equal_iff[symmetric]
                                  unfolding frontier_less_equal_iff2
                                  using less_eq_antichain_def apply fastforce
                                  done
                                done
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              done
                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  by (smt (z3) dataflow_topology_from_tree.obtain_frontier_elem frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_iff2 frontier_less_equal_trans loc_2_1_cases location.simps(1)
                                      port.simps(1,4) trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  unfolding frontier_less_equal_iff[symmetric]
                                  unfolding frontier_less_equal_iff2
                                  apply (smt (verit, del_insts) frontier_idempotent frontier_less_equal_addI frontier_less_equal_iff2 frontier_less_equal_le_trans frontier_less_equal_trans trivial_dataflow_topology_interpretation.le_plus(1)
                                      zmset_of_mset_set_ge_zero)
                                  done
                                done
                              done

                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  by (smt (verit, best) dataflow_topology_from_tree.obtain_frontier_elem frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_iff2 frontier_less_equal_trans mem_simps(3) prems(31)
                                      zmset_of_mset_set_ge_zero)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  done
                                done
                              done
                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  by (smt (z3) dataflow_topology_from_tree.obtain_frontier_elem frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_iff2 frontier_less_equal_trans loc_2_1_cases location.simps(1)
                                      port.simps(1,4) trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (meson basic_trans_rules(23) frontier_le_singletons)                       
                                  done
                                done
                              done


                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  by (smt (verit, del_insts) antichain_singletonD frontier_singleton le_trans less_eq_antichain_def loc_2_1_cases location.simps(1) nat_in_between_eq(2) nat_less_le port.simps(1,4)
                                      trivial_dataflow_topology_interpretation.obtain_frontier_elem)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (meson basic_trans_rules(23) frontier_le_singletons le_SucI)
                                  done
                                done
                              done


                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  by (smt (z3) Sup_empty Sup_empty dataflow_topology_from_tree.obtain_frontier_elem frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_iff2 frontier_less_equal_trans mem_simps(3)
                                      prems(31) zmset_of_mset_set_ge_zero)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)+
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (rule bexI)
                                  apply (rule refl)
                                  apply simp
                                  apply simp
                                  done
                                done
                              done



                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule disjI1)
                              apply (rule image_eqI)
                              apply (rule refl)
                              apply simp
                              apply simp
                              done

                            subgoal for t''
                              using prems2(6) apply -
                              apply (drule lzip_lshift_D)
                              apply clarsimp
                              apply (drule sym[of "LCons (batch, t) xs''"])
                              apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                              apply (subst (asm) (2) iterates.code)
                              apply auto
                              apply hypsubst_thin

                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  apply simp
                                  apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                      numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                  apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                  apply (simp add: frontier_le_remove_l)
                                  done
                                done
                              done

                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule image_eqI)
                              apply (rule refl)
                              apply simp
                              apply simp
                              done


                            subgoal for t''
                              using prems2(6) apply -
                              apply (drule lzip_lshift_D)
                              apply clarsimp
                              apply (drule sym[of "LCons (batch, t) xs''"])
                              apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                              apply (subst (asm) (2) iterates.code)
                              apply auto
                              apply hypsubst_thin

                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  apply simp
                                  apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                      numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                  apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                  apply (simp add: frontier_le_remove_l)
                                  done
                                done
                              done
                            done
                          done
                        done
                      apply (subgoal_tac "propagate_invs my_summ
     (change_multiplicities my_summ
       (extract_progress 0 (\<lambda>l. if l = Loc 0 (Src 1) then [Loc 1 (Trg 1)] else [])
         \<lparr>cons =
            consu
             (produce (os1\<lparr>inter := operator_state.inter os1 @ concat (map (\<lambda>t'. [(1, t', - 1), (1, Suc t', 1)]) [n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)])\<rparr>)
               (Cap (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)) 1) batch),
            inte =
              operator_state.inter
               (produce (os1\<lparr>inter := operator_state.inter os1 @ concat (map (\<lambda>t'. [(1, t', - 1), (1, Suc t', 1)]) [n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)])\<rparr>)
                 (Cap (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)) 1) batch) @
              [(1, trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs), - 1)],
            prod =
              produ
               (produce (os1\<lparr>inter := operator_state.inter os1 @ concat (map (\<lambda>t'. [(1, t', - 1), (1, Suc t', 1)]) [n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)])\<rparr>)
                 (Cap (trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)) 1) batch)\<rparr> @
        extract_progress 1 (\<lambda>l. if l = Loc 0 (Src 1) then [Loc 1 (Trg 1)] else [])
         \<lparr>cons = consu os2 @ map (\<lambda>x. (1, t, 1)) batch, inte = operator_state.inter os2 @ map (\<lambda>t. (1, t, 1)) (rmdups (time ` set caps) (map (\<lambda>x. t) batch)),
            prod = produ (fold (\<lambda>t os. os\<lparr>consu := consu os @ [(1, t, 1)]\<rparr>) (map (\<lambda>x. t) batch) (os2\<lparr>inter := operator_state.inter os2 @ map (\<lambda>t. (1, t, 1)) (rmdups (time ` set caps) (map (\<lambda>x. t) batch))\<rparr>))\<rparr>)
       (pt_tr sg))")
                      defer

                      subgoal premises
                        unfolding propagate_invs_def

                        apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                        prefer 3
                        apply (rule refl)
                        subgoal
                          using prems(2,9,10,22,23) apply -
                          apply (auto 0 0  simp flip: add.assoc simp add: produce_def changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            apply (drule bspec)
                            by  (drule bspec) auto
 subgoal
                            apply  (drule bspec)
                             apply blast
                            apply simp
                            done
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            by  (drule bspec) auto
 subgoal
                            apply  (drule bspec)
                             apply blast
                            apply simp
                            done
                          subgoal
                            by  (drule bspec) auto
                          subgoal
                            by  (drule bspec) auto
                          done

                        subgoal
                          apply safe
                          subgoal for l t' x
                            using prems(2,9,10,17,11,27,13,23,3,14) prems2(7) apply -
                            apply (drule spec[of _ l])
                            apply (auto 0 0 simp flip: add.assoc simp add: split_beta produce_def changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal premises prems3
                              using prems3(2,3,4,6,8) apply -
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (1) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  by (smt (verit, ccfv_SIG) dual_order.trans frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_singletons frontier_less_equal_iff frontier_less_equal_zcount_pos le_add1 prems3(6) zcount_zmset_of_nonneg zero_one)
                                subgoal
                                  using prems3(5,6) apply -
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  unfolding frontier_less_equal_iff[symmetric]
                                  unfolding frontier_less_equal_iff2
                                  using less_eq_antichain_def apply fastforce
                                  done
                                done
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              done

                            subgoal premises prems3
                              using prems3(2,3,4,6,8) apply -
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (1) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  by (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_singletons frontier_less_equal_iff frontier_less_equal_zcount_pos le_add1 le_add_same_cancel2 linordered_nonzero_semiring_class.zero_le_one
                                      order.trans plus_1_eq_Suc prems3(6) zero_one zmset_of_mset_set_ge_zero)
                                subgoal
                                  using prems3(5,6) apply -
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                  apply (metis frontier_le_singletons trivial_dataflow_topology_interpretation.le_plus(1))
                                  apply (simp add: frontier_le_remove_l)
                                  done
                                done
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              done

                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI1)
                              apply (rule image_eqI)
                              apply (rule refl)
                              apply simp
                              apply simp
                              done


                            subgoal
                              using prems2(6) apply -
                              apply (drule lzip_lshift_D)
                              apply clarsimp
                              apply (drule sym[of "LCons (batch, t) xs''"])
                              apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                              apply (subst (asm) (2) iterates.code)
                              apply auto
                              apply hypsubst_thin

                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  apply simp
                                  apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                      numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                  apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                  apply (simp add: frontier_le_remove_l)
                                  done
                                done
                              done


                            subgoal for t''
                              using prems2(6) apply -
                              apply (drule lzip_lshift_D)
                              apply clarsimp
                              apply (drule sym[of "LCons (batch, t) xs''"])
                              apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                              apply (subst (asm) (2) iterates.code)
                              apply auto
                              apply hypsubst_thin

                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  apply simp
                                  apply (metis (lifting) ext antichain_singletonD frontier_less_equal_iff2 frontier_less_equal_trans frontier_less_equal_zcount_pos frontier_singleton lessI less_eq_antichain_def nat_less_less_eq)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (meson basic_trans_rules(23) frontier_le_singletons le_Suc_eq)
                                  done
                                done
                              done

                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI1)
                              apply (rule bexI)
                              apply (rule refl)
                              apply simp
                              apply simp
                              done

                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule disjI1)
                              apply (rule image_eqI)
                              apply (rule refl)
                              apply simp
                              apply simp
                              done


                            subgoal for t''
                              using prems2(6) apply -
                              apply (drule lzip_lshift_D)
                              apply clarsimp
                              apply (drule sym[of "LCons (batch, t) xs''"])
                              apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                              apply (subst (asm) (2) iterates.code)
                              apply auto
                              apply hypsubst_thin

                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  apply simp
                                  apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                      numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                  apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                  apply (simp add: frontier_le_remove_l)
                                  done
                                done
                              done


                            subgoal 
                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule image_eqI)
                              apply (rule refl)
                              apply simp
                              apply simp
                              done

                            subgoal for t''
                              using prems2(6) apply -
                              apply (drule lzip_lshift_D)
                              apply clarsimp
                              apply (drule sym[of "LCons (batch, t) xs''"])
                              apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                              apply (subst (asm) (2) iterates.code)
                              apply auto
                              apply hypsubst_thin

                              apply (subst frontier_less_equal_iff2[symmetric]) 
                              unfolding frontier_less_equal_iff input_cap_def
                              apply (subst (asm) (2) if_not_P)
                              subgoal 
                                using prems2(6) 
                                by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  apply (rule order.trans)
                                  apply assumption
                                  apply simp
                                  apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                      numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI1)
                                  apply (rule image_eqI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                  apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                  apply (simp add: frontier_le_remove_l)
                                  done
                                done
                              done
                            done
                          done
                        done



                      subgoal premises premsf
                        (* start *)
                        unfolding R_def
                        apply simp
                        apply (subst (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40) fold_rmdups; simp?)
                        apply (tactic \<open>Tactic.distinct_subgoals_tac\<close>)
                        prefer 4

                        unfolding comp_def
                        apply simp
                        apply (subst (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20) propagate_all_frontier_c_imp_correctness_alt; simp?)
                        apply (simp_all add: prems(1,2,3) flip: change_multiplicities_append_alt)
                        apply simp_all
                        apply (tactic \<open>Tactic.distinct_subgoals_tac\<close>)


                        subgoal
                          using premsf(1) 
                          unfolding propagate_invs_def
                          by simp
                        subgoal
                          using premsf(2) 
                          unfolding propagate_invs_def
                          by simp
                        subgoal
                          apply safe
                          subgoal
                            apply (subgoal_tac "set caps = {}")
                            defer
                            subgoal
                              using prems(4) prems2(2) apply simp
                              using prems(5) prems2(3,6,7,8) apply -
                              unfolding comp_def produce_def max_from_caps_buf_def BENQ_def
                              apply (auto simp add: map_eq_Cons_conv comp_def lshift_ltake_ldrop dest!: rmdups_NilD)
                              done
                            subgoal
                              apply (subst (1 2 3 4 5 6) filter_True_False)
                              prefer 5
                              apply (subst (1 2) filter_False)
                              unfolding comp_def
                              apply (simp_all flip: change_multiplicities_append_alt)
                              apply simp_all
                              apply (tactic \<open>Tactic.distinct_subgoals_tac\<close>)
                              subgoal
                                (* here 4 *)
                                apply (intro impI)
                                using prems(1,2,3,9,10,11,12,14,13) prems2(1,2,3) apply -
                                apply (auto 0 0 simp add: zmset_map_snd_concat zmset_map_one_zmset_of zmset_map_minus_one_zmset_of produce_def dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
                                apply (simp flip: add.assoc)
                                apply (simp add: add.assoc)
                                unfolding input_cap_def
                                apply simp
                                apply (subst (asm) (2 3) if_not_P)
                                subgoal
                                  using prems2(6) by (metis llist.distinct(2) lshift.elims lzip_eq_LNil_conv)
                                subgoal
                                  using prems2(6) by (metis llist.distinct(2) lshift.elims lzip_eq_LNil_conv)
                                subgoal
                                  apply (simp add: update_zmultiset_one zmset_of_image_mset flip: add.assoc)
                                  apply (subst (asm) (1 2 3) add_zmset_add_single)
                                  apply (subgoal_tac "
Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) + {#trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)#}\<^sub>z) +
                {#n 1#}\<^sub>z =
Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                (zmset_of (mset_set {n 1..trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) +
                {#n 1#}\<^sub>z")
                                  defer 
                                  subgoal premises
                                    apply (simp flip: atLeastLessThanSuc_atLeastAtMost)
                                    apply (subst (1) atLeastLessThanSuc)
                                    apply auto
                                    done
                                  subgoal
                                    apply (simp only: )
                                    apply (subgoal_tac "
Auxiliary.image_zmset Suc (zmset_of (mset_set {n 1..<trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)})) -
                zmset_of (mset_set {n 1..trivial_dataflow_topology_interpretation.followed_by (n 1) (length zs)}) +
                {#n 1#}\<^sub>z =
{#}\<^sub>z")
                                    defer
                                    subgoal premises
                                      by (simp only: zmset_of_Suc_minus_empty flip: zmset_of_image_mset)
                                    apply simp
                                    apply (subgoal_tac "
c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)) +
                Auxiliary.image_zmset (trivial_dataflow_topology_interpretation.followed_by (n 1)) (Auxiliary.image_zmset length (zmset_of (replicate_mset (length batch) zs))) +
                (- zmset (map snd (consu os2)) - zmset_of {#t. x \<in># mset batch#}) = {#}\<^sub>z")
                                    subgoal
                                      apply simp
                                      unfolding frontier_less_equal_iff2
                                      using mem_antichain_nonempty apply blast
                                      done
                                    subgoal premises prems5
                                      using prems2(6) apply -
                                      apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                                      apply hypsubst_thin
                                      apply (auto simp add: lshift_ltake_ldrop)
                                      apply (drule sym[of "LCons (batch, t) xs''"])
                                      apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                                      apply hypsubst_thin
                                      apply (subst (asm) (2) iterates)
                                      apply auto
                                      apply hypsubst_thin
                                      subgoal premises prems6 for ys xs'
                                        apply (auto simp flip: zmset_of_replicate_mset)
                                        apply (subgoal_tac "min (length (list_of (ltake (enat (length ys)) (inps 1)))) (length ys) = length ys")
                                        subgoal
                                          apply (simp del: zmset_of_replicate_mset add: image_mset_const_eq)
                                          apply (subgoal_tac "c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (produ os1)) - zmset (map snd (consu os2)) = {#}\<^sub>z")
                                          subgoal
                                            apply (clarsimp simp del: zmset_of_replicate_mset)
                                            using Suc_funpow numeral_nat(7) plus_1_eq_Suc apply presburger
                                            done
                                          subgoal premises prems6
                                            using prems(1,2,5,9,10,11,12) prems2(3) apply -
                                            unfolding max_from_caps_buf_def extract_progress_def
                                            apply (auto simp add: zmultiset_move_add_other_side c_pts_change_multiplicities dest!: rmdups_NilD)
                                            done
                                          done
                                        subgoal
                                          by (simp add: prems6(1))
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal
                                apply (rule wb_upto_b_sym)
                                apply (rule wb_upto_b_base)
                                apply (intro conjI exI; (rule refl)?; (simp add: comp_def prems)?)
                                subgoal
                                  apply (rule arg_cong3[where f=map_op])
                                  apply (simp_all add: comp_def)
                                  apply (rule arg_cong[where f=source_op])
                                  apply (rule ext)+
                                  apply (clarsimp simp add: comp_def)
                                  subgoal premises prems3
                                    using prems(4,5,6) prems2(2,3) prems3(1) apply -
                                    apply (subst (1 2) drop_all)
                                    apply (simp_all add: BULK_BENQ_def)
                                    unfolding max_from_caps_buf_def
                                    apply (auto dest!: rmdups_NilD split: list.splits)
                                    apply (metis all_not_in_conv lmap_eq_LNil lset_LNil)
                                    done
                                  done
                                subgoal
                                  using prems(4,5,6) prems2(2,3) apply -
                                  unfolding max_from_caps_buf_def
                                  apply (auto simp add: BULK_BENQ_def comp_def dest!: rmdups_NilD)
                                  done
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12) prems2(2,3,6) apply -
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def
                                  apply (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                  apply hypsubst_thin
                                  apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                                  apply hypsubst_thin
                                  apply (auto simp add: lshift_ltake_ldrop)
                                  apply (drule sym[of "LCons (batch, t) xs''"])
                                  apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                                  apply hypsubst_thin
                                  apply (subst (asm) (2) iterates)
                                  apply auto
                                  apply (auto simp add: image_mset_const_eq Suc_funpow Groups.add_ac zmset_map_minus_one_zmset_of propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                  apply hypsubst_thin
                                  subgoal for ys xs'
                                    by (metis (no_types, lifting) Groups.add_ac(2) One_nat_def Suc_funpow arith_extra_simps(12) group_cancel.sub1 more_arith_simps(4) plus_1_eq_Suc uminus_add_conv_diff_mset)
                                  done
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12,13) prems2(2,3,6) apply -
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def input_cap_def
                                  apply (subst (asm) (2) if_not_P)
                                  subgoal 
                                    using prems2(6) 
                                    by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                  subgoal
                                    by (auto simp add: add_zmset_zmset_map_Suc_minus image_mset_const_eq update_zmultiset_one zmset_map_snd_concat propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: add.assoc zmset_of_replicate_mset dest!: rmdups_NilD split: if_splits)
                                  done
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12,14) prems2(2,3,6) 
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def
                                  by (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12,15) prems2(2,3,6) 
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def
                                  apply (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                  subgoal premises prems4
                                    apply (subgoal_tac "zmset (map (\<lambda>x. (x, 1)) (rmdups {} (map (\<lambda>x. t) batch))) + zmset (map (\<lambda>x :: (1, nat) capability. (time x, - 1)) (rmdups {} (map (\<lambda>x. Cap t 1) batch))) = {#}\<^sub>z")
                                    subgoal
                                      using prems4(9) by (simp add: add.assoc)
                                    subgoal
                                      apply (induct batch rule: rev_induct)
                                      apply auto
                                      apply (metis (mono_tags, lifting) more_arith_simps(9) neg_eq_iff_add_eq_0 update_zmultiset_singleton(1,2))
                                      done
                                    done
                                  done
                                subgoal
                                  apply (subst (1) propagate_all_frontier_c_imp_correctness_alt)
                                  apply simp_all
                                  using premsf(2) apply -
                                  unfolding propagate_invs_def
                                  apply simp
                                  done
                                subgoal
                                  apply safe
                                  subgoal for l
                                    apply (subst (1) propagate_all_frontier_c_imp_correctness_alt)
                                    apply simp_all
                                    subgoal
                                      using premsf(2) unfolding propagate_invs_def by simp
                                    subgoal
                                      unfolding dataflow_topology_implied_frontier_alt_my_summ
                                      by (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset)
                                    done
                                  done
                                subgoal
                                  apply safe
                                  subgoal for a t' x
                                    unfolding dataflow_topology_implied_frontier_alt_my_summ
                                    apply  (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset)
                                    subgoal
                                      apply (rule FalseE)
                                      using prems(1,2,3,4,5,6,9,10,11,12) prems2(2,3,6,7) 
                                      unfolding max_from_caps_buf_def  BENQ_def
                                      apply (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                      done
                                    subgoal
                                      using prems(5,1,2,9,10,11,13,14) prems2(7,3)  apply -
                                      unfolding produce_def input_cap_def
                                      apply (subst (asm) (2) if_not_P)
                                      subgoal 
                                        using prems2(6) 
                                        by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                      unfolding max_from_caps_buf_def extract_progress_def produce_def
                                      apply (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                      done
                                    done
                                  done
                                subgoal                        
                                  using propagate_all_preserves_inv[where summary=my_summ] apply -
                                  apply (drule meta_spec)+
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  apply simp
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (elim conjE)
                                  apply assumption
                                  apply simp
                                  using premsf(2) unfolding propagate_invs_def apply simp_all
                                  done
                                subgoal                        
                                  using propagate_all_preserves_inv[where summary=my_summ] apply -
                                  apply (drule meta_spec)+
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  apply simp
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (elim conjE)
                                  apply assumption
                                  apply simp
                                  using premsf(2) unfolding propagate_invs_def apply simp_all
                                  done
                                subgoal                        
                                  using propagate_all_preserves_inv[where summary=my_summ] apply -
                                  apply (drule meta_spec)+
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  apply simp
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (elim conjE)
                                  apply assumption
                                  apply simp
                                  using premsf(2) unfolding propagate_invs_def apply simp_all
                                  done
                                subgoal
                                  using prems(2,9,10,22) 
                                  unfolding extract_progress_def changes_non_zero_def
                                  by auto
                                subgoal
                                  using prems(5,1,2,9,10,11,15) prems2(7,3)  apply -
                                  unfolding changes_above_impl_def  dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt produce_def max_from_caps_buf_def
                                  apply  (auto 0 0 simp add: split_beta zmset_map_one_zmset_of zmset_map_minus_one_zmset_of zmset_map_snd_concat extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: add.assoc zmset_of_replicate_mset)

                                  apply hypsubst_thin
                                  apply (intro frontier_less_equal_addI)
                                  apply simp_all
                                  apply (rule disjI1)
                                  apply (intro frontier_less_equal_addI)
                                  apply simp_all
                                  apply (rule disjI2)
                                  subgoal premises prems6
                                    using prems6(5) apply -
                                    apply (induct batch)
                                    apply auto
                                    apply (metis add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_less_equal_iff union_add_left_zmset zcount_zmset_of_nonneg)
                                    done
                                  done
                                subgoal
                                  unfolding changes_above_impl_def  dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt produce_def
                                  by  (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset)
                                subgoal
                                  using prems(5,1,2,9,10,11,15) prems2(7,3)  apply -
                                  unfolding changes_above_impl_def  dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt produce_def max_from_caps_buf_def
                                  apply  (auto 0 0 simp add: split_beta zmset_map_one_zmset_of zmset_map_minus_one_zmset_of zmset_map_snd_concat extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: add.assoc zmset_of_replicate_mset)

                                  apply hypsubst_thin
                                  apply (intro frontier_less_equal_addI)
                                  apply simp_all
                                  apply (rule disjI1)
                                  apply (intro frontier_less_equal_addI)
                                  apply simp_all
                                  apply (rule disjI2)
                                  subgoal premises prems6
                                    using prems6(5) apply -
                                    apply (induct batch)
                                    apply auto
                                    apply (metis add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_less_equal_iff union_add_left_zmset zcount_zmset_of_nonneg)
                                    done
                                  done
                                subgoal
                                  by (auto simp add: zmset_map_minus_one_zmset_of)
                                subgoal
                                  using prems2(7) prems(2,8,9,10,11,15)  apply -
                                  unfolding    propagate_all_preserves_c_pts_alt produce_def
                                  apply simp
                                  apply  (auto simp add: zmset_map_one_zmset_of extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset)
                                  apply hypsubst_thin
                                  apply (smt (z3) add_cancel_right_right negative_zle zcount_union)
                                  done
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12) prems2(2,3,6) 
                                  unfolding max_from_caps_buf_def 
                                  by (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                subgoal
                                  using prems(30) apply -
                                  unfolding BENQ_def
                                  apply safe
                                  subgoal
                                    apply (rule fold_Cap_eq_Nil)
                                    apply simp_all
                                    apply blast
                                    done
                                  subgoal for t'
                                    apply (rule fold_Cap_eq_Nil)
                                    apply simp_all
                                    using prems(1,2,3,4,5,6,9,10,11,12) prems2(2,3,6,7) 
                                    unfolding max_from_caps_buf_def  BENQ_def
                                    apply (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                    subgoal for t''
                                      apply hypsubst_thin
                                      unfolding dataflow_topology_implied_frontier_alt_my_summ produce_def
                                      apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                                      apply hypsubst_thin
                                      apply (auto simp add: lshift_ltake_ldrop)
                                      apply (drule sym[of "LCons (batch, t') xs''"])
                                      apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                                      apply hypsubst_thin
                                      apply (subst (asm) (2) iterates)
                                      apply (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                      apply hypsubst_thin
                                      apply (metis One_nat_def funpow_Suc_conv nat_neq_iff plus_1_eq_Suc)
                                      done
                                    done
                                  done
                                subgoal
                                  unfolding BULK_BENQ_def
                                  apply (auto simp add: sorted_append)
                                  using prems(1,2,3,4,5,6,9,10,11,12,15) prems2(2,3,6) 
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def
                                  apply (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                  done
                                done
                              done
                            done
                          subgoal

                            apply (subgoal_tac "set caps = {}")
                            defer
                            subgoal
                              using prems(4) prems2(2) apply simp
                              using prems(5) prems2(3,6,7,8) apply -
                              unfolding comp_def produce_def max_from_caps_buf_def BENQ_def
                              apply (auto simp add: map_eq_Cons_conv comp_def lshift_ltake_ldrop dest!: rmdups_NilD)
                              done
                            subgoal
                              apply (subst (1 2 3 4 5 6) filter_True_False)
                              prefer 5
                              apply (subst (1 2) filter_False)
                              unfolding comp_def
                              apply (simp_all flip: change_multiplicities_append_alt)
                              apply simp_all
                              apply (tactic \<open>Tactic.distinct_subgoals_tac\<close>)
                              subgoal
                                (* here 4 *)
                                apply (intro impI)
                                using prems(1,2,3,9,10,11,12,14,13) prems2(1,2,3) apply -
                                apply (auto 0 0 simp add: zmset_map_snd_concat zmset_map_one_zmset_of zmset_map_minus_one_zmset_of produce_def dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
                                apply (simp flip: add.assoc)
                                apply (simp add: add.assoc)
                                unfolding input_cap_def
                                apply simp
                                apply (subst (asm) (2 3) if_not_P)
                                subgoal
                                  using prems2(6) by (metis llist.distinct(2) lshift.elims lzip_eq_LNil_conv)
                                subgoal
                                  using prems2(6) by (metis llist.distinct(2) lshift.elims lzip_eq_LNil_conv)
                                subgoal
                                  using premsf2(1) apply -
                                  apply auto
                                  using prems2(6) apply -
                                  apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                                  apply hypsubst_thin
                                  apply (auto simp add: lshift_ltake_ldrop)
                                  apply (drule sym[of "LCons (batch, t) xs''"])
                                  apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                                  apply hypsubst_thin
                                  apply (subst (asm) (2) iterates)
                                  unfolding frontier_less_equal_iff2
                                  apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                                  apply hypsubst_thin
                                  apply (metis One_nat_def Suc_n_not_le_n funpow_Suc_conv plus_1_eq_Suc)
                                  done
                                done
                              subgoal
                                apply (rule wb_upto_b_sym)
                                apply (rule wb_upto_b_base)
                                apply (intro conjI exI; (rule refl)?; (simp add: comp_def prems)?)
                                subgoal
                                  apply (rule arg_cong3[where f=map_op])
                                  apply (simp_all add: comp_def)
                                  apply (rule arg_cong[where f=source_op])
                                  apply (rule ext)+
                                  apply (clarsimp simp add: comp_def)
                                  subgoal premises prems3
                                    using prems(4,5,6) prems2(2,3,4,6) prems3(1) apply -
                                    apply (subst (1 2) drop_all)
                                    apply (simp_all add: BULK_BENQ_def)
                                    unfolding max_from_caps_buf_def
                                    apply (auto dest!: rmdups_NilD split: list.splits)



                                    apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                                    apply hypsubst_thin
                                    apply (auto simp add: lshift_ltake_ldrop)
                                    apply (drule sym[of "LCons (batch, t) xs''"])
                                    apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                                    apply hypsubst_thin
                                    apply (subst (asm) (2) iterates)
                                    apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                                    subgoal premises prems6 for ys xs'
                                      apply (rule arg_cong[where f="Coinductive_List_Auxiliary.lconcat"])
                                      apply (rule Coinductive_List.llist.map_cong)
                                      apply (auto simp add: ltake_all lmap_fst_lzip_conv_ltake)
                                      apply (rule arg_cong2[where f=lzip])
                                      apply auto
                                      using funpow_Suc_conv numeral_nat(7) plus_1_eq_Suc apply presburger
                                      done
                                    done
                                  done
                                subgoal
                                  using prems(4,5,6) prems2(2,3) apply -
                                  unfolding max_from_caps_buf_def
                                  apply (auto simp add: BULK_BENQ_def comp_def dest!: rmdups_NilD)
                                  done
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12) prems2(2,3,6) apply -
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def
                                  apply (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                  apply hypsubst_thin
                                  apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                                  apply hypsubst_thin
                                  apply (auto simp add: lshift_ltake_ldrop)
                                  apply (drule sym[of "LCons (batch, t) xs''"])
                                  apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                                  apply hypsubst_thin
                                  apply (subst (asm) (2) iterates)
                                  apply auto
                                  apply (auto simp add: image_mset_const_eq Suc_funpow Groups.add_ac zmset_map_minus_one_zmset_of propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                  apply hypsubst_thin
                                  subgoal for ys xs'
                                    by (metis (no_types, lifting) Groups.add_ac(2) One_nat_def Suc_funpow arith_extra_simps(12) group_cancel.sub1 more_arith_simps(4) plus_1_eq_Suc uminus_add_conv_diff_mset)
                                  done
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12,13) prems2(2,3,6) apply -
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def input_cap_def
                                  apply (subst (asm) (2) if_not_P)
                                  subgoal 
                                    using prems2(6) 
                                    by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                  subgoal
                                    by (auto simp add: add_zmset_zmset_map_Suc_minus image_mset_const_eq update_zmultiset_one zmset_map_snd_concat propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: add.assoc zmset_of_replicate_mset dest!: rmdups_NilD split: if_splits)
                                  done
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12,14) prems2(2,3,6) 
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def
                                  by (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12,15) prems2(2,3,6) 
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def
                                  apply (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                  subgoal premises prems4
                                    apply (subgoal_tac "zmset (map (\<lambda>x. (x, 1)) (rmdups {} (map (\<lambda>x. t) batch))) + zmset (map (\<lambda>x :: (1, nat) capability. (time x, - 1)) (rmdups {} (map (\<lambda>x. Cap t 1) batch))) = {#}\<^sub>z")
                                    subgoal
                                      using prems4(9) by (simp add: add.assoc)
                                    subgoal
                                      apply (induct batch rule: rev_induct)
                                      apply auto
                                      apply (metis (mono_tags, lifting) more_arith_simps(9) neg_eq_iff_add_eq_0 update_zmultiset_singleton(1,2))
                                      done
                                    done
                                  done
                                subgoal
                                  apply (subst (1) propagate_all_frontier_c_imp_correctness_alt)
                                  apply simp_all
                                  using premsf(1) apply -
                                  unfolding propagate_invs_def
                                  apply simp
                                  done
                                subgoal
                                  apply safe
                                  subgoal for l
                                    apply (subst (1) propagate_all_frontier_c_imp_correctness_alt)
                                    apply simp_all
                                    subgoal
                                      using premsf(1) unfolding propagate_invs_def by simp
                                    subgoal
                                      unfolding dataflow_topology_implied_frontier_alt_my_summ
                                      by (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset)
                                    done
                                  done
                                subgoal
                                  apply safe
                                  subgoal for a t' x
                                    unfolding dataflow_topology_implied_frontier_alt_my_summ
                                    apply  (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset)
                                    subgoal
                                      apply (rule FalseE)
                                      using prems(1,2,3,4,5,6,9,10,11,12) prems2(2,3,6,7) 
                                      unfolding max_from_caps_buf_def  BENQ_def
                                      apply (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                      done
                                    subgoal
                                      using prems(5,1,2,9,10,11,13,14) prems2(7,3)  apply -
                                      unfolding produce_def input_cap_def
                                      apply (subst (asm) (2) if_not_P)
                                      subgoal 
                                        using prems2(6) 
                                        by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                      unfolding max_from_caps_buf_def extract_progress_def produce_def
                                      apply (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                      done
                                    done
                                  done
                                subgoal                        
                                  using propagate_all_preserves_inv[where summary=my_summ] apply -
                                  apply (drule meta_spec)+
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  apply simp
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (elim conjE)
                                  apply assumption
                                  apply simp
                                  using premsf(1) unfolding propagate_invs_def apply simp_all
                                  done
                                subgoal                        
                                  using propagate_all_preserves_inv[where summary=my_summ] apply -
                                  apply (drule meta_spec)+
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  apply simp
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (elim conjE)
                                  apply assumption
                                  apply simp
                                  using premsf(1) unfolding propagate_invs_def apply simp_all
                                  done
                                subgoal                        
                                  using propagate_all_preserves_inv[where summary=my_summ] apply -
                                  apply (drule meta_spec)+
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  apply simp
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (drule meta_mp)
                                  defer
                                  apply (elim conjE)
                                  apply assumption
                                  apply simp
                                  using premsf(1) unfolding propagate_invs_def apply simp_all
                                  done
                                subgoal
                                  using prems(2,9,10,22) 
                                  unfolding extract_progress_def changes_non_zero_def
                                  by auto
                                subgoal
                                  using prems(5,1,2,9,10,11,15) prems2(7,3)  apply -
                                  unfolding changes_above_impl_def  dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt produce_def max_from_caps_buf_def
                                  apply  (auto 0 0 simp add: split_beta zmset_map_one_zmset_of zmset_map_minus_one_zmset_of zmset_map_snd_concat extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: add.assoc zmset_of_replicate_mset)

                                  apply hypsubst_thin
                                  apply (intro frontier_less_equal_addI)
                                  apply simp_all
                                  apply (rule disjI1)
                                  apply (intro frontier_less_equal_addI)
                                  apply simp_all
                                  apply (rule disjI2)
                                  subgoal premises prems6
                                    using prems6(5) apply -
                                    apply (induct batch)
                                    apply auto
                                    apply (metis add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_less_equal_iff union_add_left_zmset zcount_zmset_of_nonneg)
                                    done
                                  done
                                subgoal
                                  unfolding changes_above_impl_def  dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt produce_def
                                  by  (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset)
                                subgoal
                                  using prems(5,1,2,9,10,11,15) prems2(7,3)  apply -
                                  unfolding changes_above_impl_def  dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt produce_def max_from_caps_buf_def
                                  apply  (auto 0 0 simp add: split_beta zmset_map_one_zmset_of zmset_map_minus_one_zmset_of zmset_map_snd_concat extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: add.assoc zmset_of_replicate_mset)

                                  apply hypsubst_thin
                                  apply (intro frontier_less_equal_addI)
                                  apply simp_all
                                  apply (rule disjI1)
                                  apply (intro frontier_less_equal_addI)
                                  apply simp_all
                                  apply (rule disjI2)
                                  subgoal premises prems6
                                    using prems6(5) apply -
                                    apply (induct batch)
                                    apply auto
                                    apply (metis add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_less_equal_iff union_add_left_zmset zcount_zmset_of_nonneg)
                                    done
                                  done
                                subgoal
                                  by (auto simp add: zmset_map_minus_one_zmset_of)
                                subgoal
                                  using prems2(7) prems(2,8,9,10,11,15)  apply -
                                  unfolding    propagate_all_preserves_c_pts_alt produce_def
                                  apply simp
                                  apply  (auto simp add: zmset_map_one_zmset_of extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset)
                                  apply hypsubst_thin
                                  apply (smt (z3) add_cancel_right_right negative_zle zcount_union)
                                  done
                                subgoal
                                  using prems(1,2,3,4,5,6,9,10,11,12) prems2(2,3,6) 
                                  unfolding max_from_caps_buf_def 
                                  by (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                subgoal
                                  using prems(30) apply -
                                  unfolding BENQ_def
                                  apply safe
                                  subgoal
                                    apply (rule fold_Cap_eq_Nil)
                                    apply simp_all
                                    apply blast
                                    done
                                  subgoal for t'
                                    apply (rule fold_Cap_eq_Nil)
                                    apply simp_all
                                    using prems(1,2,3,4,5,6,9,10,11,12) prems2(2,3,6,7) 
                                    unfolding max_from_caps_buf_def  BENQ_def
                                    apply (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                    subgoal for t''
                                      apply hypsubst_thin
                                      unfolding dataflow_topology_implied_frontier_alt_my_summ produce_def
                                      apply (auto simp add: Suc_le_eq lzip_eq_LCons_conv dest!: lzip_lshift_D)
                                      apply hypsubst_thin
                                      apply (auto simp add: lshift_ltake_ldrop)
                                      apply (drule sym[of "LCons (batch, t') xs''"])
                                      apply (auto simp add: lzip_eq_LCons_conv ldrop_iterates dest!: lzip_lshift_D)
                                      apply hypsubst_thin
                                      apply (subst (asm) (2) iterates)
                                      apply (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                      apply hypsubst_thin
                                      apply (metis One_nat_def funpow_Suc_conv nat_neq_iff plus_1_eq_Suc)
                                      done
                                    done
                                  done
                                subgoal
                                  unfolding BULK_BENQ_def
                                  apply (auto simp add: sorted_append)
                                  using prems(1,2,3,4,5,6,9,10,11,12,15) prems2(2,3,6) 
                                  unfolding max_from_caps_buf_def extract_progress_def produce_def
                                  apply (auto simp add: propagate_all_preserves_c_pts_alt c_pts_change_multiplicities BULK_BENQ_def comp_def simp flip: zmset_of_replicate_mset dest!: rmdups_NilD)
                                  done
                                done
                              done
                            done
                          done
                        subgoal
                          using prems(7) by simp
                        subgoal
                          unfolding comp_def
                          by (induct batch) auto
                        subgoal
                          using prems(4) prems2(2) apply simp
                          using prems(5) prems2(3,6,7,8) apply -
                          unfolding comp_def produce_def max_from_caps_buf_def BENQ_def
                          apply (auto simp add: map_eq_Cons_conv comp_def lshift_ltake_ldrop dest!: rmdups_NilD)
                          done
                        done
                      done
                    done
                  apply simp_all
                  subgoal
                    using prems2(5,6) apply -
                    apply (drule lzip_lshift_D)
                    apply safe
                    apply (auto simp add: lnull_def)
                    done
                  subgoal
                    using prems2(5,6) apply -
                    apply (drule lzip_lshift_D)
                    apply safe
                    apply (auto simp add: split_beta lnull_def split: list.splits llist.splits)
                    apply (subst (asm) ltake_lshift)
                    apply (auto simp add: split_beta subset_eq image_iff llist_of_eq_LNil_conv  split: list.splits llist.splits)
                    apply (metis in_set_impl_in_set_zip1 list.exhaust split_pairs2)
                    done
                  subgoal
                    using prems2(5,6,7,8) apply -
                    apply (drule lzip_lshift_D)
                    apply (auto simp add: )
                    apply hypsubst_thin
                    apply (drule sym[of "LCons (batch, t) xs''"])
                    apply (auto simp add: lzip_eq_LCons_conv)
                    apply (subst ldropn_lshift)
                    apply simp_all
                    apply (subst lmap_fst_lzip_conv_ltake)
                    apply (subst ltake_all)
                    apply simp_all
                    apply (clarsimp simp add: lshift_ltake_ldrop)
                    subgoal for ys xs' ys'
                      apply (subgoal_tac "llength ys' = infinity")
                      apply simp_all
                      subgoal premises prems3
                        using prems3(7) by (metis enat.simps(2) gen_llength_code(2) gen_llength_def idiff_infinity llength_iterates llength_ldrop plus_eq_infty_iff_enat)
                      done
                    done
                  subgoal
                    using prems(5) prems2(3,6,7,8) apply -
                    unfolding comp_def produce_def max_from_caps_buf_def
                    apply (auto simp add: comp_def lshift_ltake_ldrop dest!: rmdups_NilD)
                    subgoal premises prems3
                      using prems3(6) apply -
                      apply (drule sym)
                      apply (clarsimp simp add: lzip_eq_LCons_conv ldrop_iterates)
                      apply (metis funpow_Suc_conv lhd_LCons lhd_iterates numeral_nat(7) plus_1_eq_Suc)
                      done
                    done
                  using prems(7) apply simp
                  subgoal
                    unfolding BULK_BENQ_def by auto
                  subgoal
                    using prems(5) prems2(3,6,7,8) apply -
                    unfolding comp_def produce_def max_from_caps_buf_def
                    by (auto simp add: comp_def lshift_ltake_ldrop dest!: rmdups_NilD)
                  subgoal
                    apply (subgoal_tac "set caps = {}")
                    defer
                    subgoal
                      using prems(4) prems2(2) apply simp
                      using prems(5) prems2(3,6,7,8) apply -
                      unfolding comp_def produce_def max_from_caps_buf_def BENQ_def
                      apply (auto simp add: map_eq_Cons_conv comp_def lshift_ltake_ldrop dest!: rmdups_NilD)
                      done
                    subgoal
                      apply (subst (1 2 3 4 5 6) fold_rmdups; simp?)
                      apply (tactic \<open>Tactic.distinct_subgoals_tac\<close>)
                      defer
                      subgoal
                        using prems(1,2) apply -
                        apply (simp add: comp_def flip: change_multiplicities_append_alt)
                        apply (subst (1 2) propagate_all_frontier_c_imp_correctness_alt)
                        apply simp_all
                        prefer 3
                        subgoal
                          apply (subst (1 2) filter_True; simp?)
                          prefer 3
                          subgoal
                            using prems(4) prems2(2) apply simp
                            using prems(5) prems2(3,6,7,8) apply -
                            unfolding comp_def produce_def max_from_caps_buf_def BENQ_def
                            apply (auto simp add: map_eq_Cons_conv comp_def lshift_ltake_ldrop dest!: rmdups_NilD)
                            apply hypsubst_thin
                            apply (rule exI[of _ "Cap _ _"])
                            apply simp
                            apply (intro conjI[rotated])
                            apply (rule refl)+
                            subgoal premises
                              apply (subgoal_tac "buf2 (Cap t 1) = []")
                              subgoal
                                apply (rule Max_eq_if)
                                apply auto
                                done
                              subgoal
                                using prems(30) apply -
                                apply (drule spec[of _ t])
                                apply (drule mp)
                                subgoal
                                  using prems2(6) apply -
                                  apply (auto simp add: lshift_ltake_ldrop)
                                  apply (drule sym)
                                  back
                                  apply (auto simp add: lzip_eq_LCons_conv)
                                  apply (metis basic_trans_rules(31) llist.set_intros(1) lset_iterates_Suc_ge' lset_ldrop_subset numeral_nat(7) plus_1_eq_Suc)
                                  done
                                apply simp
                                done
                              done
                            subgoal premises
                              using prems2(7) apply -
                              apply (induct batch)
                              apply auto
                              apply (metis Diff_empty empty_set list.map_disc_iff list.simps(15) rmdups_insert_NilI set_rmdups)
                              done
                            done
                          subgoal
                            (* here 4 *)
                            apply (intro impI)
                            using prems(1,2,3,9,10,11,12,14,13) prems2(1,2,3) apply -
                            apply (auto 0 0 simp add: zmset_map_snd_concat zmset_map_one_zmset_of zmset_map_minus_one_zmset_of produce_def dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
                            apply (simp flip: add.assoc)
                            apply (simp add: add.assoc)
                            unfolding input_cap_def
                            apply simp
                            apply (subst (asm) (2 3) if_not_P)
                            subgoal
                              using prems2(6) by (metis llist.distinct(2) lshift.elims lzip_eq_LNil_conv)
                            subgoal
                              using prems2(6) by (metis llist.distinct(2) lshift.elims lzip_eq_LNil_conv)
                            subgoal
                              using premsf2 apply -
                              apply simp
                              using prems2(6) apply -
                              apply (drule lzip_lshift_D)
                              apply clarsimp
                              apply (drule sym[of "LCons (batch, t) xs''"])
                              apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                              apply (subst (asm) (2) iterates.code)
                              unfolding frontier_less_equal_iff2
                              apply (auto simp add: frontier_singleton dest!: antichain_singletonD)
                              apply hypsubst_thin
                              apply (metis Suc_n_not_le_n funpow_Suc_conv numeral_nat(7) plus_1_eq_Suc)

                              done
                            done

                          subgoal
                            (* here 4 *)
                            apply (intro impI)
                            using prems(1,2,3,9,10,11,12,14,13) prems2(1,2,3) apply -
                            apply (auto 0 0 simp add: zmset_map_snd_concat zmset_map_one_zmset_of zmset_map_minus_one_zmset_of produce_def dataflow_topology_implied_frontier_alt_my_summ propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)
                            apply (simp flip: add.assoc)
                            apply (simp add: add.assoc)
                            unfolding input_cap_def
                            apply simp
                            apply (subst (asm) (2 3) if_not_P)
                            subgoal
                              using prems2(6) by (metis llist.distinct(2) lshift.elims lzip_eq_LNil_conv)
                            subgoal
                              using prems2(6) by (metis llist.distinct(2) lshift.elims lzip_eq_LNil_conv)
                            subgoal
                              using premsf2(2) apply -
                              apply simp

                              unfolding frontier_less_equal_iff2
                              using mem_antichain_nonempty apply blast
                              done

                            done
                          done
                        subgoal
                          apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                          prefer 3
                          apply (rule refl)
                          subgoal
                            using prems(2,9,10,22,23) apply -
                            apply (auto 0 0  simp flip: add.assoc simp add: produce_def changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              apply (drule bspec)
                              by  (drule bspec) auto
                            subgoal
                              apply  (drule bspec)
                               apply blast
                              apply simp
                              done
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              apply  (drule bspec)
                               apply blast
                              apply simp
                              done
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              by  (drule bspec) auto
                            done

                          subgoal
                            apply safe
                            subgoal for l t' x
                              using prems(2,9,10,17,11,27,13,23,3,14) prems2(7) apply -
                              apply (drule spec[of _ l])
                              apply (auto 0 0 simp flip: add.assoc simp add: split_beta produce_def changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal premises prems3
                                using prems3(2,3,4,6,9) apply -
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    by (smt (verit, ccfv_SIG) dual_order.trans frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_singletons frontier_less_equal_iff frontier_less_equal_zcount_pos le_add1 prems3(6) zcount_zmset_of_nonneg zero_one)
                                  subgoal
                                    using prems3(5,6) apply -
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    unfolding frontier_less_equal_iff[symmetric]
                                    unfolding frontier_less_equal_iff2
                                    using less_eq_antichain_def apply fastforce
                                    done
                                  done
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                done

                              subgoal premises prems3
                                using prems3(2,3,4,6,9) apply -
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    by (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_singletons frontier_less_equal_iff frontier_less_equal_zcount_pos le_add1 le_add_same_cancel2 linordered_nonzero_semiring_class.zero_le_one
                                        order.trans plus_1_eq_Suc prems3(6) zero_one zmset_of_mset_set_ge_zero)
                                  subgoal
                                    using prems3(5,6) apply -
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    unfolding frontier_less_equal_iff[symmetric]
                                    unfolding frontier_less_equal_iff2
                                    using less_eq_antichain_def apply fastforce
                                    done
                                  done
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                done
                              subgoal 
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    by (smt (z3) dataflow_topology_from_tree.obtain_frontier_elem frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_iff2 frontier_less_equal_trans loc_2_1_cases location.simps(1)
                                        port.simps(1,4) trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    unfolding frontier_less_equal_iff[symmetric]
                                    unfolding frontier_less_equal_iff2
                                    apply (smt (verit, del_insts) frontier_idempotent frontier_less_equal_addI frontier_less_equal_iff2 frontier_less_equal_le_trans frontier_less_equal_trans trivial_dataflow_topology_interpretation.le_plus(1)
                                        zmset_of_mset_set_ge_zero)
                                    done
                                  done
                                done

                              subgoal 
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    by (smt (verit, best) dataflow_topology_from_tree.obtain_frontier_elem frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_iff2 frontier_less_equal_trans mem_simps(3) prems(31)
                                        zmset_of_mset_set_ge_zero)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    done
                                  done
                                done
                              subgoal 
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    by (smt (z3) dataflow_topology_from_tree.obtain_frontier_elem frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_iff2 frontier_less_equal_trans loc_2_1_cases location.simps(1)
                                        port.simps(1,4) trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson basic_trans_rules(23) frontier_le_singletons)                       
                                    done
                                  done
                                done


                              subgoal 
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    by (smt (verit, del_insts) antichain_singletonD frontier_singleton le_trans less_eq_antichain_def loc_2_1_cases location.simps(1) nat_in_between_eq(2) nat_less_le port.simps(1,4)
                                        trivial_dataflow_topology_interpretation.obtain_frontier_elem)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson basic_trans_rules(23) frontier_le_singletons le_SucI)
                                    done
                                  done
                                done


                              subgoal 
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    by (smt (z3) Sup_empty Sup_empty dataflow_topology_from_tree.obtain_frontier_elem frontier_idempotent frontier_le_remove_l frontier_less_equal_iff frontier_less_equal_iff2 frontier_less_equal_trans mem_simps(3)
                                        prems(31) zmset_of_mset_set_ge_zero)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)+
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI2)
                                    apply (rule disjI1)
                                    apply (rule bexI)
                                    apply (rule refl)
                                    apply simp
                                    apply simp
                                    done
                                  done
                                done



                              subgoal 
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule disjI1)
                                apply (rule image_eqI)
                                apply (rule refl)
                                apply simp
                                apply simp
                                done

                              subgoal for t''
                                using prems2(6) apply -
                                apply (drule lzip_lshift_D)
                                apply clarsimp
                                apply (drule sym[of "LCons (batch, t) xs''"])
                                apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                                apply (subst (asm) (2) iterates.code)
                                apply auto
                                apply hypsubst_thin

                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    apply simp
                                    apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                        numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                    done
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (rule order.trans)
                                    apply assumption
                                    apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                    apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                    apply (simp add: frontier_le_remove_l)
                                    done
                                  done
                                done

                              subgoal 
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule image_eqI)
                                apply (rule refl)
                                apply simp
                                apply simp
                                done


                              subgoal for t''
                                using prems2(6) apply -
                                apply (drule lzip_lshift_D)
                                apply clarsimp
                                apply (drule sym[of "LCons (batch, t) xs''"])
                                apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                                apply (subst (asm) (2) iterates.code)
                                apply auto
                                apply hypsubst_thin

                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    apply simp
                                    apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                        numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                    done
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (rule order.trans)
                                    apply assumption
                                    apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                    apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                    apply (simp add: frontier_le_remove_l)
                                    done
                                  done
                                done
                              done
                            done
                          done

(* here <- *)


                        subgoal
                          apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                            prefer 3
                            apply (rule refl)
                          subgoal
                            using prems(2,9,10,22,23) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: produce_def changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal
                              by  (drule bspec) auto
                            subgoal

                              by  (drule bspec) auto
                            subgoal
                              apply  (drule bspec)
                               apply blast
                              apply simp
                              done
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              apply  (drule bspec)
                               apply blast
                              apply simp
                              done
                            subgoal
                              by  (drule bspec) auto
                            subgoal
                              by  (drule bspec) auto
                            done

                          subgoal
                            apply safe
                            subgoal for l t' x
                              using prems(2,9,10,17,11,27,13,23,3,14) prems2(7) apply -
                              apply (drule spec[of _ l])
                              apply (auto 0 0 simp flip: add.assoc simp add: split_beta produce_def changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal premises prems3
                                using prems3(2,3,4,6,9) apply -
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    by (smt (verit, ccfv_SIG) dual_order.trans frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_singletons frontier_less_equal_iff frontier_less_equal_zcount_pos le_add1 prems3(6) zcount_zmset_of_nonneg zero_one)
                                  subgoal
                                    using prems3(5,6) apply -
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    unfolding frontier_less_equal_iff[symmetric]
                                    unfolding frontier_less_equal_iff2
                                    using less_eq_antichain_def apply fastforce
                                    done
                                  done
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                done

                              subgoal premises prems3
                                using prems3(2,3,4,6,9) apply -
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    by (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_le_singletons frontier_less_equal_iff frontier_less_equal_zcount_pos le_add1 le_add_same_cancel2 linordered_nonzero_semiring_class.zero_le_one
                                        order.trans plus_1_eq_Suc prems3(6) zero_one zmset_of_mset_set_ge_zero)
                                  subgoal
                                    using prems3(5,6) apply -
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                    using frontier_le_singletons le_add1 apply blast            
                                    apply (metis (no_types, opaque_lifting) frontier_idempotent frontier_less_equal_addI frontier_less_equal_iff frontier_less_equal_le_trans zcount_zmset_of_nonneg)
                                    done
                                  done
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                done

                              subgoal 

                                apply (drule bspec)
                                apply simp
                                apply (rule disjI1)
                                apply (rule image_eqI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                unfolding frontier_less_equal_iff[symmetric]
                                unfolding frontier_less_equal_iff2
                                apply (smt (verit, del_insts) frontier_idempotent frontier_less_equal_addI frontier_less_equal_iff2 frontier_less_equal_le_trans frontier_less_equal_trans trivial_dataflow_topology_interpretation.le_plus(1)
                                    zmset_of_mset_set_ge_zero)
                                done

                              subgoal 
                                using prems2(6) apply -
                                apply (drule lzip_lshift_D)
                                apply clarsimp
                                apply (drule sym[of "LCons (batch, t) xs''"])
                                apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                                apply (subst (asm) (2) iterates.code)
                                apply auto
                                apply hypsubst_thin

                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    apply simp
                                    apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                        numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                    done
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (rule order.trans)
                                    apply assumption
                                    apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                    apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                    apply (simp add: frontier_le_remove_l)
                                    done
                                  done
                                done


                              subgoal 
                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    by (smt (verit, del_insts) antichain_singletonD frontier_singleton le_trans less_eq_antichain_def loc_2_1_cases location.simps(1) nat_in_between_eq(2) nat_less_le port.simps(1,4)
                                        trivial_dataflow_topology_interpretation.obtain_frontier_elem)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson basic_trans_rules(23) frontier_le_singletons le_SucI)
                                    done
                                  done
                                done


                              subgoal 

                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI1)
                                apply (rule bexI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                unfolding frontier_less_equal_iff[symmetric]
                                unfolding frontier_less_equal_iff2
                                apply (smt (verit, del_insts) frontier_idempotent frontier_less_equal_addI frontier_less_equal_iff2 frontier_less_equal_le_trans frontier_less_equal_trans trivial_dataflow_topology_interpretation.le_plus(1)
                                    zmset_of_mset_set_ge_zero)
                                done

                              subgoal 

                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule disjI1)
                                apply (rule image_eqI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                unfolding frontier_less_equal_iff[symmetric]
                                unfolding frontier_less_equal_iff2
                                apply (smt (verit, del_insts) frontier_idempotent frontier_less_equal_addI frontier_less_equal_iff2 frontier_less_equal_le_trans frontier_less_equal_trans trivial_dataflow_topology_interpretation.le_plus(1)
                                    zmset_of_mset_set_ge_zero)
                                done

                              subgoal 
                                using prems2(6) apply -
                                apply (drule lzip_lshift_D)
                                apply clarsimp
                                apply (drule sym[of "LCons (batch, t) xs''"])
                                apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                                apply (subst (asm) (2) iterates.code)
                                apply auto
                                apply hypsubst_thin

                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    apply simp
                                    apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                        numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                    done
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (rule order.trans)
                                    apply assumption
                                    apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                    apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                    apply (simp add: frontier_le_remove_l)
                                    done
                                  done
                                done

                              subgoal 

                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule image_eqI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                unfolding frontier_less_equal_iff[symmetric]
                                unfolding frontier_less_equal_iff2
                                apply (smt (verit, del_insts) frontier_idempotent frontier_less_equal_addI frontier_less_equal_iff2 frontier_less_equal_le_trans frontier_less_equal_trans trivial_dataflow_topology_interpretation.le_plus(1)
                                    zmset_of_mset_set_ge_zero)
                                done


                              subgoal 
                                using prems2(6) apply -
                                apply (drule lzip_lshift_D)
                                apply clarsimp
                                apply (drule sym[of "LCons (batch, t) xs''"])
                                apply (clarsimp simp add: lshift_ltake_ldrop lzip_eq_LCons_conv ldrop_iterates)
                                apply (subst (asm) (2) iterates.code)
                                apply auto
                                apply hypsubst_thin

                                apply (subst frontier_less_equal_iff2[symmetric]) 
                                unfolding frontier_less_equal_iff input_cap_def
                                apply (subst (asm) (2) if_not_P)
                                subgoal 
                                  using prems2(6) 
                                  by (metis LNil_eq_shift_iff llist.distinct(2) lzip_simps(1) zero_one)
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 0 (Src 1))) (n 0) > 0 \<or> zcount ( zmset (map snd (operator_state.inter os1))) (n 0) > 0")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_0 zcount_add_zmset zcount_union)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    apply (rule order.trans)
                                    apply assumption
                                    apply simp
                                    apply (smt (verit, ccfv_threshold) antichain_singletonD frontier_idempotent frontier_le_remove_l frontier_singleton funpow_Suc_conv in_frontier_iff le_trans less_eq_antichain_def
                                        numeral_nat(7) order_zmset_exists_foundation' plus_1_eq_Suc trivial_dataflow_topology_interpretation.le_plus(1) zmset_of_mset_set_ge_zero)
                                    done
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI1)
                                    apply (rule image_eqI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (rule order.trans)
                                    apply assumption
                                    apply (rule order.trans[rotated, of "frontier {#n 1#}\<^sub>z"])
                                    apply (metis One_nat_def Suc_funpow frontier_le_singletons le_add2 plus_1_eq_Suc)
                                    apply (simp add: frontier_le_remove_l)
                                    done
                                  done
                                done

                              done
                            done
                          done
                        done
                      subgoal premises
                        unfolding comp_def
                        apply simp
                        apply (induct batch)
                        apply auto
                        done
                      done
                    done
                  done
                done
              done

(* next case *)            

            subgoal for y ys'
              using prems(5) apply -
              apply clarsimp
              apply hypsubst_thin
              subgoal premises prems2
                apply (intro exI conjI[rotated])
                apply (intro relcomppI)
                apply (rule bisim_refl)
                defer
                apply (rule wbisim_refl)
                apply (rule wstep_trans(1))
                apply (rule relpowp_imp_rtranclp[where n="length (outpu os1 0) + length (buf1 (Inr (1, 1))) + length (outpu os1 0) + 1 + 1 + 1 + 1"]) 
                apply (simp only: relpowp_add)
                apply (intro relcomppI)
                apply (rule step_tau_pow_dataflow_op)
                apply simp
                apply (rule step_tau_pow_map_op)
                apply (rule step_tau_Out_pow_comp_op_steps_intro[where xs="map Inr (outpu os1 0)"])
                apply (rule steps_map_op)
                apply (rule refl)+
                defer
                apply (rule steps_input_top_Out[where p=1])
                apply (simp add: defaults_num1_def)
                apply (rule refl)+
                apply simp
                apply simp
                apply (rule refl)+                         
                apply (rule step_tau_pow_dataflow_op)
                apply (rule step_tau_pow_map_op)
                apply (rule step_tau_Inp_pow_comp_op_steps_intro[where xs="buf1 (Inr (1, 1))" ])
                apply (rule steps_map_op)
                apply (rule refl)+
                defer
                apply (rule steps_max_top'_Inp_Some_intro[where xs="buf1 (Inr (1, 0))"])
                using prems(6) apply simp
                defer
                apply (rule refl)+
                using prems(7) apply simp
                apply simp
                apply simp
                subgoal
                  by (auto simp add: BULK_BENQ_def)
                subgoal
                  by (auto simp add: BULK_BENQ_def)
                apply (rule refl)+
                apply (rule step_tau_pow_dataflow_op)
                apply (rule step_tau_pow_map_op)
                apply (rule step_tau_Inp_pow_comp_op_steps_intro[where xs="map Inr (outpu os1 1)"])
                apply (rule steps_map_op)
                apply (rule refl)+
                defer
                apply (rule steps_max_top'_Inp_Some_intro[where xs="map Inr (outpu os1 1)"])
                using prems(6) apply simp
                defer
                apply (rule refl)+
                defer
                apply simp
                apply simp
                subgoal
                  by (auto simp add: BULK_BENQ_def)
                subgoal
                  by (auto simp add: BULK_BENQ_def)
                apply (rule refl)+
                apply (simp add: eq_OO)
                apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=0, rotated])
                apply (rule refl)
                apply (rule step_map_op)
                apply (rule step_comp_op_L_Out)
                apply (rule step_map_op)
                apply (rule step_input_top_Out_None_intro[where p="1 :: 1"])
                apply (rule refl)+
                apply (simp add: defaults_num1_def)
                apply simp
                apply simp
                apply (rule refl)+
                apply simp
                apply (simp add: eq_OO)
                apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=1, rotated])
                apply (rule refl)
                apply (rule step_map_op)
                apply (rule step_comp_op_R_Out)
                apply (rule step_map_op)
                apply (rule step_max_top'_Out_None)
                apply simp
                apply (rule refl)+
                apply (simp_all add: eq_OO)
                apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
                apply (rule step_map_op)
                apply (rule step_comp_op_R_Inp)
                apply (rule step_map_op)
                apply (rule step_max_top'Inp_None)
                defer
                defer
                apply (rule refl)+
                apply simp_all
                apply simp
                apply (rule step_Tau_dataflow_op_Tau_intro)
                apply (rule step_map_op)
                apply (rule step_comp_op_R_Tau)
                apply (rule step_map_op)
                apply (rule step_max_top'_Tau_output)
                apply (rule refl)+
                apply simp
                apply (rule refl)+
                apply simp
                apply (rule step_Out_dataflow_op_Out_Inr_intro)
                apply (rule step_map_op)
                apply (rule step_comp_op_R_Out)
                apply (rule step_map_op)
                apply (rule step_max_top'_Out_intro)
                apply (rule refl)+
                apply (rule sym)
                defer
                apply simp
                apply (rule refl)+
                apply simp_all
                defer
                apply (rule prod.collapse)
                apply (rule prod.collapse)
                defer
                apply (clarsimp simp add: extract_progress_def comp_def)
                using prems(4) prems2(2) apply -
                apply simp
                apply (rule sym)
                apply (subst (1 2 3 4) fst_fold_rmdups)
                using prems apply simp
                subgoal
                  using prems(33) by (clarsimp simp add: sorted_append comp_def)
                subgoal
                  using prems(32) apply -
                  apply auto
                  apply (metis eq_snd_iff map_in_setD set_map)
                  done
                subgoal
                  using prems(7, 32, 33) apply -
                  apply (auto simp add: sorted_append comp_def)
                  apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                  done
                subgoal
                  using prems(33) by (clarsimp simp add: sorted_append comp_def)
                subgoal
                  using prems(7, 32, 33) apply -
                  apply (auto simp add: comp_def sorted_append)
                  apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                  done
                subgoal
                  using prems(7) by simp
                subgoal
                  using prems(33) by (clarsimp simp add: sorted_append comp_def)
                subgoal
                  using prems(32) apply -
                  apply auto
                  apply (metis eq_snd_iff map_in_setD set_map)
                  done
                apply (subst filter_True)
                prefer 2
                apply (subst prems2(4))
                subgoal
                  unfolding max_from_caps_buf_def BENQ_def BULK_BENQ_def list_to_buf_def
                  apply (rule map_cong)
                  apply (auto simp add: comp_def split_beta split: sum.splits)
                  subgoal
                    apply (rule arg_cong2[where f=rmdups])
                    apply auto
                    done
                  subgoal for x
                    apply (cases x; simp)
                    apply (rule Max_eq_if)
                    apply (auto simp add: image_iff)
                    done
                  subgoal for x
                    using prems(6) apply -
                    apply (cases x; simp)
                    apply force
                    apply (rule Max_eq_if)
                    apply (auto simp add: image_iff)
                    done
                  subgoal for a x
                    apply (rule Max_eq_if)
                    apply (auto simp add: image_iff)
                    done
                  done
                subgoal
                  using prems(1,2,3,6,14,9,10,11,13) prems(12)[symmetric] apply -
                  apply simp
                  apply (subst propagate_all_frontier_c_imp_correctness_alt)
                  apply simp_all
                  defer
                  subgoal
                    apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                    apply hypsubst_thin
                    apply (subgoal_tac 
                        "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                    subgoal
                      unfolding input_cap_def frontier_less_equal_iff2
                      using prems(28,29) apply -
                      apply clarsimp
                      apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                      using mem_antichain_nonempty apply blast
                      using mem_antichain_nonempty apply blast
                      using mem_antichain_nonempty apply blast
                      subgoal for x
                        apply (cases x; simp)
                        apply force
                        subgoal for b
                          apply (cases b; simp)
                          apply (drule spec2)
                          apply (elim conjE)
                          apply (drule mp)
                          apply (rule image_eqI[rotated])
                          apply auto
                          done
                        done
                      subgoal for a b
                        apply (drule spec2)
                        apply (elim conjE)
                        apply (drule mp)
                        back
                        apply auto
                        done
                      done
                    subgoal premises prems3
                      by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                    done
                  subgoal
                    apply hypsubst_thin
                    apply (simp flip: change_multiplicities_append_alt)
                    apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)]])
                    prefer 3
                    apply (rule refl)
                    subgoal
                      using prems(2,9,10,22,23) apply -
                      apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
 subgoal
                            apply  (drule bspec)
                             apply blast
                            apply simp
                            done
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      done
                    subgoal
                      apply safe
                      subgoal for l t x
                        using prems(2,9,10,17,23) apply -
                        apply (drule spec[of _ l])
                        apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal for x
                          apply (cases x; simp)
                          using prems(6) apply fastforce
                          apply hypsubst_thin
                          subgoal for p
                            apply (cases p)
                            apply simp
                            subgoal for n t
                              apply hypsubst_thin
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                              subgoal
                                apply (elim disjE)
                                subgoal
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (intro bexI conjI exI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                  done
                                done
                              subgoal premises prems2
                                using prems2(8,12) apply -
                                apply (simp add:  zmultiset_eq_iff)
                                apply (drule spec[of _ t])
                                apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                defer
                                subgoal premises
                                  using prems(8) apply -
                                  apply (induct "consu os2")
                                  apply auto
                                  apply (meson zcount_zmset_ge_zero)
                                  done
                                subgoal
                                  apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                  subgoal
                                    by linarith
                                  subgoal
                                    apply clarsimp
                                    apply (rule image_eqI[rotated])
                                    apply assumption
                                    apply auto
                                    done
                                  done
                                done
                              done
                            done
                          done
                        subgoal for p
                          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                          subgoal
                            apply (elim disjE)
                            subgoal
                              unfolding frontier_less_equal_iff2[symmetric]
                              unfolding frontier_less_equal_iff
                              by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                            subgoal
                              apply (drule zcount_gt_0_in_set_2)
                              apply (elim exE conjE)
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI1)
                              apply (intro bexI conjI exI)
                              apply (rule refl)+
                              apply assumption
                              apply simp
                              apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                              done
                            done
                          subgoal premises prems2
                            using prems2(8,12) apply -
                            apply (simp add:  zmultiset_eq_iff)
                            apply (drule spec[of _ t])
                            apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                            defer
                            subgoal premises
                              using prems(8) apply -
                              apply (induct "consu os2")
                              apply auto
                              apply (meson zcount_zmset_ge_zero)
                              done
                            subgoal
                              by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                            done
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal for x
                          apply (cases x; simp)
                          using prems(6) apply fastforce
                          apply hypsubst_thin
                          subgoal for p
                            apply (cases p)
                            apply simp
                            subgoal for n t
                              apply hypsubst_thin
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                              subgoal
                                apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    unfolding frontier_less_equal_iff2[symmetric]
                                    unfolding frontier_less_equal_iff
                                    apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                    by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI2)
                                    apply (rule disjI1)
                                    apply (intro bexI conjI exI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                    done
                                  done
                                done
                              subgoal premises prems2
                                using prems2(8,13) apply -
                                apply (simp add:  zmultiset_eq_iff)
                                apply (drule spec[of _ t])
                                apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                defer
                                subgoal premises
                                  using prems(8) apply -
                                  apply (induct "consu os2")
                                  apply auto
                                  apply (meson zcount_zmset_ge_zero)
                                  done
                                subgoal
                                  apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                  subgoal
                                    by linarith
                                  subgoal
                                    apply clarsimp
                                    apply (rule image_eqI[rotated])
                                    apply assumption
                                    apply auto
                                    done
                                  done
                                done
                              done
                            done
                          done
                        subgoal for p
                          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                          subgoal
                            subgoal
                              apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                              defer
                              subgoal
                                by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)

                              apply (elim disjE)
                              subgoal
                                unfolding frontier_less_equal_iff2[symmetric]
                                unfolding frontier_less_equal_iff
                                by (meson basic_trans_rules(23) frontier_less_equal_iff frontier_less_equal_zcount_pos)
                              subgoal
                                apply (drule zcount_gt_0_in_set_2)
                                apply (elim exE conjE)
                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI1)
                                apply (intro bexI conjI exI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                apply (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                done
                              done
                            done
                          subgoal premises prems2
                            using prems2(8,12) apply -
                            apply (simp add:  zmultiset_eq_iff)
                            apply (drule spec[of _ t])
                            apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                            defer
                            subgoal premises
                              using prems(8) apply -
                              apply (induct "consu os2")
                              apply auto
                              apply (meson zcount_zmset_ge_zero)
                              done
                            subgoal
                              by (smt (z3) count_mset_gt_0 img_snd less_numeral_extra(3) list.set_map mset_map not_int_zless_negative of_nat_le_0_iff prems2(13))
                            done
                          done
                        done
                      done
                    done
                  done
                subgoal
                  apply simp_all
                  unfolding R_def
                  apply (rule wb_upto_b_sym)
                  apply (rule wb_upto_b_base)
                  apply simp
                  apply (intro conjI exI; (rule refl)?; (simp add: comp_def prems)?)
                  subgoal
                    apply (rule arg_cong3[where f=map_op])
                    apply (simp_all add: comp_def)
                    apply (rule arg_cong[where f=source_op])
                    apply (rule ext)+
                    apply (clarsimp simp add: comp_def)
                    subgoal premises prems2
                      unfolding max_from_caps_buf_def
                      apply (subst (1 2) drop_all)
                      apply (simp_all add: BULK_BENQ_def)
                      apply (subst (1 2 3 4 5 6 7 8) fst_fold_rmdups)
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        apply (metis eq_snd_iff map_in_setD set_map)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        apply (metis eq_snd_iff map_in_setD set_map)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      apply (subst filter_False)
                      subgoal
                        using prems(1,2,3,6,14,9,10,11,13) prems(12)[symmetric] apply -
                        apply simp
                        apply (subst propagate_all_frontier_c_imp_correctness_alt)
                        apply simp_all
                        defer
                        subgoal
                          apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                          apply hypsubst_thin
                          apply (subgoal_tac 
                              "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                          subgoal
                            unfolding input_cap_def frontier_less_equal_iff2
                            using prems(28,29) apply -
                            apply clarsimp
                            apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            subgoal for x
                              apply (cases x; simp)
                              apply force
                              subgoal for b
                                apply (cases b; simp)
                                apply (drule spec2)
                                apply (elim conjE)
                                apply (drule mp)
                                apply (rule image_eqI[rotated])
                                apply auto
                                done
                              done
                            subgoal for a b
                              apply (drule spec2)
                              apply (elim conjE)
                              apply (drule mp)
                              back
                              apply auto
                              done
                            done
                          subgoal premises prems3
                            by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                          done
                        subgoal
                          apply hypsubst_thin
                          apply (simp flip: change_multiplicities_append_alt)
                          apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                          prefer 3
                          apply (rule refl)
                          subgoal
                            using prems(2,9,10,22,23) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                               apply fastforce+
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            done
                          subgoal
                            apply safe
                            subgoal for l t x
                              using prems(2,9,10,17,23) apply -
                              apply (drule spec[of _ l])
                              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (elim disjE)
                                      subgoal
                                        unfolding frontier_less_equal_iff2[symmetric]
                                        unfolding frontier_less_equal_iff
                                        by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                      subgoal
                                        apply (drule zcount_gt_0_in_set_2)
                                        apply (elim exE conjE)
                                        apply (drule bspec)
                                        apply simp
                                        apply (rule disjI2)
                                        apply (rule disjI1)
                                        apply (intro bexI conjI exI)
                                        apply (rule refl)+
                                        apply assumption
                                        apply simp
                                        apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                        done
                                      done
                                    subgoal premises prems2
                                      using prems2 apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) not_int_zless_negative)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    unfolding frontier_less_equal_iff2[symmetric]
                                    unfolding frontier_less_equal_iff
                                    by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI2)
                                    apply (rule disjI1)
                                    apply (intro bexI conjI exI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                    done
                                  done
                                subgoal apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal premises
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                                  done
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      defer
                                      subgoal
                                        by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)
                                      subgoal
                                        apply (elim disjE)
                                        subgoal
                                          unfolding frontier_less_equal_iff2[symmetric]
                                          unfolding frontier_less_equal_iff
                                          apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                          by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                        subgoal
                                          apply (drule zcount_gt_0_in_set_2)
                                          apply (elim exE conjE)
                                          apply (drule bspec)
                                          apply simp
                                          apply (rule disjI2)
                                          apply (rule disjI1)
                                          apply (intro bexI conjI exI)
                                          apply (rule refl)+
                                          apply assumption
                                          apply simp
                                          apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                          done
                                        done
                                      done
                                    subgoal apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) int_zle_neg)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  subgoal
                                    apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                    defer
                                    subgoal
                                      by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)

                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      by (meson basic_trans_rules(23) frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                      done
                                    done
                                  done
                                subgoal premises prems2
                                  using prems2(6,11) apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal 
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_mset_gt_0 less_numeral_extra(3) map_in_setD mset_map negative_zle of_nat_le_0_iff snd_conv)
                                  done
                                done
                              done
                            done
                          done

                        done
                      apply simp
                      done
                    done
                  apply (simp_all add: BULK_BENQ_def)
                  subgoal
                    apply (subst (1 2 3 4) fst_fold_rmdups)

                    using prems apply simp
                    subgoal
                      using prems(33) by (clarsimp simp add: sorted_append comp_def)
                    subgoal
                      using prems(32) apply -
                      apply auto
                      apply (metis eq_snd_iff map_in_setD set_map)
                      done
                    subgoal
                      using prems(7, 32, 33) apply -
                      apply (auto simp add: sorted_append comp_def)
                      apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                      done
                    subgoal
                      using prems(33) by (clarsimp simp add: sorted_append comp_def)
                    subgoal
                      using prems(7, 32, 33) apply -
                      apply (auto simp add: comp_def sorted_append)
                      apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                      done
                    subgoal
                      using prems(7) by simp
                    subgoal
                      using prems(33) by (clarsimp simp add: sorted_append comp_def)
                    subgoal
                      using prems(32) apply -
                      apply auto
                      apply (metis eq_snd_iff map_in_setD set_map)
                      done
                    using prems(7,32, 33) apply -
                    apply (auto simp add: comp_def sorted_append intro!: sorted_filter sorted_map_rmdups)
                    apply fastforce
                    apply (metis (no_types, opaque_lifting) imageI prod.sel(2) surj_pair)
                    done
                  subgoal premises prems2
                    using prems(1,2,9,10,11,12,13,14,15) apply -
                    apply (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)                  
                    apply (subst propagate_all_preserves_c_pts)
                    apply simp
                    apply (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)                  
                    done
                  subgoal premises prems2
                    using prems(1,2,9,10,11,12,13,14,15) apply -
                    apply (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)                  
                    apply (subst propagate_all_preserves_c_pts)
                    apply simp
                    apply (auto simp add: input_cap_def zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)                  
                    done
                  subgoal premises prems2
                    using prems(1,2,3,9,10,11,12,13,14,15,16) apply -
                    apply (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)                  
                    apply (subst propagate_all_preserves_c_pts)
                    apply simp
                    apply (auto simp add: input_cap_def zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits; hypsubst_thin?)                  
                    done
                  subgoal premises
                    using prems(1,2,3,9,10,11,15) apply -
                    apply (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits if_splits; hypsubst?)                  
                    apply (subst filter_mset_False_alt)
                    subgoal premises prems4
                      apply simp
                      apply (subst (1 2 3) fst_fold_rmdups)
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        apply (metis eq_snd_iff map_in_setD set_map)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        apply (simp flip: change_multiplicities_append_alt)
                        using prems(1,2,3,6,14,9,10,11,13) prems(12)[symmetric] apply -
                        apply simp
                        apply (subst propagate_all_frontier_c_imp_correctness_alt)
                        apply simp_all
                        defer
                        subgoal
                          apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                          apply hypsubst_thin
                          apply (subgoal_tac 
                              "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                          subgoal for x
                            apply (cases x; simp)
                            unfolding input_cap_def frontier_less_equal_iff2
                            using prems(28,29) apply -
                            apply clarsimp
                            apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            subgoal for x
                              apply (cases x; simp)
                              apply force
                              subgoal for b
                                apply (cases b; simp)
                                apply (drule spec2)
                                apply (elim conjE)
                                apply (drule mp)
                                apply (rule image_eqI[rotated])
                                apply auto
                                done
                              done
                            subgoal for a b
                              apply (drule spec2)
                              apply (elim conjE)
                              apply (drule mp)
                              back
                              apply auto
                              done
                            done
                          subgoal premises prems3
                            by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                          done

                        subgoal

                          apply hypsubst_thin
                          apply (simp flip: change_multiplicities_append_alt)
                          apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                          prefer 3
                          apply (rule refl)
                          subgoal
                            using prems(2,9,10,22,23) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply fastforce+
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            done
                          subgoal
                            apply safe
                            subgoal for l t x
                              using prems(2,9,10,17,23) apply -
                              apply (drule spec[of _ l])
                              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (elim disjE)
                                      subgoal
                                        unfolding frontier_less_equal_iff2[symmetric]
                                        unfolding frontier_less_equal_iff
                                        by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                      subgoal
                                        apply (drule zcount_gt_0_in_set_2)
                                        apply (elim exE conjE)
                                        apply (drule bspec)
                                        apply simp
                                        apply (rule disjI2)
                                        apply (rule disjI1)
                                        apply (intro bexI conjI exI)
                                        apply (rule refl)+
                                        apply assumption
                                        apply simp
                                        apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                        done
                                      done
                                    subgoal premises prems2
                                      using prems2 apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) not_int_zless_negative)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    unfolding frontier_less_equal_iff2[symmetric]
                                    unfolding frontier_less_equal_iff
                                    by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI2)
                                    apply (rule disjI1)
                                    apply (intro bexI conjI exI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                    done
                                  done
                                subgoal apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal premises
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                                  done
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      defer
                                      subgoal
                                        by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)
                                      subgoal
                                        apply (elim disjE)
                                        subgoal
                                          unfolding frontier_less_equal_iff2[symmetric]
                                          unfolding frontier_less_equal_iff
                                          apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                          by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                        subgoal
                                          apply (drule zcount_gt_0_in_set_2)
                                          apply (elim exE conjE)
                                          apply (drule bspec)
                                          apply simp
                                          apply (rule disjI2)
                                          apply (rule disjI1)
                                          apply (intro bexI conjI exI)
                                          apply (rule refl)+
                                          apply assumption
                                          apply simp
                                          apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                          done
                                        done
                                      done
                                    subgoal apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) int_zle_neg)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  subgoal
                                    apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                    defer
                                    subgoal
                                      by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)

                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      by (meson basic_trans_rules(23) frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                      done
                                    done
                                  done
                                subgoal premises prems2
                                  using prems2(6,11) apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal 
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_mset_gt_0 less_numeral_extra(3) map_in_setD mset_map negative_zle of_nat_le_0_iff snd_conv)
                                  done
                                done
                              done
                            done
                          done
                        done
                      done
                    subgoal
                      apply (subst filter_True)
                      subgoal premises prems4
                        apply (subst (1 2 3) fst_fold_rmdups)
                        using prems apply simp
                        subgoal
                          using prems(33) by (clarsimp simp add: sorted_append comp_def)
                        subgoal
                          using prems(32) apply -
                          apply auto
                          apply (metis eq_snd_iff map_in_setD set_map)
                          done
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: sorted_append comp_def)
                          done
                        subgoal
                          using prems(33) by (clarsimp simp add: sorted_append comp_def)
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: comp_def sorted_append)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: comp_def sorted_append)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: comp_def sorted_append)
                          done
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: sorted_append comp_def)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        subgoal
                          apply (simp flip: change_multiplicities_append_alt)
                          using prems(1,2,3,6,14,9,10,11,13) prems(12)[symmetric] apply -
                          apply simp
                          apply (subst propagate_all_frontier_c_imp_correctness_alt)
                          apply simp_all
                          defer
                          subgoal
                            apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                            apply hypsubst_thin
                            apply (subgoal_tac 
                                "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                            subgoal for x
                              apply (cases x; simp)
                              unfolding input_cap_def frontier_less_equal_iff2
                              using prems(28,29) apply -
                              apply clarsimp
                              apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                              using mem_antichain_nonempty apply blast
                              using mem_antichain_nonempty apply blast
                              using mem_antichain_nonempty apply blast
                              subgoal for x
                                apply (cases x; simp)
                                apply force
                                subgoal for b
                                  apply (cases b; simp)
                                  apply (drule spec2)
                                  apply (elim conjE)
                                  apply (drule mp)
                                  apply (rule image_eqI[rotated])
                                  apply auto
                                  done
                                done
                              subgoal for a b
                                apply (drule spec2)
                                apply (elim conjE)
                                apply (drule mp)
                                back
                                apply auto
                                done
                              done
                            subgoal premises prems3
                              by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                            done

                          subgoal

                            apply hypsubst_thin
                            apply (simp flip: change_multiplicities_append_alt)
                            apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                            prefer 3
                            apply (rule refl)
                            subgoal
                              using prems(2,9,10,22,23) apply -
                              apply (auto 0 0  simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal
                                apply (drule bspec)
                                apply auto
                                done
                              subgoal
                                apply (drule bspec)
                                apply fastforce+
                                done
                              subgoal
                                apply (drule bspec)
                                apply auto
                                done
                              subgoal
                                apply (drule bspec)
                                apply auto
                                done
                              done
                            subgoal
                              apply safe
                              subgoal for l t x
                                using prems(2,9,10,17,23) apply -
                                apply (drule spec[of _ l])
                                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                                subgoal
                                  apply (drule bspec)
                                  apply blast
                                  apply simp
                                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                  done
                                subgoal
                                  apply (drule bspec)
                                  apply blast
                                  apply simp
                                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                  done
                                subgoal
                                  apply (drule bspec)
                                  apply blast
                                  apply simp
                                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                  done
                                subgoal for x
                                  apply (cases x; simp)
                                  using prems(6) apply fastforce
                                  apply hypsubst_thin
                                  subgoal for p
                                    apply (cases p)
                                    apply simp
                                    subgoal for n t
                                      apply hypsubst_thin
                                      apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                      subgoal
                                        apply (elim disjE)
                                        subgoal
                                          unfolding frontier_less_equal_iff2[symmetric]
                                          unfolding frontier_less_equal_iff
                                          by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                        subgoal
                                          apply (drule zcount_gt_0_in_set_2)
                                          apply (elim exE conjE)
                                          apply (drule bspec)
                                          apply simp
                                          apply (rule disjI2)
                                          apply (rule disjI1)
                                          apply (intro bexI conjI exI)
                                          apply (rule refl)+
                                          apply assumption
                                          apply simp
                                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                          done
                                        done
                                      subgoal premises prems2
                                        using prems2 apply -
                                        apply (simp add:  zmultiset_eq_iff)
                                        apply (drule spec[of _ t])
                                        apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                        defer
                                        subgoal premises
                                          using prems(8) apply -
                                          apply (induct "consu os2")
                                          apply auto
                                          apply (meson zcount_zmset_ge_zero)
                                          done
                                        subgoal
                                          apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                          subgoal
                                            by (smt (z3) not_int_zless_negative)
                                          subgoal
                                            apply clarsimp
                                            apply (rule image_eqI[rotated])
                                            apply assumption
                                            apply auto
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                subgoal for p
                                  apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                  subgoal
                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                      done
                                    done
                                  subgoal apply -
                                    apply (simp add:  zmultiset_eq_iff)
                                    apply (drule spec[of _ t])
                                    apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                    defer
                                    subgoal premises
                                      using prems(8) apply -
                                      apply (induct "consu os2")
                                      apply auto
                                      apply (meson zcount_zmset_ge_zero)
                                      done
                                    subgoal
                                      by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                                    done
                                  done
                                subgoal
                                  apply (drule bspec)
                                  apply blast
                                  apply simp
                                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                  done
                                subgoal for x
                                  apply (cases x; simp)
                                  using prems(6) apply fastforce
                                  apply hypsubst_thin
                                  subgoal for p
                                    apply (cases p)
                                    apply simp
                                    subgoal for n t
                                      apply hypsubst_thin
                                      apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                      subgoal
                                        apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                        defer
                                        subgoal
                                          by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)
                                        subgoal
                                          apply (elim disjE)
                                          subgoal
                                            unfolding frontier_less_equal_iff2[symmetric]
                                            unfolding frontier_less_equal_iff
                                            apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                            by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                          subgoal
                                            apply (drule zcount_gt_0_in_set_2)
                                            apply (elim exE conjE)
                                            apply (drule bspec)
                                            apply simp
                                            apply (rule disjI2)
                                            apply (rule disjI1)
                                            apply (intro bexI conjI exI)
                                            apply (rule refl)+
                                            apply assumption
                                            apply simp
                                            apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                            done
                                          done
                                        done
                                      subgoal apply -
                                        apply (simp add:  zmultiset_eq_iff)
                                        apply (drule spec[of _ t])
                                        apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                        defer
                                        subgoal premises
                                          using prems(8) apply -
                                          apply (induct "consu os2")
                                          apply auto
                                          apply (meson zcount_zmset_ge_zero)
                                          done
                                        subgoal
                                          apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                          subgoal
                                            by (smt (z3) int_zle_neg)
                                          subgoal
                                            apply clarsimp
                                            apply (rule image_eqI[rotated])
                                            apply assumption
                                            apply auto
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                subgoal for p
                                  apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                  subgoal
                                    subgoal
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      defer
                                      subgoal
                                        by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)

                                      apply (elim disjE)
                                      subgoal
                                        unfolding frontier_less_equal_iff2[symmetric]
                                        unfolding frontier_less_equal_iff
                                        by (meson basic_trans_rules(23) frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                      subgoal
                                        apply (drule zcount_gt_0_in_set_2)
                                        apply (elim exE conjE)
                                        apply (drule bspec)
                                        apply simp
                                        apply (rule disjI2)
                                        apply (rule disjI1)
                                        apply (intro bexI conjI exI)
                                        apply (rule refl)+
                                        apply assumption
                                        apply simp
                                        apply (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                        done
                                      done
                                    done
                                  subgoal premises prems2
                                    using prems2(6,11) apply -
                                    apply (simp add:  zmultiset_eq_iff)
                                    apply (drule spec[of _ t])
                                    apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                    defer
                                    subgoal 
                                      using prems(8) apply -
                                      apply (induct "consu os2")
                                      apply auto
                                      apply (meson zcount_zmset_ge_zero)
                                      done
                                    subgoal
                                      by (smt (z3) count_mset_gt_0 less_numeral_extra(3) map_in_setD mset_map negative_zle of_nat_le_0_iff snd_conv)
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      subgoal
                        apply (auto simp add: comp_def)
                        apply (subst propagate_all_preserves_c_pts_alt)
                        apply hypsubst_thin
                        apply (auto simp add: propagate_pointstamps_def extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def dest!: propagate_all_preserves_c_pts split: option.splits if_splits; hypsubst?)                  
                        apply (subst zmset_map_minus_one_zmset_of)
                        apply (subst (1 2 3 4 5 6) fold_rmdups)
                        prefer 7
                        subgoal
                          apply (auto simp add:  comp_def simp flip: add.assoc)
                          apply (simp add: map_time_rmdups zmset_of_plus zmset_map_one_zmset_of flip: mset_map)
                          done
                        using prems apply simp
                        subgoal
                          using prems(33) by (clarsimp simp add: sorted_append comp_def)
                        subgoal
                          using prems(32) apply -
                          apply auto
                          subgoal for t x
                            apply (cases x; cases t; simp)
                            using prems(6) apply fastforce
                            using image_iff apply fastforce
                            done
                          done
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: sorted_append comp_def)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        subgoal
                          using prems(33) by (clarsimp simp add: sorted_append comp_def)
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: comp_def sorted_append)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        done
                      done
                    done
                  subgoal 
                    apply (subst propagate_all_frontier_c_imp_correctness_alt)
                    prefer 4
                    subgoal
                      by (auto simp add: dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt)
                    apply simp_all
                    subgoal
                      using prems(1,2,3,6,14,9,10,11,13) prems(12)[symmetric] apply -
                      apply simp

                      apply (simp flip: change_multiplicities_append_alt)
                      apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                      prefer 3
                      apply (rule refl)
                      subgoal
                        using prems(2,9,10,22,23) apply -
                        apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                        subgoal
                          apply (drule bspec)
                          apply auto
                          done
                        subgoal
                          apply (drule bspec)
                           apply fastforce+
                          done
                        subgoal
                          apply (drule bspec)
                           apply auto
                          done
      subgoal
                          apply (drule bspec)
                           apply auto
                          done
                        done
                      subgoal
                        apply safe
                        subgoal for l t x
                          using prems(2,9,10,17,23) apply -
                          apply (drule spec[of _ l])
                          apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                          subgoal
                            apply (drule bspec)
                            apply blast
                            apply simp
                            apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                            done
                          subgoal
                            apply (drule bspec)
                            apply blast
                            apply simp
                            apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                            done
                          subgoal
                            apply (drule bspec)
                            apply blast
                            apply simp
                            apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                            done
                          subgoal for x
                            apply (cases x; simp)
                            using prems(6) apply fastforce
                            apply hypsubst_thin
                            subgoal for p
                              apply (cases p)
                              apply simp
                              subgoal for n t
                                apply hypsubst_thin
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    unfolding frontier_less_equal_iff2[symmetric]
                                    unfolding frontier_less_equal_iff
                                    by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI2)
                                    apply (rule disjI1)
                                    apply (intro bexI conjI exI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                    done
                                  done
                                subgoal premises prems2
                                  using prems2 apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal premises
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                    subgoal
                                      by (smt (z3) not_int_zless_negative)
                                    subgoal
                                      apply clarsimp
                                      apply (rule image_eqI[rotated])
                                      apply assumption
                                      apply auto
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          subgoal for p
                            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                            subgoal
                              apply (elim disjE)
                              subgoal
                                unfolding frontier_less_equal_iff2[symmetric]
                                unfolding frontier_less_equal_iff
                                by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                              subgoal
                                apply (drule zcount_gt_0_in_set_2)
                                apply (elim exE conjE)
                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI1)
                                apply (intro bexI conjI exI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              done
                            subgoal apply -
                              apply (simp add:  zmultiset_eq_iff)
                              apply (drule spec[of _ t])
                              apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                              defer
                              subgoal premises
                                using prems(8) apply -
                                apply (induct "consu os2")
                                apply auto
                                apply (meson zcount_zmset_ge_zero)
                                done
                              subgoal
                                by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                              done
                            done
                          subgoal
                            apply (drule bspec)
                            apply blast
                            apply simp
                            apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                            done
                          subgoal for x
                            apply (cases x; simp)
                            using prems(6) apply fastforce
                            apply hypsubst_thin
                            subgoal for p
                              apply (cases p)
                              apply simp
                              subgoal for n t
                                apply hypsubst_thin
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                  defer
                                  subgoal
                                    by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)
                                  subgoal
                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                      done
                                    done
                                  done
                                subgoal apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal premises
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                    subgoal
                                      by (smt (z3) int_zle_neg)
                                    subgoal
                                      apply clarsimp
                                      apply (rule image_eqI[rotated])
                                      apply assumption
                                      apply auto
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          subgoal for p
                            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                            subgoal
                              subgoal
                                apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                defer
                                subgoal
                                  by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)

                                apply (elim disjE)
                                subgoal
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  by (meson basic_trans_rules(23) frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (intro bexI conjI exI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                  done
                                done
                              done
                            subgoal premises prems2
                              using prems2(8,13) apply -
                              apply (simp add:  zmultiset_eq_iff)
                              apply (drule spec[of _ t])
                              apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                              defer
                              subgoal 
                                using prems(8) apply -
                                apply (induct "consu os2")
                                apply auto
                                apply (meson zcount_zmset_ge_zero)
                                done
                              subgoal
                                by (smt (z3) count_mset_gt_0 less_numeral_extra(3) map_in_setD mset_map negative_zle of_nat_le_0_iff snd_conv)
                              done
                            done
                          done
                        done
                      done
                    done
                  subgoal premises
                    apply (auto simp add: comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt)
                    using  propagate_pointstamps_preserve_inv[unfolded propagate_pointstamps_def, where summary=my_summ, simplified, OF _   prems(19)[unfolded prems(1)] prems(20) prems(21)] apply -
                    apply (drule meta_spec)+
                    apply (drule meta_mp)
                    defer
                    apply (drule meta_mp)
                    defer
                    apply (drule meta_mp)
                    defer
                    apply (elim conjE)
                    apply assumption
                    apply simp
                    subgoal
                      using prems(2,9,10,22,23) apply -
                      apply (auto  simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      done

                    subgoal

                      apply safe
                      subgoal for l t x
                        using prems(2,9,10,17,23) apply -
                        apply (drule spec[of _ l])
                        apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal for x
                          apply (cases x; simp)
                          using prems(6) apply fastforce
                          apply hypsubst_thin
                          subgoal for p
                            apply (cases p)
                            apply simp
                            subgoal for n t
                              apply hypsubst_thin
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                              subgoal
                                apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                defer
                                subgoal premises
                                  by (simp add: frontier_le_remove_left)
                                apply (elim disjE)
                                subgoal
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (intro bexI conjI exI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                  done
                                done
                              subgoal 
                                using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                                apply (simp add:  zmultiset_eq_iff)
                                apply (drule spec[of _ t])
                                apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                defer
                                subgoal premises
                                  using prems(8) apply -
                                  apply (induct "consu os2")
                                  apply auto
                                  apply (meson zcount_zmset_ge_zero)
                                  done
                                subgoal
                                  apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                  subgoal
                                    by (smt (z3) not_int_zless_negative)
                                  subgoal
                                    apply clarsimp
                                    apply (rule image_eqI[rotated])
                                    apply assumption
                                    apply auto
                                    done
                                  done
                                done
                              done
                            done
                          done
                        subgoal for p
                          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                          subgoal
                            subgoal
                              apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                              defer
                              subgoal premises
                                by (simp add: frontier_le_remove_left)
                              apply (elim disjE)
                              subgoal
                                unfolding frontier_less_equal_iff2[symmetric]
                                unfolding frontier_less_equal_iff
                                by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                              subgoal
                                apply (drule zcount_gt_0_in_set_2)
                                apply (elim exE conjE)
                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule disjI1)
                                apply (intro bexI conjI exI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              done
                            done
                          subgoal 
                            using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (simp add:  zmultiset_eq_iff)
                            apply (drule spec[of _ t])
                            apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                            defer
                            subgoal premises
                              using prems(8) apply -
                              apply (induct "consu os2")
                              apply auto
                              apply (meson zcount_zmset_ge_zero)
                              done
                            subgoal
                              by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                            done
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal for p
                          apply (cases p; simp)
                          using prems(6) apply fastforce
                          subgoal for t'
                            apply hypsubst_thin
                            using prems(9,10,11,15) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (cases t'; simp)
                            subgoal for n t'
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t' > 0 \<or> zcount (zmset (map snd (produ os1))) t' > 0")
                              subgoal
                                apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))")
                                defer
                                subgoal premises
                                  by (simp add: frontier_le_remove_l frontier_le_remove_left)
                                apply (elim disjE)
                                subgoal
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule frontier_le_remove_left)
                                  apply simp_all
                                  apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (intro bexI conjI exI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (simp add: Groups.add_ac(2,3) frontier_le_remove_left)
                                  done
                                done
                              subgoal

                                using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                                apply (simp add:  zmultiset_eq_iff)
                                apply (drule spec[of _ t'])+
                                apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t' \<ge> 0")
                                defer
                                subgoal premises
                                  using prems(8) apply -
                                  apply (induct "consu os2")
                                  apply auto
                                  apply (meson zcount_zmset_ge_zero)
                                  done
                                subgoal
                                  apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t') > 0")
                                  subgoal
                                    by (smt (z3) not_int_zless_negative)
                                  subgoal
                                    apply clarsimp
                                    apply (rule image_eqI[rotated])
                                    apply assumption
                                    apply auto
                                    done
                                  done
                                done
                              done
                            done
                          done

                        subgoal for p

                          using prems(9,10,11,15) apply -
                          apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                          subgoal
                            apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))")
                            defer
                            subgoal premises
                              by (simp add: frontier_le_remove_l frontier_le_remove_left)
                            apply (elim disjE)
                            subgoal
                              unfolding frontier_less_equal_iff2[symmetric]
                              unfolding frontier_less_equal_iff
                              apply (rule order.trans)
                              apply assumption
                              apply (rule frontier_le_remove_left)
                              apply simp_all
                              apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                              done
                            subgoal
                              apply (drule zcount_gt_0_in_set_2)
                              apply (elim exE conjE)
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule disjI1)
                              apply (intro bexI conjI exI)
                              apply (rule refl)+
                              apply assumption
                              apply simp
                              unfolding frontier_less_equal_iff2[symmetric]
                              unfolding frontier_less_equal_iff
                              apply (rule order.trans)
                              apply assumption
                              apply (simp add: Groups.add_ac(2,3) frontier_le_remove_left)
                              done
                            done
                          subgoal

                            using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (simp add:  zmultiset_eq_iff)
                            apply (drule spec[of _ t])
                            apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                            defer
                            subgoal premises
                              using prems(8) apply -
                              apply (induct "consu os2")
                              apply auto
                              apply (meson zcount_zmset_ge_zero)
                              done
                            subgoal
                              by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                            done
                          done
                        done
                      done
                    done
                  subgoal premises
                    apply (auto simp add: comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt)
                    using  propagate_pointstamps_preserve_inv[unfolded propagate_pointstamps_def, where summary=my_summ, simplified, OF _   prems(19)[unfolded prems(1)] prems(20) prems(21)] apply -
                    apply (drule meta_spec)+
                    apply (drule meta_mp)
                    defer
                    apply (drule meta_mp)
                    defer
                    apply (drule meta_mp)
                    defer
                    apply (elim conjE)
                    apply assumption
                    apply simp
                    subgoal
                      using prems(2,9,10,22,23) apply -
                      apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
       subgoal
                        apply (drule bspec)
                        apply fastforce+
                        done
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      done

                    subgoal

                      apply safe
                      subgoal for l t x
                        using prems(2,9,10,17,23) apply -
                        apply (drule spec[of _ l])
                        apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal for x
                          apply (cases x; simp)
                          using prems(6) apply fastforce
                          apply hypsubst_thin
                          subgoal for p
                            apply (cases p)
                            apply simp
                            subgoal for n t
                              apply hypsubst_thin
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                              subgoal
                                apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                defer
                                subgoal premises
                                  by (simp add: frontier_le_remove_left)
                                apply (elim disjE)
                                subgoal
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (intro bexI conjI exI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                  done
                                done
                              subgoal 
                                using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                                apply (simp add:  zmultiset_eq_iff)
                                apply (drule spec[of _ t])
                                apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                defer
                                subgoal premises
                                  using prems(8) apply -
                                  apply (induct "consu os2")
                                  apply auto
                                  apply (meson zcount_zmset_ge_zero)
                                  done
                                subgoal
                                  apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                  subgoal
                                    by (smt (z3) not_int_zless_negative)
                                  subgoal
                                    apply clarsimp
                                    apply (rule image_eqI[rotated])
                                    apply assumption
                                    apply auto
                                    done
                                  done
                                done
                              done
                            done
                          done
                        subgoal for p
                          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                          subgoal
                            subgoal
                              apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                              defer
                              subgoal premises
                                by (simp add: frontier_le_remove_left)
                              apply (elim disjE)
                              subgoal
                                unfolding frontier_less_equal_iff2[symmetric]
                                unfolding frontier_less_equal_iff
                                by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                              subgoal
                                apply (drule zcount_gt_0_in_set_2)
                                apply (elim exE conjE)
                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule disjI1)
                                apply (intro bexI conjI exI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              done
                            done
                          subgoal 
                            using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (simp add:  zmultiset_eq_iff)
                            apply (drule spec[of _ t])
                            apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                            defer
                            subgoal premises
                              using prems(8) apply -
                              apply (induct "consu os2")
                              apply auto
                              apply (meson zcount_zmset_ge_zero)
                              done
                            subgoal
                              by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                            done
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal for p
                          apply (cases p; simp)
                          using prems(6) apply fastforce
                          subgoal for t'
                            apply hypsubst_thin
                            using prems(9,10,11,15) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (cases t'; simp)
                            subgoal for n t'
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t' > 0 \<or> zcount (zmset (map snd (produ os1))) t' > 0")
                              subgoal
                                apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))")
                                defer
                                subgoal premises
                                  by (simp add: frontier_le_remove_l frontier_le_remove_left)
                                apply (elim disjE)
                                subgoal
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule frontier_le_remove_left)
                                  apply simp_all
                                  apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (intro bexI conjI exI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (simp add: Groups.add_ac(2,3) frontier_le_remove_left)
                                  done
                                done
                              subgoal

                                using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                                apply (simp add:  zmultiset_eq_iff)
                                apply (drule spec[of _ t'])+
                                apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t' \<ge> 0")
                                defer
                                subgoal premises
                                  using prems(8) apply -
                                  apply (induct "consu os2")
                                  apply auto
                                  apply (meson zcount_zmset_ge_zero)
                                  done
                                subgoal
                                  apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t') > 0")
                                  subgoal
                                    by (smt (z3) not_int_zless_negative)
                                  subgoal
                                    apply clarsimp
                                    apply (rule image_eqI[rotated])
                                    apply assumption
                                    apply auto
                                    done
                                  done
                                done
                              done
                            done
                          done

                        subgoal for p

                          using prems(9,10,11,15) apply -
                          apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                          subgoal
                            apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))")
                            defer
                            subgoal premises
                              by (simp add: frontier_le_remove_l frontier_le_remove_left)
                            apply (elim disjE)
                            subgoal
                              unfolding frontier_less_equal_iff2[symmetric]
                              unfolding frontier_less_equal_iff
                              apply (rule order.trans)
                              apply assumption
                              apply (rule frontier_le_remove_left)
                              apply simp_all
                              apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                              done
                            subgoal
                              apply (drule zcount_gt_0_in_set_2)
                              apply (elim exE conjE)
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule disjI1)
                              apply (intro bexI conjI exI)
                              apply (rule refl)+
                              apply assumption
                              apply simp
                              unfolding frontier_less_equal_iff2[symmetric]
                              unfolding frontier_less_equal_iff
                              apply (rule order.trans)
                              apply assumption
                              apply (simp add: Groups.add_ac(2,3) frontier_le_remove_left)
                              done
                            done
                          subgoal

                            using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (simp add:  zmultiset_eq_iff)
                            apply (drule spec[of _ t])
                            apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                            defer
                            subgoal premises
                              using prems(8) apply -
                              apply (induct "consu os2")
                              apply auto
                              apply (meson zcount_zmset_ge_zero)
                              done
                            subgoal
                              by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                            done
                          done
                        done
                      done
                    done
                  subgoal premises
                    apply (auto simp add: comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt)
                    using  propagate_pointstamps_preserve_inv[unfolded propagate_pointstamps_def, where summary=my_summ, simplified, OF _   prems(19)[unfolded prems(1)] prems(20) prems(21)] apply -
                    apply (drule meta_spec)+
                    apply (drule meta_mp)
                    defer
                    apply (drule meta_mp)
                    defer
                    apply (drule meta_mp)
                    defer
                    apply (elim conjE)
                    apply assumption
                    apply simp
                    subgoal
                      using prems(2,9,10,22,23) apply -
                      apply (auto  simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      subgoal
                        apply (drule bspec)
                        apply auto
                        done
                      done

                    subgoal

                      apply safe
                      subgoal for l t x
                        using prems(2,9,10,17,23) apply -
                        apply (drule spec[of _ l])
                        apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal for x
                          apply (cases x; simp)
                          using prems(6) apply fastforce
                          apply hypsubst_thin
                          subgoal for p
                            apply (cases p)
                            apply simp
                            subgoal for n t
                              apply hypsubst_thin
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                              subgoal
                                apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                defer
                                subgoal premises
                                  by (simp add: frontier_le_remove_left)
                                apply (elim disjE)
                                subgoal
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (intro bexI conjI exI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                  done
                                done
                              subgoal 
                                using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                                apply (simp add:  zmultiset_eq_iff)
                                apply (drule spec[of _ t])
                                apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                defer
                                subgoal premises
                                  using prems(8) apply -
                                  apply (induct "consu os2")
                                  apply auto
                                  apply (meson zcount_zmset_ge_zero)
                                  done
                                subgoal
                                  apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                  subgoal
                                    by (smt (z3) not_int_zless_negative)
                                  subgoal
                                    apply clarsimp
                                    apply (rule image_eqI[rotated])
                                    apply assumption
                                    apply auto
                                    done
                                  done
                                done
                              done
                            done
                          done
                        subgoal for p
                          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                          subgoal
                            subgoal
                              apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Trg 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                              defer
                              subgoal premises
                                by (simp add: frontier_le_remove_left)
                              apply (elim disjE)
                              subgoal
                                unfolding frontier_less_equal_iff2[symmetric]
                                unfolding frontier_less_equal_iff
                                by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                              subgoal
                                apply (drule zcount_gt_0_in_set_2)
                                apply (elim exE conjE)
                                apply (drule bspec)
                                apply simp
                                apply (rule disjI2)
                                apply (rule disjI2)
                                apply (rule disjI1)
                                apply (intro bexI conjI exI)
                                apply (rule refl)+
                                apply assumption
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              done
                            done
                          subgoal 
                            using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (simp add:  zmultiset_eq_iff)
                            apply (drule spec[of _ t])
                            apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                            defer
                            subgoal premises
                              using prems(8) apply -
                              apply (induct "consu os2")
                              apply auto
                              apply (meson zcount_zmset_ge_zero)
                              done
                            subgoal
                              by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                            done
                          done
                        subgoal
                          apply (drule bspec)
                          apply blast
                          apply simp
                          apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                          done
                        subgoal for p
                          apply (cases p; simp)
                          using prems(6) apply fastforce
                          subgoal for t'
                            apply hypsubst_thin
                            using prems(9,10,11,15) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (cases t'; simp)
                            subgoal for n t'
                              apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t' > 0 \<or> zcount (zmset (map snd (produ os1))) t' > 0")
                              subgoal
                                apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))")
                                defer
                                subgoal premises
                                  by (simp add: frontier_le_remove_l frontier_le_remove_left)
                                apply (elim disjE)
                                subgoal
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (rule frontier_le_remove_left)
                                  apply simp_all
                                  apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                  done
                                subgoal
                                  apply (drule zcount_gt_0_in_set_2)
                                  apply (elim exE conjE)
                                  apply (drule bspec)
                                  apply simp
                                  apply (rule disjI2)
                                  apply (rule disjI2)
                                  apply (rule disjI1)
                                  apply (intro bexI conjI exI)
                                  apply (rule refl)+
                                  apply assumption
                                  apply simp
                                  unfolding frontier_less_equal_iff2[symmetric]
                                  unfolding frontier_less_equal_iff
                                  apply (rule order.trans)
                                  apply assumption
                                  apply (simp add: Groups.add_ac(2,3) frontier_le_remove_left)
                                  done
                                done
                              subgoal

                                using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                                apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                                apply (simp add:  zmultiset_eq_iff)
                                apply (drule spec[of _ t'])+
                                apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t' \<ge> 0")
                                defer
                                subgoal premises
                                  using prems(8) apply -
                                  apply (induct "consu os2")
                                  apply auto
                                  apply (meson zcount_zmset_ge_zero)
                                  done
                                subgoal
                                  apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t') > 0")
                                  subgoal
                                    by (smt (z3) not_int_zless_negative)
                                  subgoal
                                    apply clarsimp
                                    apply (rule image_eqI[rotated])
                                    apply assumption
                                    apply auto
                                    done
                                  done
                                done
                              done
                            done
                          done

                        subgoal for p

                          using prems(9,10,11,15) apply -
                          apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                          subgoal
                            apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))")
                            defer
                            subgoal premises
                              by (simp add: frontier_le_remove_l frontier_le_remove_left)
                            apply (elim disjE)
                            subgoal
                              unfolding frontier_less_equal_iff2[symmetric]
                              unfolding frontier_less_equal_iff
                              apply (rule order.trans)
                              apply assumption
                              apply (rule frontier_le_remove_left)
                              apply simp_all
                              apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                              done
                            subgoal
                              apply (drule zcount_gt_0_in_set_2)
                              apply (elim exE conjE)
                              apply (drule bspec)
                              apply simp
                              apply (rule disjI2)
                              apply (rule disjI2)
                              apply (rule disjI1)
                              apply (intro bexI conjI exI)
                              apply (rule refl)+
                              apply assumption
                              apply simp
                              unfolding frontier_less_equal_iff2[symmetric]
                              unfolding frontier_less_equal_iff
                              apply (rule order.trans)
                              apply assumption
                              apply (simp add: Groups.add_ac(2,3) frontier_le_remove_left)
                              done
                            done
                          subgoal

                            using prems(1,2,3,6,14,9,10,11) prems(12)[symmetric] apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            apply (simp add:  zmultiset_eq_iff)
                            apply (drule spec[of _ t])
                            apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                            defer
                            subgoal premises
                              using prems(8) apply -
                              apply (induct "consu os2")
                              apply auto
                              apply (meson zcount_zmset_ge_zero)
                              done
                            subgoal
                              by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                            done
                          done
                        done
                      done
                    done
                  subgoal premises
                    unfolding extract_progress_def comp_def
                    apply simp
                    apply (subst (1 2) filter_True)
                    subgoal premises prems4
                      apply (subst (1 2 3) fst_fold_rmdups)
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        apply (metis eq_snd_iff map_in_setD set_map)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        apply (simp flip: change_multiplicities_append_alt)
                        using prems(1,2,3,6,14,9,10,11,13) prems(12)[symmetric] apply -
                        apply simp
                        apply (subst propagate_all_frontier_c_imp_correctness_alt)
                        apply simp_all
                        defer
                        subgoal
                          apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                          apply hypsubst_thin
                          apply (subgoal_tac 
                              "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                          subgoal for x
                            apply (cases x; simp)
                            unfolding input_cap_def frontier_less_equal_iff2
                            using prems(28,29) apply -
                            apply clarsimp
                            apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            subgoal for x
                              apply (cases x; simp)
                              apply force
                              subgoal for b
                                apply (cases b; simp)
                                apply (drule spec2)
                                apply (elim conjE)
                                apply (drule mp)
                                apply (rule image_eqI[rotated])
                                apply auto
                                done
                              done
                            subgoal for a b
                              apply (drule spec2)
                              apply (elim conjE)
                              apply (drule mp)
                              back
                              apply auto
                              done
                            done
                          subgoal premises prems3
                            by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                          done

                        subgoal

                          apply hypsubst_thin
                          apply (simp flip: change_multiplicities_append_alt)
                          apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                          prefer 3
                          apply (rule refl)
                          subgoal
                            using prems(2,9,10,22,23) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal
                              apply (drule bspec)
                               apply auto
                              done
                            subgoal
                              apply (drule bspec)
                               apply fastforce+
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            done
                          subgoal
                            apply safe
                            subgoal for l t x
                              using prems(2,9,10,17,23) apply -
                              apply (drule spec[of _ l])
                              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (elim disjE)
                                      subgoal
                                        unfolding frontier_less_equal_iff2[symmetric]
                                        unfolding frontier_less_equal_iff
                                        by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                      subgoal
                                        apply (drule zcount_gt_0_in_set_2)
                                        apply (elim exE conjE)
                                        apply (drule bspec)
                                        apply simp
                                        apply (rule disjI2)
                                        apply (rule disjI1)
                                        apply (intro bexI conjI exI)
                                        apply (rule refl)+
                                        apply assumption
                                        apply simp
                                        apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                        done
                                      done
                                    subgoal premises prems2
                                      using prems2 apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) not_int_zless_negative)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    unfolding frontier_less_equal_iff2[symmetric]
                                    unfolding frontier_less_equal_iff
                                    by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI2)
                                    apply (rule disjI1)
                                    apply (intro bexI conjI exI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                    done
                                  done
                                subgoal apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal premises
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                                  done
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      defer
                                      subgoal
                                        by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)
                                      subgoal
                                        apply (elim disjE)
                                        subgoal
                                          unfolding frontier_less_equal_iff2[symmetric]
                                          unfolding frontier_less_equal_iff
                                          apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                          by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                        subgoal
                                          apply (drule zcount_gt_0_in_set_2)
                                          apply (elim exE conjE)
                                          apply (drule bspec)
                                          apply simp
                                          apply (rule disjI2)
                                          apply (rule disjI1)
                                          apply (intro bexI conjI exI)
                                          apply (rule refl)+
                                          apply assumption
                                          apply simp
                                          apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                          done
                                        done
                                      done
                                    subgoal apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) int_zle_neg)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  subgoal
                                    apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                    defer
                                    subgoal
                                      by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)

                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      by (meson basic_trans_rules(23) frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                      done
                                    done
                                  done
                                subgoal premises prems2
                                  using prems2(6,11) apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal 
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_mset_gt_0 less_numeral_extra(3) map_in_setD mset_map negative_zle of_nat_le_0_iff snd_conv)
                                  done
                                done
                              done
                            done
                          done
                        done
                      done
                    subgoal
                      unfolding changes_non_zero_def by auto
                    done
                  subgoal premises
                    unfolding extract_progress_def comp_def 
                    apply simp
                    apply (subst (1 2) filter_True)
                    subgoal premises prems4
                      apply (subst (1 2 3) fst_fold_rmdups)
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        apply (metis eq_snd_iff map_in_setD set_map)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        apply (simp flip: change_multiplicities_append_alt)
                        using prems(1,2,3,6,14,9,10,11,13) prems(12)[symmetric] apply -
                        apply simp
                        apply (subst propagate_all_frontier_c_imp_correctness_alt)
                        apply simp_all
                        defer
                        subgoal
                          apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                          apply hypsubst_thin
                          apply (subgoal_tac 
                              "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                          subgoal for x
                            apply (cases x; simp)
                            unfolding input_cap_def frontier_less_equal_iff2
                            using prems(28,29) apply -
                            apply clarsimp
                            apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            subgoal for x
                              apply (cases x; simp)
                              apply force
                              subgoal for b
                                apply (cases b; simp)
                                apply (drule spec2)
                                apply (elim conjE)
                                apply (drule mp)
                                apply (rule image_eqI[rotated])
                                apply auto
                                done
                              done
                            subgoal for a b
                              apply (drule spec2)
                              apply (elim conjE)
                              apply (drule mp)
                              back
                              apply auto
                              done
                            done
                          subgoal premises prems3
                            by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                          done

                        subgoal

                          apply hypsubst_thin
                          apply (simp flip: change_multiplicities_append_alt)
                          apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                          prefer 3
                          apply (rule refl)
                          subgoal
                            using prems(2,9,10,22,23) apply -
                            apply (auto 0 0  simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply fastforce+
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            done
                          subgoal
                            apply safe
                            subgoal for l t x
                              using prems(2,9,10,17,23) apply -
                              apply (drule spec[of _ l])
                              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (elim disjE)
                                      subgoal
                                        unfolding frontier_less_equal_iff2[symmetric]
                                        unfolding frontier_less_equal_iff
                                        by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                      subgoal
                                        apply (drule zcount_gt_0_in_set_2)
                                        apply (elim exE conjE)
                                        apply (drule bspec)
                                        apply simp
                                        apply (rule disjI2)
                                        apply (rule disjI1)
                                        apply (intro bexI conjI exI)
                                        apply (rule refl)+
                                        apply assumption
                                        apply simp
                                        apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                        done
                                      done
                                    subgoal premises prems2
                                      using prems2 apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) not_int_zless_negative)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    unfolding frontier_less_equal_iff2[symmetric]
                                    unfolding frontier_less_equal_iff
                                    by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI2)
                                    apply (rule disjI1)
                                    apply (intro bexI conjI exI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                    done
                                  done
                                subgoal apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal premises
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                                  done
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      defer
                                      subgoal
                                        by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)
                                      subgoal
                                        apply (elim disjE)
                                        subgoal
                                          unfolding frontier_less_equal_iff2[symmetric]
                                          unfolding frontier_less_equal_iff
                                          apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                          by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                        subgoal
                                          apply (drule zcount_gt_0_in_set_2)
                                          apply (elim exE conjE)
                                          apply (drule bspec)
                                          apply simp
                                          apply (rule disjI2)
                                          apply (rule disjI1)
                                          apply (intro bexI conjI exI)
                                          apply (rule refl)+
                                          apply assumption
                                          apply simp
                                          apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                          done
                                        done
                                      done
                                    subgoal apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) int_zle_neg)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  subgoal
                                    apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                    defer
                                    subgoal
                                      by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)

                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      by (meson basic_trans_rules(23) frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                      done
                                    done
                                  done
                                subgoal premises prems2
                                  using prems2(6,11) apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal 
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_mset_gt_0 less_numeral_extra(3) map_in_setD mset_map negative_zle of_nat_le_0_iff snd_conv)
                                  done
                                done
                              done
                            done
                          done
                        done
                      done
                    subgoal
                      unfolding changes_above_impl_def
                      apply (auto simp add: dataflow_topology_implied_frontier_alt_my_summ comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt)
                      using prems(1,2,3,6,14,9,10,11,15,13) prems(12)[symmetric] apply -
                      apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                      apply hypsubst_thin
                      apply (subst (1 2 3) fold_rmdups)
                      apply simp_all
                      prefer 7
                      subgoal for x
                        apply (subst (asm) (1 2 3) fold_rmdups)
                        apply simp_all
                        prefer 7
                        subgoal
                          apply (subgoal_tac 
                              "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                          subgoal
                            apply simp
                            using prems(28,29) apply -
                            apply clarsimp
                            apply (simp flip: add.assoc)
                            apply (simp add: add.assoc)
                            subgoal
                              apply simp
                              apply (elim conjE disjE)
                              subgoal
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                apply (rule disjI2)
                                apply (simp flip: add.assoc)
                                apply (simp add: add.assoc)
                                apply (intro frontier_less_equal_addI)
                                subgoal
                                  apply (rule disjI1)
                                  apply simp_all
                                  subgoal
                                    unfolding frontier_less_equal_iff2
                                    apply (subgoal_tac "zcount (zmset_of (time `# mset caps)) (time x) > 0")
                                    subgoal
                                      by (meson dataflow_topology_from_tree.obtain_frontier_elem zcount_zmset_of_nonneg zmset_elem_nonneg)
                                    subgoal premises prems5
                                      using prems5(12) apply -
                                      apply (induct caps)
                                      apply auto
                                      done
                                    done
                                  done
                                subgoal premises
                                  by force
                                subgoal premises
                                  by (auto simp add: comp_def zmset_map_one_zmset_of)
                                done
                              subgoal
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                apply (rule disjI2)
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                subgoal
                                  apply (rule disjI2)
                                  apply (intro frontier_less_equal_addI)
                                  subgoal
                                    apply (rule disjI1)
                                    unfolding frontier_less_equal_iff2 comp_def 
                                    apply (auto simp add: zmset_map_one_zmset_of)
                                    subgoal for x
                                      apply (cases x; simp)
                                      using prems(6) apply fastforce
                                      subgoal for p
                                        apply (cases p; simp)
                                        subgoal for n t
                                          apply (subgoal_tac "zcount (zmset_of (mset (rmdups (time ` set caps) (map (\<lambda>x. snd (projr x)) (buf1 (Inr (1, 1))))))) t > 0")
                                          subgoal
                                            using in_frontier_zcount by blast
                                          subgoal
                                            apply hypsubst_thin
                                            subgoal premises prems5
                                              using prems5(11,12,13)  apply -
                                              apply auto
                                              apply (rule image_eqI[rotated])
                                              apply assumption
                                              apply auto
                                              apply (metis (full_types) capability.exhaust capability.sel(1) num1_eq1)
                                              done
                                            done
                                          done
                                        done
                                      done
                                    done
                                  subgoal
                                    by (auto simp add: comp_def zmset_map_one_zmset_of)
                                  subgoal
                                    by (auto simp add: comp_def zmset_map_one_zmset_of)
                                  done
                                subgoal
                                  by (auto simp add: comp_def zmset_map_one_zmset_of)
                                done
                              subgoal
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                apply (rule disjI2)
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                subgoal
                                  apply (rule disjI2)
                                  apply (intro frontier_less_equal_addI)
                                  subgoal
                                    apply (rule disjI2)
                                    unfolding frontier_less_equal_iff2 comp_def 
                                    apply (auto simp add: zmset_map_one_zmset_of)
                                    subgoal for n t
                                      apply (subgoal_tac "zcount (zmset_of (mset (rmdups (time ` (set caps \<union> (\<lambda>x. Cap (snd (projr x)) 1) ` set (buf1 (Inr (1, 1))))) (map snd (outpu os1 1))))) t > 0")
                                      subgoal
                                        using in_frontier_zcount by blast
                                      subgoal
                                        apply auto
                                        apply (smt (verit, del_insts) capability.exhaust capability.sel(1) loc_2_1_cases location.inject port.distinct(1) port.inject(1))
                                        done
                                      done
                                    done
                                  subgoal
                                    by (auto simp add: comp_def zmset_map_one_zmset_of)
                                  subgoal
                                    by (auto simp add: comp_def zmset_map_one_zmset_of)
                                  done
                                subgoal
                                  by (auto simp add: comp_def zmset_map_one_zmset_of)
                                done
                              done
                            done
                          subgoal premises prems3
                            by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                          done
                        using prems apply simp
                        subgoal
                          using prems(33) by (clarsimp simp add: sorted_append comp_def)
                        subgoal
                          using prems(32) apply -
                          apply auto
                          subgoal for t x
                            apply (cases x; cases t; simp)
                            using prems(6) apply fastforce
                            using image_iff apply fastforce
                            done
                          done
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: sorted_append comp_def)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        subgoal
                          using prems(33) by (clarsimp simp add: sorted_append comp_def)
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: comp_def sorted_append)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        done
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        subgoal for t x
                          apply (cases x; cases t; simp)
                          using prems(6) apply fastforce
                          using image_iff apply fastforce
                          done
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      done
                    done                   
                  subgoal premises
                    unfolding extract_progress_def comp_def changes_above_impl_def
                    by simp

                  subgoal premises
                    unfolding extract_progress_def comp_def 
                    apply simp
                    apply (subst (1 2) filter_True)
                    subgoal premises prems4
                      apply (subst (1 2 3) fst_fold_rmdups)
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        apply (metis eq_snd_iff map_in_setD set_map)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        apply (simp flip: change_multiplicities_append_alt)
                        using prems(1,2,3,6,14,9,10,11,13) prems(12)[symmetric] apply -
                        apply simp
                        apply (subst propagate_all_frontier_c_imp_correctness_alt)
                        apply simp_all
                        defer
                        subgoal
                          apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                          apply hypsubst_thin
                          apply (subgoal_tac 
                              "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                          subgoal for x
                            apply (cases x; simp)
                            unfolding input_cap_def frontier_less_equal_iff2
                            using prems(28,29) apply -
                            apply clarsimp
                            apply (auto simp add: frontier_singleton split: if_splits dest!: antichain_singletonD)
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            using mem_antichain_nonempty apply blast
                            subgoal for x
                              apply (cases x; simp)
                              apply force
                              subgoal for b
                                apply (cases b; simp)
                                apply (drule spec2)
                                apply (elim conjE)
                                apply (drule mp)
                                apply (rule image_eqI[rotated])
                                apply auto
                                done
                              done
                            subgoal for a b
                              apply (drule spec2)
                              apply (elim conjE)
                              apply (drule mp)
                              back
                              apply auto
                              done
                            done
                          subgoal premises prems3
                            by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                          done

                        subgoal

                          apply hypsubst_thin
                          apply (simp flip: change_multiplicities_append_alt)
                          apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                          prefer 3
                          apply (rule refl)
                          subgoal
                            using prems(2,9,10,22,23) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply fastforce+
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            done
                          subgoal
                            apply safe
                            subgoal for l t x
                              using prems(2,9,10,17,23) apply -
                              apply (drule spec[of _ l])
                              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (elim disjE)
                                      subgoal
                                        unfolding frontier_less_equal_iff2[symmetric]
                                        unfolding frontier_less_equal_iff
                                        by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                      subgoal
                                        apply (drule zcount_gt_0_in_set_2)
                                        apply (elim exE conjE)
                                        apply (drule bspec)
                                        apply simp
                                        apply (rule disjI2)
                                        apply (rule disjI1)
                                        apply (intro bexI conjI exI)
                                        apply (rule refl)+
                                        apply assumption
                                        apply simp
                                        apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                        done
                                      done
                                    subgoal premises prems2
                                      using prems2 apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) not_int_zless_negative)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  apply (elim disjE)
                                  subgoal
                                    unfolding frontier_less_equal_iff2[symmetric]
                                    unfolding frontier_less_equal_iff
                                    by (metis (no_types, lifting) basic_trans_rules(23) frontier_idempotent frontier_le_remove_left frontier_less_equal_iff frontier_less_equal_zcount_pos zcount_zmset_of_nonneg)
                                  subgoal
                                    apply (drule zcount_gt_0_in_set_2)
                                    apply (elim exE conjE)
                                    apply (drule bspec)
                                    apply simp
                                    apply (rule disjI2)
                                    apply (rule disjI1)
                                    apply (intro bexI conjI exI)
                                    apply (rule refl)+
                                    apply assumption
                                    apply simp
                                    apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                    done
                                  done
                                subgoal apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal premises
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                                  done
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      defer
                                      subgoal
                                        by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)
                                      subgoal
                                        apply (elim disjE)
                                        subgoal
                                          unfolding frontier_less_equal_iff2[symmetric]
                                          unfolding frontier_less_equal_iff
                                          apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                          by (meson frontier_less_equal_iff frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                                        subgoal
                                          apply (drule zcount_gt_0_in_set_2)
                                          apply (elim exE conjE)
                                          apply (drule bspec)
                                          apply simp
                                          apply (rule disjI2)
                                          apply (rule disjI1)
                                          apply (intro bexI conjI exI)
                                          apply (rule refl)+
                                          apply assumption
                                          apply simp
                                          apply (smt (verit) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                          done
                                        done
                                      done
                                    subgoal apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) int_zle_neg)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  subgoal
                                    apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                    defer
                                    subgoal
                                      by (smt (verit, del_insts) add_empty_zmultiset(2) frontier_below_eq_frontier_plus_pos frontier_idempotent zcount_zmset_of_nonneg zmset_of_plus zmset_subset_eq_zmultiset_union_diff_commute zmultiset_move_add_other_side)

                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      by (meson basic_trans_rules(23) frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (smt (verit, best) frontier_below_eq_frontier_plus_pos frontier_idempotent frontier_less_equal_add_cases frontier_less_equal_iff2 frontier_less_equal_le_trans zmset_of_mset_set_ge_zero)
                                      done
                                    done
                                  done
                                subgoal premises prems2
                                  using prems2(6,11) apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal 
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_mset_gt_0 less_numeral_extra(3) map_in_setD mset_map negative_zle of_nat_le_0_iff snd_conv)
                                  done
                                done
                              done
                            done
                          done
                        done
                      done
                    subgoal
                      unfolding changes_above_impl_def
                      apply (auto simp add: dataflow_topology_implied_frontier_alt_my_summ comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt)
                      using prems(1,2,3,6,14,9,10,11,15,13) prems(12)[symmetric] apply -
                      apply (clarsimp simp add: comp_def extract_progress_def dataflow_topology_implied_frontier_alt_my_summ c_pts_change_multiplicities)
                      apply hypsubst_thin
                      apply (subst (1 2 3) fold_rmdups)
                      apply simp_all
                      prefer 7
                      subgoal for x
                        apply (subst (asm) (1 2 3) fold_rmdups)
                        apply simp_all
                        prefer 7
                        subgoal
                          apply (subgoal_tac 
                              "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                          subgoal
                            apply simp
                            using prems(28,29) apply -
                            apply clarsimp
                            apply (simp flip: add.assoc)
                            apply (simp add: add.assoc)
                            subgoal
                              apply simp
                              apply (elim conjE disjE)
                              subgoal
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                apply (rule disjI2)
                                apply (simp flip: add.assoc)
                                apply (simp add: add.assoc)
                                apply (intro frontier_less_equal_addI)
                                subgoal
                                  apply (rule disjI1)
                                  apply simp_all
                                  subgoal
                                    unfolding frontier_less_equal_iff2
                                    apply (subgoal_tac "zcount (zmset_of (time `# mset caps)) (time x) > 0")
                                    subgoal
                                      by (meson dataflow_topology_from_tree.obtain_frontier_elem zcount_zmset_of_nonneg zmset_elem_nonneg)
                                    subgoal premises prems5
                                      using prems5(12) apply -
                                      apply (induct caps)
                                      apply auto
                                      done
                                    done
                                  done
                                subgoal premises
                                  by force
                                subgoal premises
                                  by (auto simp add: comp_def zmset_map_one_zmset_of)
                                done
                              subgoal
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                apply (rule disjI2)
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                subgoal
                                  apply (rule disjI2)
                                  apply (intro frontier_less_equal_addI)
                                  subgoal
                                    apply (rule disjI1)
                                    unfolding frontier_less_equal_iff2 comp_def 
                                    apply (auto simp add: zmset_map_one_zmset_of)
                                    subgoal for x
                                      apply (cases x; simp)
                                      using prems(6) apply fastforce
                                      subgoal for p
                                        apply (cases p; simp)
                                        subgoal for n t
                                          apply (subgoal_tac "zcount (zmset_of (mset (rmdups (time ` set caps) (map (\<lambda>x. snd (projr x)) (buf1 (Inr (1, 1))))))) t > 0")
                                          subgoal
                                            using in_frontier_zcount by blast
                                          subgoal
                                            apply hypsubst_thin
                                            subgoal premises prems5
                                              using prems5(11,12,13)  apply -
                                              apply auto
                                              apply (rule image_eqI[rotated])
                                              apply assumption
                                              apply auto
                                              apply (metis (full_types) capability.exhaust capability.sel(1) num1_eq1)
                                              done
                                            done
                                          done
                                        done
                                      done
                                    done
                                  subgoal
                                    by (auto simp add: comp_def zmset_map_one_zmset_of)
                                  subgoal
                                    by (auto simp add: comp_def zmset_map_one_zmset_of)
                                  done
                                subgoal
                                  by (auto simp add: comp_def zmset_map_one_zmset_of)
                                done
                              subgoal
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                apply (rule disjI2)
                                apply (intro frontier_less_equal_addI)
                                apply simp_all
                                subgoal
                                  apply (rule disjI2)
                                  apply (intro frontier_less_equal_addI)
                                  subgoal
                                    apply (rule disjI2)
                                    unfolding frontier_less_equal_iff2 comp_def 
                                    apply (auto simp add: zmset_map_one_zmset_of)
                                    subgoal for n t
                                      apply (subgoal_tac "zcount (zmset_of (mset (rmdups (time ` (set caps \<union> (\<lambda>x. Cap (snd (projr x)) 1) ` set (buf1 (Inr (1, 1))))) (map snd (outpu os1 1))))) t > 0")
                                      subgoal
                                        using in_frontier_zcount by blast
                                      subgoal
                                        apply auto
                                        apply (smt (verit, del_insts) capability.exhaust capability.sel(1) loc_2_1_cases location.inject port.distinct(1) port.inject(1))
                                        done
                                      done
                                    done
                                  subgoal
                                    by (auto simp add: comp_def zmset_map_one_zmset_of)
                                  subgoal
                                    by (auto simp add: comp_def zmset_map_one_zmset_of)
                                  done
                                subgoal
                                  by (auto simp add: comp_def zmset_map_one_zmset_of)
                                done
                              done
                            done
                          subgoal premises prems3
                            by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                          done
                        using prems apply simp
                        subgoal
                          using prems(33) by (clarsimp simp add: sorted_append comp_def)
                        subgoal
                          using prems(32) apply -
                          apply auto
                          subgoal for t x
                            apply (cases x; cases t; simp)
                            using prems(6) apply fastforce
                            using image_iff apply fastforce
                            done
                          done
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: sorted_append comp_def)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        subgoal
                          using prems(33) by (clarsimp simp add: sorted_append comp_def)
                        subgoal
                          using prems(7, 32, 33) apply -
                          apply (auto simp add: comp_def sorted_append)
                          apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                          done
                        done
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        subgoal for t x
                          apply (cases x; cases t; simp)
                          using prems(6) apply fastforce
                          using image_iff apply fastforce
                          done
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      done
                    done
                  subgoal premises
                    by (auto simp add: zmset_map_minus_one_zmset_of extract_progress_def dataflow_topology_implied_frontier_alt_my_summ comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt)
                  subgoal premises
                    using prems(6,27,32) apply -
                    apply (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities)
                    apply (subst (1 2 3) fold_rmdups)
                    prefer 3
                    subgoal
                      apply auto
                      subgoal for t x
                        apply (cases t; cases x; simp)
                        apply fastforce
                        apply force
                        done
                      done
                    using prems apply simp
                    subgoal
                      using prems(33) by (clarsimp simp add: sorted_append comp_def)
                    subgoal
                      using prems(32) apply -
                      apply auto
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      done
                    subgoal
                      using prems(33) by (clarsimp simp add: sorted_append comp_def)
                    subgoal
                      using prems(7, 32, 33) apply -
                      apply (auto simp add: comp_def sorted_append)
                      apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                      done
                    subgoal for t
                      apply clarsimp
                      using prems(1,2,3,8,9,10,11,15) apply -
                      apply (auto simp add: zmultiset_eq_iff extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities)
                      apply hypsubst_thin
                      apply (drule spec[of _ t])+
                      apply (simp flip: add.assoc)
                      apply (simp add: add.assoc)
                      apply (auto simp add: comp_def zmset_of_plus zmset_map_one_zmset_of )
                      done
                    done
                  subgoal premises
                    using prems(28,1,2,3,8,9,10,11,14,13) prems(12)[symmetric] apply -
                    apply (auto simp add: extract_progress_def dataflow_topology_implied_frontier_alt_my_summ comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt)
                    subgoal for cap
                      apply (subst (asm) (1 2 3 4 5 6) fold_rmdups)
                      apply simp_all
                      prefer 13
                      subgoal
                        apply (subst (asm) propagate_all_frontier_c_imp_correctness_alt)
                        apply simp_all
                        defer
                        subgoal
                          apply (subgoal_tac 
                              "zmset (map (\<lambda>x. (snd (projr x), - 1)) (buf1 (Inr (1, 1)))) + zmset (map (\<lambda>x. (snd x, - 1)) (outpu os1 1)) =
    - (zmset_of ({#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} + snd `# mset (outpu os1 1)))")
                          subgoal
                            apply (auto simp add: extract_progress_def dataflow_topology_implied_frontier_alt_my_summ comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt)
                            subgoal for x
                              apply (cases x; simp)
                              using prems(6) apply fastforce
                              apply auto
                              apply hypsubst_thin
                              unfolding frontier_less_equal_iff2
                              apply (auto simp add: input_cap_def zmset_map_minus_one_zmset_of extract_progress_def dataflow_topology_implied_frontier_alt_my_summ comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt split: if_splits)
                              apply (meson mem_antichain_nonempty)
                              subgoal for a b t'
                                using prems(28,29) apply -
                                apply simp
                                apply (drule spec2)
                                apply (elim conjE)
                                apply (drule mp)
                                apply (rule image_eqI[rotated])
                                apply auto
                                done
                              done
                            subgoal for x

                              apply hypsubst_thin
                              unfolding frontier_less_equal_iff2
                              apply (auto simp add: input_cap_def zmset_map_minus_one_zmset_of extract_progress_def dataflow_topology_implied_frontier_alt_my_summ comp_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities simp flip: change_multiplicities_append_alt split: if_splits)
                              apply (meson mem_antichain_nonempty)
                              subgoal for t'
                                using prems(28,29) by simp
                              done
                            done
                          subgoal premises prems3
                            by (auto simp add: zmset_of_plus zmset_map_minus_one_zmset_of zmset_map_one_zmset_of )
                          done
                        subgoal premises prems4
                          apply (rule change_multiplicities_preserves_inv[of my_summ, simplified, OF prems(20) prems(21) prems(19)[unfolded prems(1)] ])
                          prefer 3
                          apply (rule refl)
                          subgoal
                            using prems(2,9,11,10,22,23) apply -
                            apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply fastforce+
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            subgoal
                              apply (drule bspec)
                              apply auto
                              done
                            done
                          subgoal
                            apply safe
                            subgoal for l t x
                              using prems(2,9,10,17,23,11) prems(12)[symmetric] apply -
                              apply (drule spec[of _ l])
                              apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      defer
                                      subgoal premises
                                        by (simp add: frontier_le_remove_left)
                                      apply (elim disjE)
                                      subgoal
                                        unfolding frontier_less_equal_iff2[symmetric]
                                        unfolding frontier_less_equal_iff
                                        apply (rule order.trans)
                                        apply assumption
                                        apply (rule frontier_le_remove_left)
                                        apply simp_all
                                        apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                        done
                                      subgoal
                                        apply (drule zcount_gt_0_in_set_2)
                                        apply (elim exE conjE)
                                        apply (drule bspec)
                                        apply simp
                                        apply (rule disjI2)
                                        apply (rule disjI2)
                                        apply (rule disjI1)
                                        apply (intro bexI conjI exI)
                                        apply (rule refl)+
                                        apply assumption
                                        apply simp
                                        apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                        done
                                      done
                                    subgoal premises prems2
                                      using prems2 apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) not_int_zless_negative)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  subgoal
                                    apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                    defer
                                    subgoal premises
                                      by (simp add: frontier_le_remove_left)
                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      apply (rule order.trans)
                                      apply assumption
                                      apply (rule frontier_le_remove_left)
                                      apply simp_all
                                      apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                      done
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                      done
                                    done
                                  done
                                subgoal apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal premises
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_image_mset_ge_count count_mset_gt_0 not_int_zless_negative of_nat_le_0_iff snd_conv verit_comp_simplify1(3))
                                  done
                                done
                              subgoal
                                apply (drule bspec)
                                apply blast
                                apply simp
                                apply (meson frontier_less_equal_iff2 frontier_less_equal_le_trans)
                                done
                              subgoal for x
                                apply (cases x; simp)
                                using prems(6) apply fastforce
                                apply hypsubst_thin
                                subgoal for p
                                  apply (cases p)
                                  apply simp
                                  subgoal for n t
                                    apply hypsubst_thin
                                    apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                    subgoal
                                      apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                      defer
                                      subgoal premises
                                        by (simp add: frontier_le_remove_left)
                                      subgoal
                                        apply (elim disjE)
                                        subgoal
                                          unfolding frontier_less_equal_iff2[symmetric]
                                          unfolding frontier_less_equal_iff
                                          apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                          apply (rule order.trans)
                                          apply assumption
                                          apply (rule frontier_le_remove_left)
                                          apply simp_all
                                          apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                          done
                                        subgoal
                                          apply (drule zcount_gt_0_in_set_2)
                                          apply (elim exE conjE)
                                          apply (drule bspec)
                                          apply simp
                                          apply (rule disjI2)
                                          apply (rule disjI2)
                                          apply (rule disjI1)
                                          apply (intro bexI conjI exI)
                                          apply (rule refl)+
                                          apply assumption
                                          apply simp
                                          apply (smt (verit, ccfv_threshold) add.commute add.left_commute frontier_less_equal_addI frontier_less_equal_iff2 frontier_less_equal_le_trans zcount_zmset_of_nonneg zmset_of_plus)
                                          done
                                        done
                                      done
                                    subgoal apply -
                                      apply (simp add:  zmultiset_eq_iff)
                                      apply (drule spec[of _ t])
                                      apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                      defer
                                      subgoal premises
                                        using prems(8) apply -
                                        apply (induct "consu os2")
                                        apply auto
                                        apply (meson zcount_zmset_ge_zero)
                                        done
                                      subgoal
                                        apply (subgoal_tac "int (count {#snd (projr x). x \<in># mset (buf1 (Inr (1, 1)))#} t) > 0")
                                        subgoal
                                          by (smt (z3) int_zle_neg)
                                        subgoal
                                          apply clarsimp
                                          apply (rule image_eqI[rotated])
                                          apply assumption
                                          apply auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for p
                                apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t > 0 \<or> zcount (zmset (map snd (produ os1))) t > 0")
                                subgoal
                                  subgoal
                                    apply (subgoal_tac "frontier
        (zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 0 (Src 1)))))) + zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Src 1)))))) +
         zmset_of (mset_set (set_antichain (frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1))))))) \<le> frontier (c_pts (pt_tr sg) (Loc 1 (Trg 1)))")
                                    defer
                                    subgoal premises
                                      by (simp add: frontier_le_remove_left)
                                    apply (elim disjE)
                                    subgoal
                                      unfolding frontier_less_equal_iff2[symmetric]
                                      unfolding frontier_less_equal_iff
                                      apply (rule order.trans)
                                      apply assumption
                                      apply (rule frontier_le_remove_left)
                                      apply simp_all
                                      apply (meson frontier_less_equal_iff frontier_less_equal_zcount_pos)
                                      done
                                    subgoal
                                      apply (drule zcount_gt_0_in_set_2)
                                      apply (elim exE conjE)
                                      apply (drule bspec)
                                      apply simp
                                      apply (rule disjI2)
                                      apply (rule disjI2)
                                      apply (rule disjI1)
                                      apply (intro bexI conjI exI)
                                      apply (rule refl)+
                                      apply assumption
                                      apply simp
                                      apply (smt (verit, ccfv_threshold) add.commute add.left_commute frontier_less_equal_addI frontier_less_equal_iff2 frontier_less_equal_le_trans zcount_zmset_of_nonneg zmset_of_plus)
                                      done
                                    done
                                  done
                                subgoal  apply -
                                  apply (simp add:  zmultiset_eq_iff)
                                  apply (drule spec[of _ t])
                                  apply (subgoal_tac "zcount (zmset (map snd (consu os2))) t \<ge> 0")
                                  defer
                                  subgoal 
                                    using prems(8) apply -
                                    apply (induct "consu os2")
                                    apply auto
                                    apply (meson zcount_zmset_ge_zero)
                                    done
                                  subgoal
                                    by (smt (z3) count_mset_gt_0 less_numeral_extra(3) map_in_setD mset_map negative_zle of_nat_le_0_iff snd_conv)
                                  done
                                done
                              done
                            done
                          done
                        done
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(32) apply -
                        apply auto
                        apply hypsubst_thin
                        subgoal for cap x
                          apply (cases x; cases cap; simp)
                          using prems(6) apply fastforce
                          apply auto
                          using image_iff apply fastforce
                          done
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      done
                    done

                  subgoal premises
                    using prems(30,29) apply -
                    apply auto
                    subgoal
                      apply (subst (asm) (1 2 3) fold_rmdups)
                      prefer 7
                      subgoal
                        unfolding BENQ_def
                        apply (auto simp add: extract_progress_def propagate_all_preserves_c_pts_alt c_pts_change_multiplicities)
                        apply (intro fold_Cap_eq_Nil)
                        apply simp_all
                        apply fast+
                        done
                      using prems apply simp
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)

                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: sorted_append comp_def)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      subgoal
                        using prems(33) by (clarsimp simp add: sorted_append comp_def)
                      subgoal
                        using prems(7, 32, 33) apply -
                        apply (auto simp add: comp_def sorted_append)
                        apply (smt (verit, del_insts) Un_iff eq_snd_iff image_iff prod.simps(2))
                        done
                      done
                    subgoal premises prems5 for t
                      using prems5(1,2,3) apply -
                      unfolding BENQ_def
                      apply (intro fold_Cap_eq_Nil)
                      apply simp_all
                      apply (auto 0 0 simp flip: add.assoc simp add: changes_above_impl_def changes_non_zero_def dataflow_topology_implied_frontier_alt_my_summ extract_progress_def change_multiplicities_append_comp c_pts_change_multiplicities comp_def split: option.splits; hypsubst_thin?)
                      subgoal for t'
                        apply (cases t'; simp)
                        using prems(6) apply force+
                        done
                      subgoal
                        by fastforce
                      done
                    done
                  done
                subgoal
                  apply (subst fold_rmdups)
                  prefer 4
                  subgoal
                    unfolding comp_def
                    apply (auto simp add: comp_def sorted_append)
                    using prems(7) apply blast
                    apply (rule sorted_map_rmdups)
                    using prems(6,33,32) apply -
                    apply (auto simp add: comp_def sorted_append)
                    subgoal for t x
                      apply (cases t; cases x; simp)
                      apply fastforce
                      using image_iff apply fastforce
                      done
                    done
                  using prems(6,7,33,32) apply (auto simp add: sorted_append)
                  subgoal for t x
                    apply (cases t; cases x; simp)
                    apply fastforce
                    using image_iff apply fastforce
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

find_consts " ('p, 'd, 't) operator_state"

abbreviation init_op_state where
"init_op_state ft \<equiv> \<lparr> consu = [],
   inter = [],
   produ = [],
   outpu = (\<lambda> _. []),
   front = ft \<rparr>"


abbreviation init_conf where
  "init_conf summary cgs \<equiv> the (propagate_all summary (change_multiplicities summary cgs \<lparr>c_work = (\<lambda> _.  {#}\<^sub>z), c_pts = (\<lambda> _.  {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>))"

abbreviation "default_internal_summary \<equiv> (\<lambda> _ _. frontier (abs_zmultiset (mset [0 :: nat], {#})))"

abbreviation "init_subgraph' summary cgs \<equiv>
   \<lparr> pt_tr = init_conf summary cgs,
   edges = (\<lambda> l1. [l2 \<leftarrow> enum_class.enum. \<not> is_empty_antichain (summary l1 l2) \<and> is_Src (port l1) \<and> is_Trg (port l2) ]),
   summ = summary \<rparr>"

abbreviation "my_sg inps \<equiv> init_subgraph' my_summ (if inps = LNil then [] else [(Loc 0 (Src 0), 0, 1)])"

abbreviation "os1 inps \<equiv> init_op_state (\<lambda> p. frontier (c_imp (pt_tr (my_sg inps)) (Loc 0 (Trg p))))"
abbreviation "os2 inps \<equiv> init_op_state (\<lambda> p. frontier (c_imp (pt_tr (my_sg inps)) (Loc 1 (Trg p))))"

abbreviation "st1 \<equiv> \<lparr>cons = [], inte = [], prod = []\<rparr>"
abbreviation "st2 \<equiv> \<lparr>cons = [], inte = [], prod = []\<rparr>"

lemma propagate_all_empty_conf[simp]:
  "the (propagate_all my_summ empty_conf) = empty_conf"
  unfolding propagate_all_def comp_def
  by (simp add: while_option_unfold worklist_is_empty_def)

lemma zmultiset_of_antichain_empty[simp]:
  "zmultiset_of_antichain {}\<^sub>A = {#}\<^sub>z"
  apply transfer
  unfolding equiv_zmset_def
  apply auto
  done

lemma change_multiplicities_empty_conf[simp]:
  "change_multiplicities my_summ [(Loc 0 (Src 1), 0, 1)] empty_conf =
   \<lparr>c_work = (\<lambda> l. if l = Loc 0 (Src 1) then {# 0 #}\<^sub>z else {#}\<^sub>z), c_pts = (\<lambda> l. if l = Loc 0 (Src 1) then {# 0 #}\<^sub>z else {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>"
  unfolding change_multiplicities_def
  apply auto
  subgoal
    apply (rule ext)+
    apply clarsimp
    apply transfer'
    unfolding update_zmultiset_singleton frontier_singleton
    apply auto
    done
 subgoal
    apply (rule ext)+
    apply clarsimp
    apply transfer'
    unfolding update_zmultiset_singleton frontier_singleton
    apply auto
    done
  done

lemma my_summ_code[code]:
  "my_summ = my_summ'"
  unfolding my_summ_def my_summ'_def
  apply (rule ext)+
  subgoal for l1 l2
    apply simp
    apply (subst (1 2 3 4 5 6) zmultiset_of_antichain.abs_eq[symmetric, where x="{0}", simplified])
    subgoal
      unfolding incomparable_def eq_onp_def
      by auto[1]
      apply (metis dataflow_topology_from_tree.zmset_of_lemma frontier_idempotent frontier_singleton)
    done
  done



lemma c_imp_the_propagate_all_my_summ:
  "c_imp (the (propagate_all my_summ \<lparr>c_work = (\<lambda> l. if l = Loc 0 (Src 1) then {# 0 #}\<^sub>z else {#}\<^sub>z), c_pts = (\<lambda> l. if l = Loc 0 (Src 1) then {# 0 #}\<^sub>z else {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>)) =
   (\<lambda> l. if l = Loc 1 (Trg 1) \<or> l = Loc 1 (Src 1) \<or> l = Loc 0 (Src 1) then {# 0 #}\<^sub>z else {#}\<^sub>z)"
  apply (rule ext)
  subgoal for l
    using loc_2_1_cases[where l=l] apply -
    apply (elim disjE; hypsubst_thin?)
    subgoal
      apply simp
      unfolding zequal_equal[symmetric]
      apply eval
      done
    subgoal
      apply simp
      unfolding zequal_equal[symmetric]
      apply eval
      done
    subgoal
      apply simp
      unfolding zequal_equal[symmetric]
      apply eval
      done
    subgoal
      apply simp
      unfolding zequal_equal[symmetric]
      apply eval
      done
    done
  done

lemma c_work_the_propagate_all_my_summ:
  "c_work (the (propagate_all my_summ \<lparr>c_work = (\<lambda> l. if l = Loc 0 (Src 1) then {# 0 #}\<^sub>z else {#}\<^sub>z), c_pts = (\<lambda> l. if l = Loc 0 (Src 1) then {# 0 #}\<^sub>z else {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>)) =
   (\<lambda> l. {#}\<^sub>z)"
 apply (rule ext)
  subgoal for l
    using loc_2_1_cases[where l=l] apply -
    apply (elim disjE; hypsubst_thin?)
    subgoal
      unfolding zequal_equal[symmetric]
      apply eval
      done
    subgoal
      unfolding zequal_equal[symmetric]
      apply eval
      done
    subgoal
      unfolding zequal_equal[symmetric]
      apply eval
      done
    subgoal
      unfolding zequal_equal[symmetric]
      apply eval
      done
    done
  done

         
abbreviation "op1 inps \<equiv> Logic (input_top (os1 (inps 1)) (\<lambda> _. 0) inps) default_internal_summary"
abbreviation "op2 inps \<equiv> Logic (max_top' (os2 (inps 1)) (\<lambda> _. []) []) default_internal_summary"

abbreviation "opf inps \<equiv> snd (compile_dataflow_tree (Comp [(0, 1) \<mapsto> (0, 1)] (op1 inps) (op2 inps)))"

lemma dataflow_op_inp_m_top_source_op:
 "dataflow_op (my_sg (inps 1)) (opf inps) \<approx>
  map_op (\<lambda>p :: 1. (1, 1)) (\<lambda>p :: 1. (1, 1)) (source_op
   (\<lambda>p. Coinductive_List_Auxiliary.lconcat
         (lmap (\<lambda>z. case z of (xs, t) \<Rightarrow> case xs of [] \<Rightarrow> [] | a # list \<Rightarrow> [(Max (set xs), t)])
           (lzip (inps 1) (iterates (trivial_dataflow_topology_interpretation.followed_by (Suc 0)) 0)))))"
  unfolding compile_dataflow_tree_def Let_def
  apply (simp only: implementation_graph_checker_correct weights_to_graph_fun_def Let_def compile_dataflow_tree_aux.simps prod.case)
  apply (subst (22) if_P)
   apply simp_all
  subgoal
    by eval
  subgoal
    unfolding comp_def
    apply (intro conjI impI)
    subgoal
      using dataflow_op_inp_m_top_source_op_aux
        [where inps=inps and n="\<lambda> _. 0" and caps=Nil and xs="\<lambda> _. []" and ys="\<lambda> _. []", of "my_sg (inps 1)" "os1 (inps 1)" "os2 (inps 1)" "\<lambda> _. []" "\<lambda> _. []" "os1 (inps 1)" st1 "os2 (inps 1)" st2,
          unfolded max_from_caps_buf_def extract_progress_def changes_non_zero_def changes_above_impl_def change_multiplicities_simp_alt propagate_all_preserves_c_pts_alt, simplified] apply -
      apply (simp add: propagate_all_preserves_c_pts_alt)
      apply (drule meta_spec)
      apply (drule meta_mp)
      subgoal premises
        apply (subgoal_tac "\<not> is_empty_antichain (antichain {0 :: nat})")
        subgoal
          unfolding my_summ_def  enum_location_def enum_port_def enum_num1_def
          apply (rule ext)
          apply clarsimp
          unfolding enum_location_def  Numeral_Type.enum_bit0_def Abs_bit0'_def one_bit0_def zero_bit0_def zero_bit0_def
          apply clarsimp
          apply (metis one_bit0_def rel_simps(93) zero_bit0_def)
          done
        subgoal
          unfolding is_empty_antichain.rep_eq Set.is_empty_def
          apply (subst antichain.antichain_inverse)
           apply (auto simp add: incomparable_def)
          done
        done
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      unfolding input_cap_def
       apply simp
      apply (drule meta_mp)
       defer
       apply (drule meta_mp)
        defer
        apply (drule meta_mp)
         defer
         apply (drule meta_mp)
          defer
      subgoal
        apply (rule wbisim_trans[rotated])
         apply assumption
        subgoal premises
          apply (rule wbisim_refl_alt)
          apply (rule arg_cong2[where f=dataflow_op])
           apply simp_all
          subgoal
            subgoal
              apply (subgoal_tac "\<not> is_empty_antichain (antichain {0 :: nat})")
              subgoal
                unfolding my_summ_def  enum_location_def enum_port_def enum_num1_def
                apply (rule ext)
                apply clarsimp
                unfolding enum_location_def  Numeral_Type.enum_bit0_def Abs_bit0'_def one_bit0_def zero_bit0_def zero_bit0_def
                apply clarsimp
                apply (metis one_bit0_def rel_simps(93) zero_bit0_def)
                done
              subgoal
                unfolding is_empty_antichain.rep_eq Set.is_empty_def
                apply (subst antichain.antichain_inverse)
                 apply (auto simp add: incomparable_def)
                done
              done
            done
          subgoal
            apply (rule arg_cong3[where f=map_op])
              apply simp_all
            apply (rule arg_cong4[where f=comp_op])
               apply simp_all
            apply (rule ext)+
            apply (auto split: sum.splits)
            done
          done
        done
      subgoal 
        unfolding dataflow_topology_implied_frontier_alt_my_summ
        by auto
      subgoal
        apply (subst dataflow_topology.inv_imps_work_sum_def)
         apply auto
        done
      subgoal
        apply (subst trivial_dataflow_topology_interpretation.inv_implications_nonneg_def)
        apply auto      
        done
      subgoal
        apply (subst trivial_dataflow_topology_interpretation.inv_imp_plus_work_nonneg_def)
        apply auto
        done
      done
    subgoal
      using dataflow_op_inp_m_top_source_op_aux
        [where inps=inps and n="\<lambda> _. 0" and caps=Nil and xs="\<lambda> _. []" and ys="\<lambda> _. []", of "my_sg (inps 1)" "os1 (inps 1)" "os2 (inps 1)" "\<lambda> _. []" "\<lambda> _. []" "os1 (inps 1)" st1 "os2 (inps 1)" st2,
          unfolded max_from_caps_buf_def extract_progress_def changes_non_zero_def changes_above_impl_def change_multiplicities_simp_alt propagate_all_preserves_c_pts_alt, simplified] apply -
      apply (simp add: propagate_all_preserves_c_pts_alt)
      apply (drule meta_spec)
      apply (drule meta_mp)
      subgoal premises
        apply (subgoal_tac "\<not> is_empty_antichain (antichain {0 :: nat})")
        subgoal
          unfolding my_summ_def  enum_location_def enum_port_def enum_num1_def
          apply (rule ext)
          apply clarsimp
          unfolding enum_location_def  Numeral_Type.enum_bit0_def Abs_bit0'_def one_bit0_def zero_bit0_def zero_bit0_def
          apply clarsimp
          apply (metis one_bit0_def rel_simps(93) zero_bit0_def)
          done
        subgoal
          unfolding is_empty_antichain.rep_eq Set.is_empty_def
          apply (subst antichain.antichain_inverse)
           apply (auto simp add: incomparable_def)
          done
        done
      unfolding c_pts_change_multiplicities
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      unfolding input_cap_def
       apply (simp add: update_zmultiset_singleton(2))
      apply (drule meta_mp)
       defer
       apply (drule meta_mp)
        defer
        apply (drule meta_mp)
         defer
         apply (drule meta_mp)
          defer
      subgoal
        apply (rule wbisim_trans[rotated])
         apply assumption
        subgoal premises
          apply (rule wbisim_refl_alt)
          apply (rule arg_cong2[where f=dataflow_op])
           apply simp_all
          subgoal
            subgoal
              apply (subgoal_tac "\<not> is_empty_antichain (antichain {0 :: nat})")
              subgoal
                unfolding my_summ_def  enum_location_def enum_port_def enum_num1_def
                apply (rule ext)
                apply clarsimp
                unfolding enum_location_def  Numeral_Type.enum_bit0_def Abs_bit0'_def one_bit0_def zero_bit0_def zero_bit0_def
                apply clarsimp
                apply (metis one_bit0_def rel_simps(93) zero_bit0_def)
                done
              subgoal
                unfolding is_empty_antichain.rep_eq Set.is_empty_def
                apply (subst antichain.antichain_inverse)
                 apply (auto simp add: incomparable_def)
                done
              done
            done
          subgoal
            apply (rule arg_cong3[where f=map_op])
              apply simp_all
            apply (rule arg_cong4[where f=comp_op])
               apply simp_all
            apply (rule ext)+
            apply (auto split: sum.splits)
            done
          done
        done
      subgoal 
        apply (subst propagate_all_frontier_c_imp_correctness_alt)
           apply auto
        subgoal
          apply (subst trivial_dataflow_topology_interpretation.inv_implications_nonneg_def)
          apply auto      
          done
        subgoal
          apply (subst trivial_dataflow_topology_interpretation.inv_imp_plus_work_nonneg_def)
          apply auto
          done
        subgoal
          apply (subst dataflow_topology.inv_imps_work_sum_def)
           apply auto
          apply transfer'
          unfolding update_zmultiset_singleton frontier_singleton
          apply auto
          done
        unfolding dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt
        apply auto
        done
      subgoal
        apply (subst dataflow_topology.inv_imps_work_sum_def)
        unfolding dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt c_imp_the_propagate_all_my_summ c_work_the_propagate_all_my_summ 
         apply auto
        subgoal premises
          unfolding my_summ_def
          apply auto
          unfolding frontier_singleton
          apply (subst antichain_inverse)
          unfolding incomparable_def
           apply auto
          done
        subgoal premises
          unfolding my_summ_def
          apply auto
          unfolding frontier_singleton
          apply (subst antichain_inverse)
          unfolding incomparable_def
           apply auto
          done
        subgoal premises
          unfolding my_summ_def
          apply auto
          unfolding frontier_singleton
          apply (subst antichain_inverse)
          unfolding incomparable_def
           apply auto
          done
        subgoal 
          unfolding my_summ_def
          by auto
        done
      subgoal
        apply (subst trivial_dataflow_topology_interpretation.inv_implications_nonneg_def)
        apply auto      
        unfolding dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt c_imp_the_propagate_all_my_summ c_work_the_propagate_all_my_summ 
        apply auto
        done
      subgoal
        apply (subst trivial_dataflow_topology_interpretation.inv_imp_plus_work_nonneg_def)
        unfolding dataflow_topology_implied_frontier_alt_my_summ propagate_all_preserves_c_pts_alt c_imp_the_propagate_all_my_summ c_work_the_propagate_all_my_summ 
        apply auto
        done
      done
    done
  done

end
