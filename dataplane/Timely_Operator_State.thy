theory Timely_Operator_State

imports
  Timely_Progress
begin

section \<open>Operator Utilities and Change-Batch Algebra\<close>

text \<open>
  Generic utilities for capabilities, pulling/pushing, and state updates used
  throughout operator-level correctness arguments.
\<close>

abbreviation "delayed_cap c t \<equiv>
  (Cap (time c + abs t) (out c),
  \<lambda> op. Write op None
     (Inl (Inl \<lparr> cons = [],
            inte = [(out c, time c, -1), (out c, time c + abs t, 1)],
            prod = [] \<rparr>)))"

abbreviation "pull i f \<equiv> (Read ((trace (STR ''Reading data'') Some) i)
  (\<lambda> x. case x of
    (Inr (d, t)) \<Rightarrow> Write (f (d, Cap t 0)) None (Inl (Inl \<lparr>  cons = [(i, t, 1)], inte = [(i, t, 1)], prod = [] \<rparr>))
   | _ \<Rightarrow> \<oslash>))"

record ('p, 'd, 't) operator_state =
  intsum :: "'p \<Rightarrow> 'p \<Rightarrow> 't list"
  consu :: "('p \<times> 't \<times> int) list"
  inter :: "('p \<times> 't \<times> int) list"
  produ :: "('p \<times> 't \<times> int) list"
  input :: "'p \<Rightarrow> ('d \<times> 't) list"
  outpu :: "'p \<Rightarrow> ('d \<times> 't) list"
  front :: "'p \<Rightarrow> 't antichain"
  ocaps :: "'p \<Rightarrow> 't list"
  initia :: bool

section \<open>Initial States and Compilation Entry Points\<close>

text \<open>
  Initial control-plane and operator states, graph-to-next-edge extraction, and
  top-level compilation into a wrapped dataflow operator.
\<close>

abbreviation init_op_state where
  "init_op_state su i \<equiv> \<lparr>
   intsum = su,
   consu = [],
   inter = [],
   produ = [],
   input = \<lambda> _. [],
   outpu = \<lambda> _. [],
   front = \<lambda> _. antichain_from_list bots,
   ocaps = \<lambda> _. bots,
   initia = i
   \<rparr>"

definition "default_internal_summary = (\<lambda> p1 p2. if p1 = p2 then [0] else [])"

abbreviation "init_op_states \<equiv> (\<lambda> x. init_op_state default_internal_summary (x = 0))"


record ('p, 'd, 'd1, 't) operator_state_ty = "('p, 'd, 't) operator_state" +
  en1 :: "'d1 \<Rightarrow> 'd" de1 :: "'d \<Rightarrow> 'd1" is_en1 :: "'d \<Rightarrow> bool"
record ('p, 'd, 'd1, 'd2, 't) operator_state_ty2 = "('p, 'd, 'd1, 't) operator_state_ty" +
  en2 :: "'d2 \<Rightarrow> 'd" de2 :: "'d \<Rightarrow> 'd2" is_en2 :: "'d \<Rightarrow> bool"
record ('p, 'd, 'd1, 'd2, 'd3, 't) operator_state_ty3 = "('p, 'd, 'd1, 'd2, 't) operator_state_ty2" +
  en3 :: "'d3 \<Rightarrow> 'd" de3 :: "'d \<Rightarrow> 'd3" is_en3 :: "'d \<Rightarrow> bool"

definition "delay_cap os cap incr = (os\<lparr> inter := inter os @ [(out cap, time cap, -1), (out cap, time cap + incr, 1)] \<rparr>)"

definition "produce os cap batch = (if batch = [] then os else os\<lparr> outpu := (outpu os)(out cap := outpu os (out cap) @ map (\<lambda> x. (x, time cap)) batch), produ := produ os @ [(out cap, time cap, length batch)] \<rparr>)"

definition "consume os p t len = (if len = 0 then os else os\<lparr> consu := consu os @ [(p, t, len)] \<rparr>)"

abbreviation "choice4 op1 op2 op3 op4 \<equiv> choice2 (choice2 op1 op2) (choice2 op3 op4)"

abbreviation "choice5 op1 op2 op3 op4 op5 \<equiv> choice3 (choice2 op1 op2) (choice2 op3 op4) op5"

definition "mint_cap os p t = os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"
definition \<open>mint os caps p t = (if t \<in> set (caps p) then (caps, os) else (caps(p := caps p @ [t]), mint_cap os p t))\<close>

definition "produces os batch = os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"
abbreviation "send_progress op st \<equiv> Write op None (Inl (Inl st))"

definition "obtain_progress os = (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"

definition "drop_cap os cap = os\<lparr> inter := inter os @ [(out cap, time cap, -1)], ocaps := (ocaps os) ((out cap) := remove_last (time cap) (ocaps os (out cap))) \<rparr>"

definition "drop_caps os caps = trace (STR ''Drop caps'')  os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, -1)) caps, ocaps := (\<lambda> p. list_diff (ocaps os p) (map time (filter (\<lambda> cap. out cap = p) caps))) \<rparr>"

definition "add_cap os p t = os\<lparr> inter := inter os @ [(p, t, 1)], ocaps := (ocaps os) (p := ocaps os p @ [t])  \<rparr>"

definition "add_caps os caps = os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, 1)) caps, ocaps := (\<lambda> p. ocaps os p @ map time (filter (\<lambda> cap. out cap = p) caps))  \<rparr>"

definition "consumes os p t d = add_caps (os\<lparr> consu := consu os @ [(p, t, 1)], input := BENQ p (d, t) (input os) \<rparr>) (concat (map (\<lambda> p'. map (\<lambda> t'. Cap (t -+- t') p') (intsum os p p')) enum_class.enum))"


lemma outpu_obtain_progress[simp]:
  "outpu (fst (obtain_progress os)) = outpu os"
  unfolding obtain_progress_def by simp
lemma inter_obtain_progress[simp]:
  "inter (fst (obtain_progress os)) = []"
  unfolding obtain_progress_def by simp
lemma produ_obtain_progress[simp]:
  "produ (fst (obtain_progress os)) = []"
  unfolding obtain_progress_def by simp
lemma consu_obtain_progress[simp]:
  "consu (fst (obtain_progress os)) = []"
  unfolding obtain_progress_def by simp

lemma outpu_consumes[simp]:
  "outpu (consumes os p t d) p' = outpu os p'"
  unfolding consumes_def BENQ_def add_caps_def
  by (auto simp add: operator_state.defs)

lemma consu_add_caps[simp]:
  "consu (add_caps os caps) = consu os"
  unfolding add_caps_def by auto
lemma inter_add_caps[simp]:
  "inter (add_caps os caps) = inter os @ map (\<lambda>cap. (out cap, time cap, 1)) caps"
  unfolding add_caps_def by auto
lemma produ_add_caps[simp]:
  "produ (add_caps os caps) = produ os"
  unfolding add_caps_def by auto
lemma outpu_drop_caps[simp]:
  "outpu (drop_caps os caps) = outpu os"
  unfolding drop_caps_def
  by auto
lemma outpu_drop_cap[simp]:
  "outpu (drop_cap os cap) = outpu os"
  unfolding drop_cap_def
  by auto
lemma outpu_produces[simp]:
  "outpu (produces os batch) = (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch))"
  unfolding produces_def
  by auto
lemma ocaps_produces[simp]:
  "ocaps (produces os batch) = ocaps os"
  unfolding produces_def by auto
lemma inter_produces[simp]:
  "inter (produces os batch) = inter os"
  unfolding produces_def by auto
lemma outpu_fold_consumes[simp]:
  "outpu (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = outpu os"
  by (induct xs arbitrary: os)
    auto
lemma produ_if[simp]:
  "produ (if nid' = nid then os nid\<lparr>front := f\<rparr> else os nid') =
   produ (os nid')"
  by auto
lemma inter_if[simp]:
  "inter (if nid' = nid then os nid\<lparr>front := f\<rparr> else os nid') =
   inter (os nid')"
  by auto
lemma consu_if[simp]:
  "consu (if nid' = nid then os nid\<lparr>front := f\<rparr> else os nid') =
   consu (os nid')"
  by auto


definition extract_progress where
  "extract_progress nid nt st =
    map (\<lambda> (p, t, m). (Loc nid (Trg p), t, -m)) (cons st) @
    map (\<lambda> (p, t, m). (Loc nid (Src p), t, m)) (inte st) @
    List.map_filter (\<lambda> (p, t, m). case_option None (\<lambda> (nid', p'). Some (Loc nid' (Trg p'), t, m)) (nt (nid, p))) (prod st)"



lemma extract_progress_obtain_progress_obtain_progress[simp]:
  "extract_progress nid su (snd (obtain_progress (fst (obtain_progress (os nid))))) = []"
  unfolding obtain_progress_def extract_progress_def
  by auto
lemma intsum_consumes[simp]:
  "intsum (consumes os p t d) = intsum os"
  unfolding consumes_def add_caps_def
  apply auto
  done

lemma input_consumes[simp]:
  "input (consumes os p t d) = (input os)(p := input os p @ [(d, t)])"
  unfolding consumes_def add_caps_def BENQ_def
  by auto
lemma input_fold_consumes:
  "input (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = (input os)(p := input os p @ xs)"
  by (induct xs arbitrary: os)
   auto
lemma operator_state_eqI:
  "intsum os1 = intsum os2 \<Longrightarrow>
   consu os1 = consu os2 \<Longrightarrow>
   inter os1 = inter os2 \<Longrightarrow>
   produ os1 = produ os2 \<Longrightarrow>
   input os1 = input os2 \<Longrightarrow>
   outpu os1 = outpu os2 \<Longrightarrow>
   front os1 = front os2 \<Longrightarrow>
   ocaps os1 = ocaps os2 \<Longrightarrow>
   initia os1 = initia os2 \<Longrightarrow>
   operator_state.more os1 = operator_state.more os2 \<Longrightarrow>
   os1 = os2"
  apply (cases os1; cases os2)
  apply auto
  done

lemma concat_map_map_filter:
  "distinct xs \<Longrightarrow>
   p' \<in> set xs \<Longrightarrow>
   concat (map (\<lambda>x. map ((-+-) t) (filter (\<lambda>xa. x = p') (intsum os p x))) xs) = map ((-+-) t) (intsum os p p')"
  apply (induct xs)
  apply simp
  apply (auto simp add: filter_empty_conv)
  done


lemma ocaps_consumes[simp]:
  "ocaps (consumes os p t d) = (\<lambda> p'. ocaps os p' @ map (\<lambda> t'. t -+- t') (intsum os p p'))"
  unfolding consumes_def add_caps_def
  apply (clarsimp simp add: filter_map split_beta operator_state.defs comp_def map_concat)
  apply (rule ext)+
  apply (clarsimp simp add: enum_class.enum_UNIV enum_class.enum_distinct concat_map_map_filter filter_map split_beta operator_state.defs comp_def map_concat filter_concat)
  done
lemma ocaps_consumes_fold[simp]:
  "ocaps (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = (\<lambda> p'. ocaps os p' @ concat (map (\<lambda> (d, t). map (\<lambda> t'. t -+- t') (intsum os p p')) xs))"
  by (induct xs arbitrary: os)
   auto


lemma consu_consumes[simp]:
  "consu (consumes os p t d) = consu os @ [(p, t, 1)]"
  unfolding consumes_def BENQ_def add_caps_def
  apply auto
  done

lemma produ_consumes[simp]:
  "produ (consumes os p t d) = produ os"
  unfolding consumes_def BENQ_def add_caps_def
  by auto

lemma inter_consumes[simp]:
  "inter (consumes os p t d) = inter os @ concat (map (\<lambda> p'. map (\<lambda> t'. (p', t -+- t', 1)) (intsum os p p')) enum_class.enum)"
  unfolding consumes_def BENQ_def add_caps_def
  by (auto simp add: map_concat comp_def)

lemma front_consumes[simp]:
  "front (consumes os p t d) p' = front os p'"
  unfolding consumes_def add_caps_def
  apply auto
  done

lemma initia_consumes[simp]:
  "initia (consumes os p t d) = initia os"
  unfolding consumes_def add_caps_def
  apply auto
  done

lemma more_consumes[simp]:
  "operator_state.more (consumes os p t d) = operator_state.more os"
  unfolding consumes_def add_caps_def
  apply auto
  done

lemma front_consumes_fold[simp]:
  "front (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = front os"
  by (induct xs arbitrary: os) auto

lemma initia_consumes_fold[simp]:
  "initia (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = initia os"
  by (induct xs arbitrary: os)
   (auto split: prod.splits)+

lemma more_consumes_fold[simp]:
  "operator_state.more (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = operator_state.more os"
  by (induct xs arbitrary: os)
   (auto split: prod.splits)+

lemma inter_consumes_fold:
  "inter (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = inter os @ concat (map (\<lambda> (d, t). concat (map (\<lambda> p'. map (\<lambda> t'. (p',  t -+- t', 1)) (intsum os p p')) enum_class.enum)) xs)"
  by (induct xs arbitrary: os)
    auto

lemma consu_consumes_fold:
  "consu (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = consu os @ map (\<lambda> (d, t). (p, t, 1)) xs"
  by (induct xs arbitrary: os)
   auto
lemma intsum_consumes_fold:
  "intsum (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = intsum os"
  by (induct xs arbitrary: os)
   auto
lemma produ_consumes_fold:
  "produ (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = produ os"
  by (induct xs arbitrary: os)
   auto
lemma en1_consumes[simp]:
  "en1 (consumes os p t d) = en1 os"
  unfolding consumes_def add_caps_def
  by auto
lemma en2_consumes[simp]:
  "en2 (consumes os p t d) = en2 os"
  unfolding consumes_def add_caps_def
  by auto

lemma de1_consumes[simp]:
  "de1 (consumes os p t d) = de1 os"
  unfolding consumes_def add_caps_def
  by auto
lemma de2_consumes[simp]:
  "de2 (consumes os p t d) = de2 os"
  unfolding consumes_def add_caps_def
  by auto

lemma fold_consumes:
  "fold (\<lambda>(d, t) os. consumes os p t d) xs os =
   os\<lparr> input := (input os)(p := input os p @ xs), consu := consu os @ map (\<lambda>(d, t). (p, t, 1)) xs , inter := inter os @ concat (map (\<lambda> (d, t). concat (map (\<lambda> p'. map (\<lambda> t'. (p',  t -+- t', 1)) (intsum os p p')) enum_class.enum)) xs), ocaps := (\<lambda> p'. ocaps os p' @ concat (map (\<lambda> (d, t). map (\<lambda> t'. t -+- t') (intsum os p p')) xs)) \<rparr>"
  apply (rule operator_state_eqI)
  apply (auto simp add: intsum_consumes_fold consu_consumes_fold produ_consumes_fold input_fold_consumes inter_consumes_fold)
  done

lemma en1_fold_consumes[simp]:
  "en1 (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = en1 os"
  by (induct xs arbitrary: os) auto
lemma en2_fold_consumes[simp]:
  "en2 (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = en2 os"
  by (induct xs arbitrary: os) auto

lemma de1_fold_consumes[simp]:
  "de1 (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = de1 os"
  by (induct xs arbitrary: os) auto
lemma de2_fold_consumes[simp]:
  "de2 (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = de2 os"
  by (induct xs arbitrary: os) auto

section \<open>Implied-Frontier Reasoning\<close>

text \<open>
  Introduction/elimination and transport lemmas for relating local frontiers and
  implied frontiers across graph paths.
\<close>

lemma frontier_less_equal_ifrontierI:
  "dataflow_topology su (-+-) \<Longrightarrow>
   t' \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (frontier (c_pts c l)) t \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') (t + t')"
  apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_less_equal_sumI[where l=l])
     apply simp_all
   apply (simp add: sum_nonneg zcount_sum)
  apply (rule frontier_less_equal_sumI[of _ _ t'])
     apply simp_all
  using member_antichain.rep_eq apply blast
  unfolding frontier_less_equal_iff2
  apply clarsimp
  subgoal for t''
    apply (rule exI[of _ "t'' + t'"])
    apply clarsimp
    apply (rule in_frontierI)
     apply auto
     apply (metis frontier_idempotent in_frontier_iff pos_zcount_image_zmset zmset_of_mset_set_ge_zero)
    apply (metis (no_types, lifting) add_less_cancel_right dataflow_topology_from_tree.in_frontier_least frontier_idempotent pos_image_zmset_obtain_pre zmset_of_mset_set_ge_zero)
    done
  done

lemma in_frontier_zmset_image:
  "(\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   t \<in>\<^sub>A frontier {#t -+- s. t \<in>#\<^sub>z M#} \<longleftrightarrow> (\<exists> t'. t = t' -+- s \<and> t' \<in>\<^sub>A frontier M)"
  apply transfer
  apply (auto simp add: minimal_antichain_def)
    apply (metis (no_types, lifting) add_strict_right_mono pos_image_zmset_obtain_pre pos_zcount_image_zmset)
   apply (meson pos_zcount_image_zmset)
  apply (metis add_less_cancel_right pos_image_zmset_obtain_pre)
  done

lemma frontier_less_equal_ifrontierE:
  "frontier_less_equal (ifrontier su (-+-) c l') t \<Longrightarrow> 
   dataflow_topology su (-+-) \<Longrightarrow>
   \<exists> l s t'. s \<in>\<^sub>A graph.path_weight su l l' \<and> frontier_less_equal (frontier (c_pts c l)) t' \<and> t = t' + s"
  apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply simp_all
  apply (drule frontier_less_equal_sumE)
   apply clarsimp+
  apply (drule frontier_less_equal_sumE)
   apply clarsimp+
  subgoal for l s
    apply (rule exI[of _ l])
    apply (rule exI[of _ s])
    apply (intro conjI)
    using member_antichain.rep_eq apply blast
    subgoal premises prems
      using prems(3) apply -
      unfolding frontier_less_equal_iff2
      apply (clarsimp simp add: in_frontier_zmset_image)
      apply (metis add.commute add.left_commute dataflow_topology_from_tree.le_plus(2) less_eqE)
      done
    done
  done


lemma frontier_le_image_gen:
  "frontier M \<le> frontier M' \<Longrightarrow>
   (\<forall> t. zcount M' t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   s \<le> s' \<Longrightarrow>
   frontier {#t -+- s. t \<in>#\<^sub>z M#} \<le> frontier {#t -+- s'. t \<in>#\<^sub>z M'#}"
  unfolding less_eq_antichain_def
  apply clarsimp
  apply (metis dataflow_topology_from_tree.results_in_mono_raw in_frontier_zmset_image)
  done

lemma sum_zmset:
  "finite S \<Longrightarrow>
   (\<Sum>s\<in>S. {#t -+- s#}\<^sub>z) = zmset_of (mset_set (((-+-) t) ` S))"
  apply (induct S rule: finite_induct)
   apply simp_all
  subgoal for x S
    by (metis (no_types, lifting) add_left_imp_eq finite_imageI imageE mset_set.insert zmset_of_add_mset)
  done


lemma frontier_less_equal_ifrontier_trans:
  "dataflow_topology su (-+-) \<Longrightarrow>
   t' \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) t \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') (t -+- t')"
  apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (drule frontier_less_equal_ifrontierE)
   apply assumption
  apply clarsimp+
  subgoal for l' s t''
    apply (frule Graph.graph.path_weight_elem_trans[rotated, of s])
      apply assumption+
    using dataflow_topology.axioms(1) apply blast
    apply clarsimp
    subgoal for u
      apply (rule frontier_less_equal_sumI[of _ _ l'])
         apply (simp_all add: sum_nonneg zcount_sum)
      apply (rule frontier_less_equal_sumI[of _ _ u])
         apply (simp_all add: sum_nonneg zcount_sum)
      using member_antichain.rep_eq apply blast
      unfolding frontier_less_equal_iff2
      apply (clarsimp simp add: in_frontier_zmset_image)
      apply (metis dataflow_topology_from_tree.plus_mono group_cancel.add1)
      done
    done
  done

lemma frontier_less_equal_ifrontier_trans_alt2:
  "dataflow_topology su (-+-) \<Longrightarrow>
   s \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) t \<Longrightarrow>
   t -+- s \<le> t' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') t'"
  using frontier_less_equal_ifrontier_trans frontier_less_equal_trans by blast


lemma frontier_le_image:
  "frontier M \<le> frontier M' \<Longrightarrow>
   (\<forall> t. zcount M' t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   frontier {#t -+- s. t \<in>#\<^sub>z M#} \<le> frontier {#t -+- s. t \<in>#\<^sub>z M'#}"
  unfolding less_eq_antichain_def
  apply clarsimp
  apply (metis add.commute add_left_mono in_frontier_zmset_image)
  done

lemma ifrontier_le_all_le:
  "dataflow_topology su (-+-) \<Longrightarrow>
   (\<forall> l' t'. t' \<in>\<^sub>A graph.path_weight su l' l \<longrightarrow> frontier (c_pts c l') \<le> frontier (c_pts c' l')) \<Longrightarrow>
   ifrontier su (-+-) c l \<le> ifrontier su (-+-) c' l"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_sum_le)
    apply simp_all
  subgoal
    apply (intro allI)
    apply (rule frontier_sum_le)
      apply simp_all
    subgoal for loc'
      apply (intro ballI)
      subgoal for s
        apply (drule spec[of _ loc'])
        apply (drule mp)
        using set_antichain1 apply blast
        apply (rule frontier_le_image)
          apply simp_all
        done
      done
    done
  subgoal
    by (simp add: sum_nonneg zcount_sum)
  done

lemma ifrontier_eq_all_le:
  "dataflow_topology su (-+-) \<Longrightarrow>
   (\<forall> l' t'. t' \<in>\<^sub>A graph.path_weight su l' l \<longrightarrow> frontier (c_pts c l') = frontier (c_pts c' l')) \<Longrightarrow>
   ifrontier su (-+-) c l = ifrontier su (-+-) c' l"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_sum_eq)
     apply (simp_all add: sum_nonneg zcount_sum)
  apply (metis dataflow_topology_from_tree.elems_eq_sum_eq member_antichain.rep_eq)
  done

section \<open>Auxiliary Progress and Path Decomposition Lemmas\<close>

text \<open>
  Supporting lemmas for append-splitting of extracted progress, pointstamp arithmetic,
  and decomposition of membership in extracted change batches.
\<close>



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

definition "graph_to_nxt summary =
  (\<lambda> (nid, p). find (\<lambda> (nid', p'). \<not> is_empty_antichain (summary (Loc nid (Src p)) (Loc nid' (Trg p')))) Enum.enum)"

abbreviation initial_conf where
  "initial_conf \<equiv> \<lparr>c_work = \<lambda> l. if is_Src (port l) then zmset_of (mset_set (set bots)) else {#}\<^sub>z, c_pts = \<lambda> l. if is_Src (port l) then to_zmset bots else {#}\<^sub>z, c_imp = \<lambda> _. {#}\<^sub>z\<rparr>"


end
