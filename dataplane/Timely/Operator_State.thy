theory Operator_State

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.BNA_Operators
  Progress_Tracking.Propagate
  Nondeterministic_Dataflow.Eval
  "HOL-Library.While_Combinator"
  "../Lib/Executable"
  "../Lib/Termination"
  "../Lib/Zero_Cyc_Check"
  "../Lib/Locations"
  "../Lib/DataplaneUtils"
  "../Lib/CsetUtils"
  "../Lib/ZmsetUtils"
  "../Lib/ListUtils"
  Containers.Collection_Order
  "../Lib/AntichainOrder"
  "../Lib/Bots"
  "../Lib/MyMisc"
begin

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

section \<open>State Records\<close>

(* Inspired by https://github.com/TimelyDataflow/timely-dataflow/blob/eba4ae5298442cc2475e5ef82277bb135e4a7ea4/timely/src/progress/change_batch.rs#L16 *)
type_synonym 'a change_batch = "'a list"

(* Inspired by https://github.com/TimelyDataflow/timely-dataflow/blob/eba4ae5298442cc2475e5ef82277bb135e4a7ea4/timely/src/progress/subgraph.rs#L236 *)
record ('id, 'p, 't) subgraph =
  pt_tr :: "(('id, 'p) location, 't) configuration"
  nxt :: "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option"
  summ :: "('id, 'p) location \<Rightarrow> ('id, 'p) location \<Rightarrow> 't antichain"

text \<open>Extension of @{type subgraph} with the bookkeeping needed by the
optimized dataflow wrapper: a per-node flag recording whether the node's
frontier knowledge may be outdated.\<close>

record ('id, 'p, 't) subgraph_opt = "('id, 'p, 't) subgraph" +
  upfro :: "'id \<Rightarrow> bool"

(* Inspired by https://github.com/TimelyDataflow/timely-dataflow/blob/eba4ae5298442cc2475e5ef82277bb135e4a7ea4/timely/src/progress/operate.rs#L185 *)
record ('p, 't) shared_state =
  cons :: "('p \<times> 't \<times> int) change_batch"
  inte :: "('p \<times> 't \<times> int) change_batch"
  prod :: "('p \<times> 't \<times> int) change_batch"

datatype ('p, 't) capability = Cap (time: "'t :: plus") (out: 'p)

abbreviation "delayed_cap c t \<equiv>
  (Cap (time c + abs t) (out c),
  \<lambda> op. Write op None
     (Inl (Inl \<lparr> cons = [],
            inte = [(out c, time c, -1), (out c, time c + abs t, 1)],
            prod = [] \<rparr>)))"

abbreviation "pull i f \<equiv> (Read (Some i)
  (\<lambda> x. case x of
    (Inr (d, t)) \<Rightarrow> Write (f (d, Cap t 0)) None (Inl (Inl \<lparr>  cons = [(i, t, 1)], inte = [(i, t, 1)], prod = [] \<rparr>))
   | _ \<Rightarrow> \<oslash>))"

(* Inspired by https://github.com/TimelyDataflow/timely-dataflow/blob/eba4ae5298442cc2475e5ef82277bb135e4a7ea4/timely/src/progress/subgraph.rs#L605
   and https://github.com/TimelyDataflow/timely-dataflow/blob/eba4ae5298442cc2475e5ef82277bb135e4a7ea4/timely/src/progress/operate.rs#L185 *)
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


section \<open>Typed State Extensions\<close>

record ('p, 'd, 'd1, 't) operator_state_ty = "('p, 'd, 't) operator_state" +
  en1 :: "'d1 \<Rightarrow> 'd" de1 :: "'d \<Rightarrow> 'd1" is_en1 :: "'d \<Rightarrow> bool"
record ('p, 'd, 'd1, 'd2, 't) operator_state_ty2 = "('p, 'd, 'd1, 't) operator_state_ty" +
  en2 :: "'d2 \<Rightarrow> 'd" de2 :: "'d \<Rightarrow> 'd2" is_en2 :: "'d \<Rightarrow> bool"
record ('p, 'd, 'd1, 'd2, 'd3, 't) operator_state_ty3 = "('p, 'd, 'd1, 'd2, 't) operator_state_ty2" +
  en3 :: "'d3 \<Rightarrow> 'd" de3 :: "'d \<Rightarrow> 'd3" is_en3 :: "'d \<Rightarrow> bool"

section \<open>Primitive State Operations\<close>

definition "delay_cap os cap incr = (os\<lparr> inter := inter os @ [(out cap, time cap, -1), (out cap, time cap + incr, 1)] \<rparr>)"

definition "consume os p t len = (if len = 0 then os else os\<lparr> consu := consu os @ [(p, t, len)] \<rparr>)"

abbreviation "choice4 op1 op2 op3 op4 \<equiv> choice2 (choice2 op1 op2) (choice2 op3 op4)"

abbreviation "choice5 op1 op2 op3 op4 op5 \<equiv> choice3 (choice2 op1 op2) (choice2 op3 op4) op5"

definition "produces os batch = os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

definition input_tl where
  \<open>input_tl old_os p = old_os\<lparr>input := (input old_os)(p := tl (input old_os p))\<rparr>\<close>

lemma intsum_input_tl[simp]: "intsum (input_tl os p) = intsum os"
  unfolding input_tl_def by simp
lemma consu_input_tl[simp]: "consu (input_tl os p) = consu os"
  unfolding input_tl_def by simp
lemma inter_input_tl[simp]: "inter (input_tl os p) = inter os"
  unfolding input_tl_def by simp
lemma produ_input_tl[simp]: "produ (input_tl os p) = produ os"
  unfolding input_tl_def by simp
lemma outpu_input_tl[simp]: "outpu (input_tl os p) = outpu os"
  unfolding input_tl_def by simp
lemma front_input_tl[simp]: "front (input_tl os p) = front os"
  unfolding input_tl_def by simp
lemma ocaps_input_tl[simp]: "ocaps (input_tl os p) = ocaps os"
  unfolding input_tl_def by simp
lemma initia_input_tl[simp]: "initia (input_tl os p) = initia os"
  unfolding input_tl_def by simp

abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"

definition "obtain_progress os = (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"

definition "drop_caps os caps = os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, -1)) caps, ocaps := (\<lambda> p. list_diff (ocaps os p) (map time (filter (\<lambda> cap. out cap = p) caps))) \<rparr>"

definition "release_caps os p = (
  let ts = list_diff (ocaps os p) (concat (map (\<lambda> (p', s). (map (((+) s) o snd) (input os p'))) (concat (map (\<lambda> p'. (map (\<lambda> s. (p', s)) (intsum os p' p))) enum_class.enum)))) in
  trace (STR ''Droping: '' + show_nat (length ts)) (drop_caps os (map (\<lambda> t. Cap t p) ts)))"

definition "add_caps os caps = os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, 1)) caps, ocaps := (\<lambda> p. ocaps os p @ map time (filter (\<lambda> cap. out cap = p) caps))  \<rparr>"

lemma drop_caps_singleton:
  \<open>drop_caps os [cap] = os\<lparr> inter := inter os @ [(out cap, time cap, -1)], ocaps := (ocaps os) ((out cap) := remove_last (time cap) (ocaps os (out cap))) \<rparr>\<close>
  unfolding drop_caps_def by (auto simp: fun_eq_iff)

lemma add_caps_singleton:
  \<open>add_caps os [Cap t p] = os\<lparr> inter := inter os @ [(p, t, 1)], ocaps := (ocaps os) (p := ocaps os p @ [t]) \<rparr>\<close>
  unfolding add_caps_def by (auto simp: fun_eq_iff)

definition "consumes os p t d = add_caps (os\<lparr> consu := consu os @ [(p, t, 1)], input := BENQ p (d, t) (input os) \<rparr>) (concat (map (\<lambda> p'. map (\<lambda> t'. Cap (t + t') p') (intsum os p p')) enum_class.enum))"


section \<open>Frame and Simp Rules\<close>

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

subsection \<open>Operator-state extension field preservation\<close>

lemma is_en1_delay_cap[simp]:
  "is_en1 (delay_cap os cap incr) = is_en1 os"
  unfolding delay_cap_def by auto

lemma is_en2_delay_cap[simp]:
  "is_en2 (delay_cap os cap incr) = is_en2 os"
  unfolding delay_cap_def by auto

lemma is_en1_consume[simp]:
  "is_en1 (consume os p t len) = is_en1 os"
  unfolding consume_def by auto

lemma is_en2_consume[simp]:
  "is_en2 (consume os p t len) = is_en2 os"
  unfolding consume_def by auto

lemma is_en1_produces[simp]:
  "is_en1 (produces os batch) = is_en1 os"
  unfolding produces_def by auto

lemma is_en2_produces[simp]:
  "is_en2 (produces os batch) = is_en2 os"
  unfolding produces_def by auto

lemma en1_produces[simp]:
  \<open>en1 (produces os batch) = en1 os\<close>
  unfolding produces_def by auto

lemma de1_produces[simp]:
  \<open>de1 (produces os batch) = de1 os\<close>
  unfolding produces_def by auto

lemma en2_produces[simp]:
  \<open>en2 (produces os batch) = en2 os\<close>
  unfolding produces_def by auto

lemma de2_produces[simp]:
  \<open>de2 (produces os batch) = de2 os\<close>
  unfolding produces_def by auto

lemma initia_produces[simp]:
  \<open>initia (produces os batch) = initia os\<close>
  unfolding produces_def by auto

lemma is_en1_drop_caps[simp]:
  "is_en1 (drop_caps os caps) = is_en1 os"
  unfolding drop_caps_def by auto

lemma is_en2_drop_caps[simp]:
  "is_en2 (drop_caps os caps) = is_en2 os"
  unfolding drop_caps_def by auto

lemma en1_drop_caps[simp]:
  \<open>en1 (drop_caps os caps) = en1 os\<close>
  unfolding drop_caps_def by auto

lemma de1_drop_caps[simp]:
  \<open>de1 (drop_caps os caps) = de1 os\<close>
  unfolding drop_caps_def by auto

lemma en2_drop_caps[simp]:
  \<open>en2 (drop_caps os caps) = en2 os\<close>
  unfolding drop_caps_def by auto

lemma de2_drop_caps[simp]:
  \<open>de2 (drop_caps os caps) = de2 os\<close>
  unfolding drop_caps_def by auto

lemma outpu_release_caps[simp]:
  "outpu (release_caps os p) = outpu os"
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma front_release_caps[simp]:
  "front (release_caps os p) = front os"
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma input_release_caps[simp]:
  "input (release_caps os p) = input os"
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma is_en1_release_caps[simp]:
  "is_en1 (release_caps os p) = is_en1 os"
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma is_en2_release_caps[simp]:
  "is_en2 (release_caps os p) = is_en2 os"
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma en1_release_caps[simp]:
  \<open>en1 (release_caps os p) = en1 os\<close>
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma de1_release_caps[simp]:
  \<open>de1 (release_caps os p) = de1 os\<close>
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma en2_release_caps[simp]:
  \<open>en2 (release_caps os p) = en2 os\<close>
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma de2_release_caps[simp]:
  \<open>de2 (release_caps os p) = de2 os\<close>
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma produ_release_caps[simp]:
  \<open>produ (release_caps os p) = produ os\<close>
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma initia_release_caps[simp]:
  \<open>initia (release_caps os p) = initia os\<close>
  unfolding release_caps_def drop_caps_def Let_def by auto

lemma input_add_caps[simp]:
  "input (add_caps os caps) = input os"
  unfolding add_caps_def by auto

lemma outpu_add_caps[simp]:
  "outpu (add_caps os caps) = outpu os"
  unfolding add_caps_def by auto

lemma front_add_caps[simp]:
  "front (add_caps os caps) = front os"
  unfolding add_caps_def by auto

lemma initia_add_caps[simp]:
  "initia (add_caps os caps) = initia os"
  unfolding add_caps_def by auto

lemma en1_add_caps[simp]:
  "en1 (add_caps os caps) = en1 os"
  unfolding add_caps_def by auto

lemma de1_add_caps[simp]:
  "de1 (add_caps os caps) = de1 os"
  unfolding add_caps_def by auto

lemma is_en1_add_caps[simp]:
  "is_en1 (add_caps os caps) = is_en1 os"
  unfolding add_caps_def by auto

lemma en2_add_caps[simp]:
  "en2 (add_caps os caps) = en2 os"
  unfolding add_caps_def by auto

lemma de2_add_caps[simp]:
  "de2 (add_caps os caps) = de2 os"
  unfolding add_caps_def by auto

lemma is_en2_add_caps[simp]:
  "is_en2 (add_caps os caps) = is_en2 os"
  unfolding add_caps_def by auto

lemma is_en1_consumes[simp]:
  "is_en1 (consumes os p t d) = is_en1 os"
  unfolding consumes_def add_caps_def BENQ_def by auto

lemma is_en2_consumes[simp]:
  "is_en2 (consumes os p t d) = is_en2 os"
  unfolding consumes_def add_caps_def BENQ_def by auto

lemma outpu_consumes_fun[simp]:
  "outpu (consumes os p t d) = outpu os"
  unfolding consumes_def add_caps_def BENQ_def by auto

lemma is_en1_fold_consumes[simp]:
  "is_en1 (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = is_en1 os"
  by (induct xs arbitrary: os) auto

lemma is_en2_fold_consumes[simp]:
  "is_en2 (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = is_en2 os"
  by (induct xs arbitrary: os) auto

lemma is_en1_obtain_progress[simp]:
  "is_en1 (fst (obtain_progress os)) = is_en1 os"
  unfolding obtain_progress_def by auto

lemma is_en2_obtain_progress[simp]:
  "is_en2 (fst (obtain_progress os)) = is_en2 os"
  unfolding obtain_progress_def by auto

lemma en1_input_tl[simp]:
  "en1 (input_tl os p) = en1 os"
  unfolding input_tl_def by auto

lemma de1_input_tl[simp]:
  "de1 (input_tl os p) = de1 os"
  unfolding input_tl_def by auto

lemma is_en1_input_tl[simp]:
  "is_en1 (input_tl os p) = is_en1 os"
  unfolding input_tl_def by auto

lemma en2_input_tl[simp]:
  "en2 (input_tl os p) = en2 os"
  unfolding input_tl_def by auto

lemma de2_input_tl[simp]:
  "de2 (input_tl os p) = de2 os"
  unfolding input_tl_def by auto

lemma is_en2_input_tl[simp]:
  "is_en2 (input_tl os p) = is_en2 os"
  unfolding input_tl_def by auto

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
lemma front_drop_caps[simp]:
  "front (drop_caps os caps) = front os"
  unfolding drop_caps_def
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

lemma intsum_produces[simp]:
  "intsum (produces os batch) = intsum os"
  unfolding produces_def 
  by auto
lemma intsum_add_caps[simp]:
  "intsum (add_caps os caps) = intsum os"
  unfolding add_caps_def by auto
lemma intsum_release_caps[simp]:
  "intsum (release_caps os p) = intsum os"
  unfolding release_caps_def drop_caps_def
  by (auto cong: if_cong)
lemma consu_produces[simp]:
  "consu (produces os batch) = consu os"
  unfolding produces_def 
  by auto

(* Inspired by https://github.com/TimelyDataflow/timely-dataflow/blob/eba4ae5298442cc2475e5ef82277bb135e4a7ea4/timely/src/progress/subgraph.rs#L752 *)
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


lemma input_drop_caps[simp]:
  "input (drop_caps os caps) = input os"
  unfolding drop_caps_def
  by auto

lemma input_produces[simp]:
  "input (produces os batch) = input os"
  unfolding produces_def
  by auto
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
   concat (map (\<lambda>x. map ((+) t) (filter (\<lambda>xa. x = p') (intsum os p x))) xs) = map ((+) t) (intsum os p p')"
  apply (induct xs)
  apply simp
  apply (auto simp add: filter_empty_conv)
  done


lemma ocaps_consumes[simp]:
  "ocaps (consumes os p t d) = (\<lambda> p'. ocaps os p' @ map (\<lambda> t'. t + t') (intsum os p p'))"
  unfolding consumes_def add_caps_def
  apply (clarsimp simp add: filter_map split_beta operator_state.defs comp_def map_concat)
  apply (rule ext)+
  apply (clarsimp simp add: enum_class.enum_UNIV enum_class.enum_distinct concat_map_map_filter filter_map split_beta operator_state.defs comp_def map_concat filter_concat)
  done
lemma ocaps_consumes_fold[simp]:
  "ocaps (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = (\<lambda> p'. ocaps os p' @ concat (map (\<lambda> (d, t). map (\<lambda> t'. t + t') (intsum os p p')) xs))"
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
  "inter (consumes os p t d) = inter os @ concat (map (\<lambda> p'. map (\<lambda> t'. (p', t + t', 1)) (intsum os p p')) enum_class.enum)"
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

lemma intsum_drop_caps[simp]:
  "intsum (drop_caps os caps) = intsum os"
  unfolding drop_caps_def
  by auto
lemma produ_drop_caps[simp]:
  "produ (drop_caps os caps) = produ os"
  unfolding drop_caps_def
  by auto
lemma consu_drop_caps[simp]:
  "consu (drop_caps os caps) = consu os"
  unfolding drop_caps_def
  by auto
lemma initia_drop_caps[simp]:
  "initia (drop_caps os caps) = initia os"
  unfolding drop_caps_def
  by auto

lemma drop_caps_intsum_update[simp]:
  \<open>drop_caps (os\<lparr>intsum := I\<rparr>) caps = (drop_caps os caps)\<lparr>intsum := I\<rparr>\<close>
  unfolding drop_caps_def by simp

lemma drop_caps_consu_update[simp]:
  \<open>drop_caps (os\<lparr>consu := C\<rparr>) caps = (drop_caps os caps)\<lparr>consu := C\<rparr>\<close>
  unfolding drop_caps_def by simp

lemma drop_caps_produ_update[simp]:
  \<open>drop_caps (os\<lparr>produ := P\<rparr>) caps = (drop_caps os caps)\<lparr>produ := P\<rparr>\<close>
  unfolding drop_caps_def by simp

lemma drop_caps_input_update[simp]:
  \<open>drop_caps (os\<lparr>input := I\<rparr>) caps = (drop_caps os caps)\<lparr>input := I\<rparr>\<close>
  unfolding drop_caps_def by simp

lemma drop_caps_outpu_update[simp]:
  \<open>drop_caps (os\<lparr>outpu := outs\<rparr>) caps = (drop_caps os caps)\<lparr>outpu := outs\<rparr>\<close>
  unfolding drop_caps_def by simp



lemma drop_caps_front_update[simp]:
  \<open>drop_caps (os\<lparr>front := F\<rparr>) caps = (drop_caps os caps)\<lparr>front := F\<rparr>\<close>
  unfolding drop_caps_def by simp

lemma drop_caps_initia_update[simp]:
  \<open>drop_caps (os\<lparr>initia := B\<rparr>) caps = (drop_caps os caps)\<lparr>initia := B\<rparr>\<close>
  unfolding drop_caps_def by simp

lemma ocaps_drop_caps_all:
  \<open>ocaps (drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))) p = []\<close>
  \<open>p' \<noteq> p \<Longrightarrow> ocaps (drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))) p' = ocaps os p'\<close>
  unfolding drop_caps_def filter_map by (simp_all add: comp_def filter_True filter_False)

lemma front_produces[simp]:
  "front (produces os batch) = front os"
  unfolding produces_def
  by auto


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
  "inter (fold (\<lambda>(d, t) os. consumes os p t d) xs os) = inter os @ concat (map (\<lambda> (d, t). concat (map (\<lambda> p'. map (\<lambda> t'. (p',  t + t', 1)) (intsum os p p')) enum_class.enum)) xs)"
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
lemma consu_release_caps[simp]:
  "consu (release_caps os p) = consu os"
  unfolding release_caps_def
  by (auto cong: if_cong)


lemma fold_consumes:
  "fold (\<lambda>(d, t) os. consumes os p t d) xs os =
   os\<lparr> input := (input os)(p := input os p @ xs), consu := consu os @ map (\<lambda>(d, t). (p, t, 1)) xs , inter := inter os @ concat (map (\<lambda> (d, t). concat (map (\<lambda> p'. map (\<lambda> t'. (p',  t + t', 1)) (intsum os p p')) enum_class.enum)) xs), ocaps := (\<lambda> p'. ocaps os p' @ concat (map (\<lambda> (d, t). map (\<lambda> t'. t + t') (intsum os p p')) xs)) \<rparr>"
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

definition "has_progress st = (cons st \<noteq> [] \<or> inte st \<noteq> [] \<or> prod st \<noteq> [])"


abbreviation "not_nop sg op \<equiv> (case op of Read (Inl nid) f \<Rightarrow> upfro sg nid | Write _ (Inl _) (Inl (Inl st)) \<Rightarrow> has_progress st | _ \<Rightarrow> True)"

lemma obtain_progress_no_progressD:
  assumes "obtain_progress os = (os', st)" and "\<not> has_progress st"
  shows "os' = os" and "consu os = []" and "inter os = []" and "produ os = []"
proof -
  have os': "os' = os\<lparr> consu := [], inter := [], produ := [] \<rparr>" and
       st: "st = \<lparr> cons = consu os, inte = inter os, prod = produ os \<rparr>"
    using assms(1) unfolding obtain_progress_def by auto
  have e1: "consu os = []" and e2: "inter os = []" and e3: "produ os = []"
    using assms(2) unfolding st has_progress_def by auto
  have "os' = os\<lparr> consu := consu os, inter := inter os, produ := produ os \<rparr>"
    unfolding os' using e1 e2 e3 by simp
  then show "os' = os" by simp
  show "consu os = []" by (rule e1)
  show "inter os = []" by (rule e2)
  show "produ os = []" by (rule e3)
qed

lemma operator_state_front_initia_upd_collapse[simp]:
  "front os' = v \<Longrightarrow> initia os' = b \<Longrightarrow> os'\<lparr> front := v, initia := b \<rparr> = os'"
proof -
  assume "front os' = v" and "initia os' = b"
  then have "os'\<lparr> front := v, initia := b \<rparr> = os'\<lparr> front := front os', initia := initia os' \<rparr>"
    by simp
  then show ?thesis by simp
qed

lemma operator_state_front_initia_upd_triv[simp]:
  "front os = v \<Longrightarrow> initia os \<Longrightarrow> os\<lparr> front := v, initia := True \<rparr> = os"
proof -
  assume "front os = v" and "initia os"
  then have "os\<lparr> front := v, initia := True \<rparr> = os\<lparr> front := front os, initia := initia os \<rparr>"
    by simp
  then show ?thesis by simp
qed

fun delay_nop where
  "delay_nop F 0 xs lxs = xs @@- lxs"
| "delay_nop F n xs LNil = llist_of xs"
| "delay_nop F (Suc n) xs (LCons x lxs) = (if F x then LCons x (delay_nop F n xs lxs) else delay_nop F n (xs @ [x]) lxs)"
declare delay_nop.simps[code del]
declare delay_nop.simps[simp del]

lemma delay_nop_code[code]:
  "delay_nop F n xs lxs =
  (if n = 0 then (xs @@- lxs) else
  (case lxs of LNil \<Rightarrow> llist_of xs | LCons x lxs \<Rightarrow> (if F x then LCons x (delay_nop F (n - 1) xs lxs) else (delay_nop F (n - 1) (xs @ [x]) lxs))))"
  apply (cases n)
  apply (simp_all add: delay_nop.simps split: llist.splits)
  done

definition "delay_cset (F :: ('a, 'b, 'c) op \<Rightarrow> bool) (n :: nat) (C :: (('a, 'b, 'c) op) cset) = C"
declare delay_cset_def[code drop]

lemma delay_cset_code_aux:
  "cUn (delay_cset F n (cset_of_llist lxs)) (cset_from_list xs)  = cset_of_llist (delay_nop F n xs lxs)"
  unfolding delay_cset_def
  apply (induct n arbitrary: lxs xs)
   apply (simp_all add: delay_nop.simps split: llist.splits)
  subgoal for n lxs xs
    apply (cases lxs)
   apply (simp_all add: delay_nop.simps split: llist.splits)
     apply (metis cset_of_llist_lshift shift_LNil)
   apply (auto simp add: delay_nop.simps split: llist.splits simp flip: cin.rep_eq)
    apply (metis cUn_cinsert_left cinsert_code)
    apply (metis cUn_cinsert_left cinsert_code)
    apply (metis cset_of_llist_lshift snoc_shift)
    apply (metis cset_of_llist_lshift snoc_shift)
    done
  done

lemma delay_cset_code[code]:
  "delay_cset F n (cset_of_llist lxs) = cset_of_llist (delay_nop F n [] lxs)"
  by (simp flip: delay_cset_code_aux)





abbreviation "CONSUMES p \<equiv> fold (\<lambda>(d, t) os. consumes os p t d)"

lemma CONSUMES_CONSUMES:
  "CONSUMES p xs (CONSUMES p ys os) =
   CONSUMES p (ys @ xs) os"
  unfolding fold_consumes
  by simp

lemma input_CONSUMES:
  \<open>input (CONSUMES p xs os) = (input os)(p := input os p @ xs)\<close>
  unfolding fold_consumes by simp


definition op_state_base where
  \<open>op_state_base os = \<lparr>
    intsum = intsum os,
    consu = consu os,
    inter = inter os,
    produ = produ os,
    input = input os,
    outpu = outpu os,
    front = front os,
    ocaps = ocaps os,
    initia = initia os\<rparr>\<close>

lemma op_state_base_add_caps[simp]:
  \<open>op_state_base (add_caps os caps) = add_caps (op_state_base os) caps\<close>
  unfolding op_state_base_def add_caps_def
  by (rule operator_state_eqI) (simp_all add: fun_eq_iff)

lemma op_state_base_produces[simp]:
  \<open>op_state_base (produces os batch) = produces (op_state_base os) batch\<close>
  unfolding op_state_base_def produces_def
  by (rule operator_state_eqI) (simp_all add: fun_eq_iff)

lemma op_state_base_drop_caps[simp]:
  \<open>op_state_base (drop_caps os caps) = drop_caps (op_state_base os) caps\<close>
  unfolding op_state_base_def drop_caps_def
  by (rule operator_state_eqI) (simp_all add: fun_eq_iff)

lemma op_state_base_release_caps[simp]:
  \<open>op_state_base (release_caps os p) = release_caps (op_state_base os) p\<close>
  unfolding op_state_base_def release_caps_def drop_caps_def Let_def
  by (rule operator_state_eqI) (simp_all add: trace_simp fun_eq_iff)

lemma op_state_base_outpu_update[simp]:
  \<open>op_state_base (os\<lparr>outpu := outs\<rparr>) = (op_state_base os)\<lparr>outpu := outs\<rparr>\<close>
  unfolding op_state_base_def
  by (rule operator_state_eqI) simp_all

lemma op_state_base_CONSUMES[simp]:
  \<open>op_state_base (CONSUMES p xs os) = CONSUMES p xs (op_state_base os)\<close>
  unfolding op_state_base_def fold_consumes
  by (rule operator_state_eqI) (simp_all add: fun_eq_iff)


lemma op_state_base_front_initia_update[simp]:

\<open>op_state_base (os\<lparr>front := F, initia := I\<rparr>) = (op_state_base os)\<lparr>front := F, initia := I\<rparr>\<close>
  unfolding op_state_base_def
  by (rule operator_state_eqI) simp_all

lemma cap_times_filter_single_port_subset:
  assumes "mset xs \<subseteq># mset (ocaps os p)"
  shows "\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') (map (\<lambda>t. Cap t p) xs))) \<subseteq># mset (ocaps os p')"
proof (intro allI)
  fix p'
  have filt_eq:
    "map capability.time (filter (\<lambda>c. out c = p') (map (\<lambda>t. Cap t p) xs)) =
      (if p' = p then xs else [])"
    by (induct xs) auto
  show "mset (map capability.time (filter (\<lambda>c. out c = p') (map (\<lambda>t. Cap t p) xs))) \<subseteq># mset (ocaps os p')"
    using assms filt_eq by auto
qed

lemma produced_oputs_caps_from_produs:
  assumes "\<forall>(p, t, m) \<in> set (map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) batch).
    m > 0 \<and> t \<in> set (ocaps os p)"
  shows "\<forall>p. snd ` set (map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) batch)) \<subseteq> set (ocaps os p)"
  using assms
  by (auto split: prod.splits)

lemma produced_oputs_produs_zmset:
  "\<forall>p. to_zmset (map snd (map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) batch))) =
    zmset (map snd (filter (\<lambda>x. p = fst x) (map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) batch)))"
  by (induct batch) (auto simp add: split_beta zmset_map_one update_zmultiset_one add.commute split: prod.splits capability.splits)

lemma produces_Nil[simp]:
  "produces os [] = os"
  unfolding produces_def
  by simp

lemma ocaps_drop_caps_port_disjoint[simp]:
  fixes os :: "('p, 'd, 't :: plus, 'more) operator_state_scheme"
    and caps :: "('p, 't) capability list"

assumes "\<And>cap. cap \<in> set caps \<Longrightarrow> out cap \<noteq> p"
shows "ocaps (drop_caps os caps) p = ocaps os p"
proof -
  have "filter (\<lambda>cap. out cap = p) caps = []"
    using assms by (induction caps) auto
  then show ?thesis
    unfolding drop_caps_def by simp
qed
subsection \<open>Consolidated State Laws\<close>

lemma intsum_CONSUMES[simp]:
  \<open>intsum (CONSUMES p xs os) = intsum os\<close>
  by (induct xs arbitrary: os) (auto split: prod.splits)

lemma de1_CONSUMES[simp]:
  \<open>de1 (CONSUMES p xs os) = de1 os\<close>
  by simp

end
