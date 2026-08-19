theory Builder_Op

imports
  Operator_State
  "../Lib/Operators_Utils"
begin


(* All timely operators are defined using this function. The logic is passed as argument. This is the only corec we need *)
section \<open>Builder Operator\<close>

(* The auxiliary datatype describes the five kinds of nondeterministic choices
   of builder_op. It lets the corecursive definition present all choices as a
   single flat cset of descriptors, which yields the clean code equation
   builder_op_code below. *)
datatype (discs_sels) ('os, 'p) builder_op_aux =
    builder_Silent_aux 'os
  | builder_Write_aux 'p
  | builder_ReadFrontier_aux
  | builder_ReadData_aux 'p
  | builder_Progress_aux

abbreviation eval_builder_op_aux where
  \<open>eval_builder_op_aux b os aux \<equiv> (case aux of
    builder_Silent_aux os' \<Rightarrow> Silent (b os')
  | builder_Write_aux p \<Rightarrow> (case outpu os p of
      x # xs \<Rightarrow> send_output (b (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>)) p x)
  | builder_ReadFrontier_aux \<Rightarrow> Read None (\<lambda>x. case x of
      Inl (Inr f) \<Rightarrow> b (os\<lparr>front := f, initia := True\<rparr>)
    | _ \<Rightarrow> Code.abort (STR ''Builder_op breaks contract'') (\<lambda>_. \<oslash>))
  | builder_ReadData_aux p \<Rightarrow> Read (Some p) (\<lambda>x. case x of
      Inr (d, t) \<Rightarrow> b (consumes os p t d)
    | Inl _ \<Rightarrow> Code.abort (STR ''Builder_op breaks contract'') (\<lambda> _. \<oslash>))
  | builder_Progress_aux \<Rightarrow> (let (os', st) = obtain_progress os in Write (b os') None (Inl (Inl st))))\<close>

(* Inspired by https://github.com/TimelyDataflow/timely-dataflow/blob/eba4ae5298442cc2475e5ef82277bb135e4a7ea4/timely/src/dataflow/operators/generic/builder_rc.rs#L27 *)
corec builder_op where
  \<open>builder_op fb tps sps os logic =
  Choice (cimage (eval_builder_op_aux (\<lambda>os'. builder_op fb tps sps os' logic) os) (cUn (cUn (cUn (cUn
    (if initia os then cimage (\<lambda>os'. builder_Silent_aux
       (os'\<lparr>front := front os, initia := initia os\<rparr>)) (logic os) else {||})
    (cimage builder_Write_aux (cfilter (\<lambda>p. outpu os p \<noteq> []) sps)))
    (if fb then {|builder_ReadFrontier_aux|} else {||}))
    (cimage builder_ReadData_aux tps))
    {|builder_Progress_aux|}))\<close>

lemma builder_op_code:
  \<open>builder_op fb tps sps os logic = Choice (cUn (cUn (cUn (cUn
    (if initia os then cimage (\<lambda>os'. Silent (builder_op fb tps sps
       (os'\<lparr>front := front os, initia := initia os\<rparr>) logic)) (logic os) else {||})
    (cimage (\<lambda>p. case outpu os p of
       x # xs \<Rightarrow> send_output (builder_op fb tps sps (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic) p x)
     (cfilter (\<lambda>p. outpu os p \<noteq> []) sps)))
    (if fb then {|Read None (\<lambda>x. case x of
       Inl (Inr f) \<Rightarrow> builder_op fb tps sps (os\<lparr>front := f, initia := True\<rparr>) logic
     | _ \<Rightarrow> Code.abort (STR ''Builder_op breaks contract'') (\<lambda>_. \<oslash>))|} else {||}))
    (cimage (\<lambda>p. Read (Some p) (\<lambda>x. case x of
       Inr (d, t) \<Rightarrow> builder_op fb tps sps (consumes os p t d) logic
     | Inl _ \<Rightarrow> Code.abort (STR ''Builder_op breaks contract'') (\<lambda> _. \<oslash>))) tps))
    {|let (os', st) = obtain_progress os in Write (builder_op fb tps sps os' logic) None (Inl (Inl st))|})\<close>
  apply (subst builder_op.code)
  apply (auto simp add: cset.map_comp o_def cimage_cUn cimage_cinsert split: list.splits)
  done

subsection \<open>Rules for @{const builder_op}\<close>


lemma step_builder_op_elim:
  assumes \<open>step io (builder_op fb tps sps os logic) op\<close>
  obtains (read_end_None) x where \<open>io = Inp None x\<close> \<open>is_Inr x \<or> is_Inl x \<and> is_Inl (projl x)\<close> \<open>op = \<oslash>\<close>
  | (read_frontier) f where \<open>io = Inp None (Inl (Inr f))\<close>
    \<open>op = builder_op fb tps sps (os\<lparr>front := f, initia := True\<rparr>) logic\<close> \<open>fb\<close>
  | (read_end_Some) p x where \<open>io = Inp (Some p) x\<close> \<open>p |\<in>| tps\<close> \<open>is_Inl x\<close> \<open>op = \<oslash>\<close>
  | (read_data) p d t where \<open>io = Inp (Some p) (Inr (d, t))\<close> \<open>p |\<in>| tps\<close>
    \<open>op = builder_op fb tps sps (consumes os p t d) logic\<close>
  | (write_state) os' st where \<open>io = Out None (Inl (Inl st))\<close> \<open>(os', st) = obtain_progress os\<close>
    \<open>op = builder_op fb tps sps os' logic\<close>
  | (write_data) p x xs where \<open>io = Out (Some p) (Inr x)\<close> \<open>p |\<in>| sps\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = builder_op fb tps sps (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic\<close>
  | (silent) os' where \<open>io = Tau\<close> \<open>initia os\<close>
    \<open>os' |\<in>| logic os\<close>
    \<open>op = builder_op fb tps sps (os'\<lparr>front := front os, initia := initia os\<rparr>) logic\<close>
proof (cases io)
  case (Inp p x)
  show ?thesis
  proof (cases p)
    case None
    consider (unexpected) \<open>is_Inr x \<or> is_Inl x \<and> is_Inl (projl x)\<close> | (frontier) f where \<open>x = Inl (Inr f)\<close>
      by (metis is_Inl.simps(1) is_Inr.simps(1) sum.sel(1) sumE)
    thus ?thesis
    proof cases
      case unexpected
      hence \<open>op = \<oslash>\<close> using assms Inp None
        apply -
        apply (subst (asm) builder_op.code)
        apply (auto 0 0 simp add: drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def split: if_splits list.splits sum.splits)
        done
        thus ?thesis using read_end_None Inp None unexpected by blast
    next
      case frontier
      show ?thesis
      proof (cases \<open>initia os\<close>)
        case True
        hence \<open>fb \<and> op = builder_op fb tps sps (os\<lparr>front := f, initia := True\<rparr>) logic\<close>
          using assms Inp None frontier by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def  split: if_splits list.splits)
        thus ?thesis using read_frontier Inp None frontier True by blast
      next
        case False
        hence \<open>fb \<and> op = builder_op fb tps sps (os\<lparr>front := f, initia := True\<rparr>) logic\<close>
          using assms Inp None frontier by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def  split: if_splits list.splits)
        thus ?thesis using read_frontier Inp None frontier False by blast
      qed
    qed
  next
    case (Some p')
    consider (unexpected) \<open>is_Inl x\<close> | (data) d t where \<open>x = Inr (d, t)\<close>
      using is_Inl.simps(1) obj_sumE surj_pair by metis
    thus ?thesis
    proof cases
      case unexpected
      hence \<open>p' |\<in>| tps \<and> op = \<oslash>\<close> using assms Inp Some by (subst (asm) builder_op.code)
          (auto 0 0 simp add: drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def  split: if_splits list.splits sum.splits)
      thus ?thesis using read_end_Some Inp Some unexpected by simp
    next
      case data
      hence \<open>p' |\<in>| tps \<and> op = builder_op fb tps sps (consumes os p' t d) logic\<close> using assms Inp Some
        by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def  split: if_splits list.splits)
      thus ?thesis using read_data Inp Some data by blast
    qed
  qed
next
  case (Out p x)
  show ?thesis
  proof (cases p)
    case None
    obtain os' st where os'_st: \<open>(os', st) = obtain_progress os\<close> unfolding obtain_progress_def by blast
    hence \<open>x = Inl (Inl st) \<and> op = builder_op fb tps sps os' logic\<close> using assms Out None
      by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def  split: if_splits list.splits)
    thus ?thesis using write_state Out None os'_st by blast
  next
    case (Some p')
    then obtain x' xs where x'_xs: \<open>x = Inr x'\<close> \<open>outpu os p' = x' # xs\<close> using assms Out
      apply -
      apply (subst (asm) builder_op.code)
      apply (auto 0 0 simp add: drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def  split: if_splits list.splits)
      done
    have \<open>p' |\<in>| sps \<and> op = builder_op fb tps sps (os\<lparr>outpu := (outpu os)(p' := xs)\<rparr>) logic\<close>
      using assms Out Some x'_xs by (subst (asm) builder_op.code)
        (auto 0 0 simp add: drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def  split: if_splits list.splits)
    thus ?thesis using write_data Out Some x'_xs by blast
  qed
next
  case Tau
  hence initialized: \<open>initia os\<close> 
    using assms apply -
    apply (subst (asm) builder_op.code)
    apply (auto split: if_splits list.splits prod.splits)
    done
  moreover obtain os' where \<open>os' |\<in>| logic os\<close>
    \<open>op = builder_op fb tps sps (os'\<lparr>front := front os, initia := initia os\<rparr>) logic\<close>
  proof -
    have \<open>Silent op |\<in>| choices (builder_op fb tps sps os logic)\<close> using Tau assms step_choicesE by blast
    thus ?thesis using that
      by (subst (asm) builder_op.code) (auto 0 0 simp add: initialized neq_Nil_conv drop_caps_def consumes_def obtain_progress_def produces_def delay_cap_def consume_def  split: if_splits)
  qed
  ultimately show ?thesis using silent Tau by blast
qed

 lemma step_builder_op_Read_None[intro]:
  assumes \<open>io = Inp None (Inl (Inr f))\<close> \<open>fb\<close>
    \<open>op = builder_op fb tps sps (os\<lparr>front := f, initia := True\<rparr>) logic\<close>
  shows \<open>step io (builder_op fb tps sps os logic) op\<close>
proof -
  let ?g = \<open>\<lambda>x. case x of Inl (Inr f) \<Rightarrow> builder_op fb tps sps (os\<lparr>front := f,initia := True\<rparr>) logic | _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read None ?g |\<in>| choices (builder_op fb tps sps os logic)\<close> using assms
    by (subst (2) builder_op.code) force
  moreover have \<open>?g (Inl (Inr f)) = op\<close> using assms by simp
  ultimately show ?thesis using assms(1) by blast
qed

lemma step_builder_op_Read_Some[intro]:
  assumes \<open>io = Inp (Some p) (Inr (d, t))\<close> \<open>p |\<in>| tps\<close>
    \<open>op = builder_op fb tps sps (consumes os p t d) logic\<close>
  shows \<open>step io (builder_op fb tps sps os logic) op\<close>
proof -
  let ?f = \<open>\<lambda>x. case x of Inr (d, t) \<Rightarrow> builder_op fb tps sps (consumes os p t d) logic | Inl _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read (Some p) ?f |\<in>| choices (builder_op fb tps sps os logic)\<close> using assms(2,3)
    by (subst (2) builder_op.code) fastforce
  moreover have \<open>?f (Inr (d, t)) = op\<close> using assms by simp
  ultimately show ?thesis using assms(1) by blast
qed

lemma step_builder_op_Write_None[intro]:
  \<open>io = Out None (Inl (Inl st)) \<Longrightarrow>
  (os', st) = obtain_progress os \<Longrightarrow> op = builder_op fb tps sps os' logic \<Longrightarrow>
  step io (builder_op fb tps sps os logic) op\<close>
  by (subst builder_op.code) (auto simp add: has_progress_def obtain_progress_def)

lemma step_builder_op_Write_Some[intro]:
  assumes \<open>io = Out (Some p) (Inr x)\<close> \<open>p |\<in>| sps\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = builder_op fb tps sps (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic\<close>
  shows \<open>step io (builder_op fb tps sps os logic) op\<close>
  using assms
proof -
  have \<open>send_output op p x |\<in>| choices (builder_op fb tps sps os logic)\<close> using assms(2-)
    by (subst builder_op.code) force
  thus ?thesis using assms(1) by blast
qed

lemma steps_builder_op_Write_Some[intro]:
  assumes \<open>p |\<in>| sps\<close> \<open>outpu os p = xs @ ys\<close>
    \<open>op = builder_op fb tps sps (os\<lparr>outpu := (outpu os)(p := ys)\<rparr>) logic\<close> \<open>zs = map (\<lambda> x. Out (Some p) (Inr x)) xs\<close>
  shows \<open>steps zs (builder_op fb tps sps os logic) op\<close>
  using assms apply -
  apply hypsubst_thin
  apply (induct xs arbitrary: os logic op ys rule: rev_induct)
  apply auto[1]
  apply fastforce
  done

lemma steps_builder_op_Read_Some[intro]:
  assumes \<open>p |\<in>| tps\<close> 
    \<open>op = builder_op fb tps sps (fold (\<lambda> (d, t) os. consumes os p t d) xs os) logic\<close>
  shows \<open>steps (map (\<lambda> x. Inp (Some p) (Inr x)) xs) (builder_op fb tps sps os logic) op\<close>
  using assms apply -
  apply (induct xs arbitrary: os op)
   apply auto[1]
  apply fastforce
  done

lemma step_builder_op_Silent[intro]:
  assumes \<open>io = Tau\<close> \<open>initia os\<close> \<open>os' |\<in>| logic os\<close>
    \<open>op = builder_op fb tps sps (os'\<lparr>front := front os, initia := initia os\<rparr>) logic\<close>
  shows \<open>step io (builder_op fb tps sps os logic) op\<close>
proof -
  have \<open>Silent op |\<in>| choices (builder_op fb tps sps os logic)\<close> using assms(2-)
    by (subst builder_op.code) auto
  thus ?thesis using assms(1) by blast
qed

lemma step_builder_op_n_Silents[intro]:
  assumes 
    \<open>os' |\<in>| ((\<lambda> oss. (cUnion (cimage (\<lambda> os. cimage
       (\<lambda> os''. os''\<lparr>front := front os, initia := initia os\<rparr>) (logic os))
       (cfilter (\<lambda> os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) oss)))) ^^ n) {| os |}\<close>
    \<open>op = builder_op fb tps sps os' logic\<close>
  shows \<open>(step Tau ^^ n) (builder_op fb tps sps os logic) op\<close>
  using assms apply -
  apply (induct n arbitrary: os os' op)
  subgoal
    by auto
  subgoal premises prems for n os os' op
    using prems(2-) apply -
    apply (clarsimp simp flip: cin.rep_eq)
    apply (intro relcomppI)
    apply hypsubst_thin
     apply (rule prems(1)[rotated])
      apply (rule refl)
    defer
     apply (rule step_builder_op_Silent)
    apply simp_all
    done
  done

text \<open>Variant with the collapsed iterate for logics that preserve
@{const front} and @{const initia}.\<close>

lemma step_builder_op_n_Silents_collapse:
  assumes collapse: "\<And>os os'. os' |\<in>| logic os \<Longrightarrow>
      os'\<lparr>front := front os, initia := initia os\<rparr> = os'"
    and "os' |\<in>| ((\<lambda> oss. (cUnion (cimage logic
      (cfilter (\<lambda> os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) oss)))) ^^ n) {| os |}"
    and "op = builder_op fb tps sps os' logic"
  shows "(step Tau ^^ n) (builder_op fb tps sps os logic) op"
  using assms(2,3)
proof (induct n arbitrary: os' op)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc.prems(1) obtain os1 where
    os1: "os1 |\<in>| ((\<lambda> oss. (cUnion (cimage logic
      (cfilter (\<lambda> os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) oss)))) ^^ n) {| os |}"
    and initia: "initia os1" and mem: "os' |\<in>| logic os1"
    by (auto simp flip: cin.rep_eq)
  have IH: "(step Tau ^^ n) (builder_op fb tps sps os logic) (builder_op fb tps sps os1 logic)"
    by (rule Suc.hyps[OF os1 refl])
  have "step Tau (builder_op fb tps sps os1 logic) (builder_op fb tps sps os' logic)"
    apply (rule step_builder_op_Silent)
       apply (rule refl)
      apply (rule initia)
     apply (rule mem)
    apply (simp add: collapse[OF mem])
    done
  then show ?case
    unfolding Suc.prems(2) by (rule relpowp_Suc_I[OF IH])
qed


subsection \<open>The leaf invariant\<close>

text \<open>@{term "nop_leaf k q"} states that the leaf operator @{term q}
answers empty progress writes with a self-loop, answers a re-read of the
frontier it currently knows (@{term k}, if any) with a self-loop, only
emits @{const Inr}-shaped data values, and that all of this is preserved
by every step. A frontier read updates the known frontier.\<close>

coinductive nop_leaf :: "('p \<Rightarrow> 't antichain) option \<Rightarrow>
  ('p option, 'p option, (('p, 't, 'm) shared_state_scheme + ('p \<Rightarrow> 't antichain)) + 'dd \<times> 't) op \<Rightarrow> bool" where
  nop_leafI: "\<lbrakk>
     \<And>st op'. \<not> has_progress st \<Longrightarrow> step (Out None (Inl (Inl st))) q op' \<Longrightarrow> op' = q;
     \<And>F op'. k = Some F \<Longrightarrow> step (Inp None (Inl (Inr F))) q op' \<Longrightarrow> op' = q;
     \<And>op'. step Tau q op' \<Longrightarrow> nop_leaf k op';
     \<And>p v op'. step (Inp (Some p) (Inr v)) q op' \<Longrightarrow> nop_leaf k op';
     \<And>p v op'. step (Out (Some p) v) q op' \<Longrightarrow> is_Inr v \<and> nop_leaf k op';
     \<And>st op'. step (Out None (Inl (Inl st))) q op' \<Longrightarrow> nop_leaf k op';
     \<And>F op'. step (Inp None (Inl (Inr F))) q op' \<Longrightarrow> nop_leaf (Some F) op'
   \<rbrakk> \<Longrightarrow> nop_leaf k q"

lemma nop_leafD_progress_selfloop:
  "nop_leaf k q \<Longrightarrow> \<not> has_progress st \<Longrightarrow> step (Out None (Inl (Inl st))) q op' \<Longrightarrow> op' = q"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_frontier_selfloop:
  "nop_leaf (Some F) q \<Longrightarrow> step (Inp None (Inl (Inr F))) q op' \<Longrightarrow> op' = q"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_Tau:
  "nop_leaf k q \<Longrightarrow> step Tau q op' \<Longrightarrow> nop_leaf k op'"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_data_in:
  "nop_leaf k q \<Longrightarrow> step (Inp (Some p) (Inr v)) q op' \<Longrightarrow> nop_leaf k op'"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_data_out:
  "nop_leaf k q \<Longrightarrow> step (Out (Some p) v) q op' \<Longrightarrow> is_Inr v \<and> nop_leaf k op'"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_progress:
  "nop_leaf k q \<Longrightarrow> step (Out None (Inl (Inl st))) q op' \<Longrightarrow> nop_leaf k op'"
  by (erule nop_leaf.cases) blast

lemma nop_leafD_frontier:
  "nop_leaf k q \<Longrightarrow> step (Inp None (Inl (Inr F))) q op' \<Longrightarrow> nop_leaf (Some F) op'"
  by (erule nop_leaf.cases) blast

subsection \<open>Builder operators satisfy the leaf invariant\<close>

text \<open>The silent case of @{const builder_op} restores @{const front} and
@{const initia} on every state the logic returns, so the invariant holds
for arbitrary logics.\<close>

lemma front_initia_produces[simp]:
  "front (produces os b) = front os"
  "initia (produces os b) = initia os"
  unfolding produces_def by simp_all

lemma front_initia_drop_caps[simp]:
  "front (drop_caps os caps) = front os"
  "initia (drop_caps os caps) = initia os"
  unfolding drop_caps_def by simp_all

lemma front_initia_add_caps[simp]:
  "front (add_caps os caps) = front os"
  "initia (add_caps os caps) = initia os"
  unfolding add_caps_def by simp_all

lemma front_initia_consumes[simp]:
  "front (consumes os p t d) = front os"
  "initia (consumes os p t d) = initia os"
  unfolding consumes_def by simp_all

lemma front_initia_obtain_progress[simp]:
  "front (fst (obtain_progress os)) = front os"
  "initia (fst (obtain_progress os)) = initia os"
  unfolding obtain_progress_def by simp_all

lemma nop_leaf_builder_op:
  assumes "k = None \<or> (\<exists> F. k = Some F \<and> front os = F \<and> initia os)"
  shows "nop_leaf k (builder_op fb tps sps os logic)"
  using assms
proof (coinduction arbitrary: k os)
  case (nop_leaf k os)
  note prem = nop_leaf
  show ?case
    apply (rule exI[of _ "builder_op fb tps sps os logic"])
    apply (rule exI[of _ k])
    apply (intro conjI)
    subgoal by (rule refl)
    subgoal by (rule refl)
    subgoal
      by (intro allI impI, erule step_builder_op_elim)
         (auto dest: obtain_progress_no_progressD[OF sym])
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply (auto simp add: operator_state_front_initia_upd_triv)
      done
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply (auto simp flip: cin.rep_eq)
      done
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply auto
      done
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply auto
      done
    subgoal
      apply (insert prem)
      apply (intro allI impI)
      apply (erule step_builder_op_elim)
      apply auto
      apply (metis front_initia_obtain_progress(1) front_initia_obtain_progress(2) fst_conv)
      done
    subgoal
      by (intro allI impI, erule step_builder_op_elim) auto
    done
qed

subsection \<open>Inputs of builder_op\<close>



lemma inputs_builder_op:
  assumes \<open>sub_op (Read p f) (builder_op fb tps sps os logic) n\<close>
  shows \<open>p = None \<or> (\<exists>ip. p = Some ip \<and> ip |\<in>| tps)\<close>
  using assms
proof (induct p \<open>builder_op fb tps sps os logic\<close> arbitrary: fb tps sps os logic rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Read2 p p' f x d g)
  then show ?case
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Write p p' op' x d g)
  then show ?case
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Silent p op' d)
  then show ?case
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Choice p choices d g)
  then show ?case
  apply -
    apply (subst (asm) (2) builder_op.code)
    apply (auto 0 0 simp add: obtain_progress_def split: if_splits list.splits sum.splits prod.splits)
    apply (meson Suc_lessD lessI)+
    done
qed

lemma inputs_builder_op_le:
  \<open>inputs (builder_op fb tps sps os logic) \<subseteq> {p. p = None \<or> (\<exists>ip. p = Some ip \<and> ip |\<in>| tps)}\<close>
  using inputs_builder_op inputs_sub_op_Read subsetI
  by (metis (mono_tags, lifting) mem_Collect_eq)

lemma inputs_builder_op_le_alt[dest!]:
  \<open>p \<in> inputs (builder_op fb tps sps os logic) \<Longrightarrow> p = None \<or> (\<exists>ip. p = Some ip \<and> ip |\<in>| tps)\<close>
  using set_mp[OF inputs_builder_op_le, simplified] by fastforce


subsection \<open>The Notifier Operator\<close>

(* Inspired by https://github.com/TimelyDataflow/timely-dataflow/blob/eba4ae5298442cc2475e5ef82277bb135e4a7ea4/timely/src/dataflow/operators/generic/notificator.rs#L17 *)
definition notifier_op where
  "notifier_op tps sps os logic = (builder_op True tps sps os
   (\<lambda> os. logic os (\<lambda> p. filter (\<lambda> t. \<not> frontier_less_equal (front os p) t) (ocaps os p))))"

end