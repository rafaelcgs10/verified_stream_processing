theory Builder_Op

imports
  Progress_Extraction
  "../Lib/Operators_Utils"
begin


(* All timely operators are defined using this function. The logic is passed as argument. This is the only corec we need *)
section \<open>Builder Operator\<close>

corec builder_op where
  \<open>builder_op fb ips ops os logic =
  (choice5
    (if initia os then
      Choice (cimage (\<lambda>os. Silent (builder_op fb ips ops os logic)) (logic os))
    else \<oslash>)
    (Choice (cimage (\<lambda>p. case outpu os p of
      x # xs \<Rightarrow> send_output (builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic) p x)
      (cfilter (\<lambda>p. outpu os p \<noteq> []) ops)))
    (if fb then Read None (\<lambda>x. case x of
      Inl (Inr f) \<Rightarrow> builder_op fb ips ops (os\<lparr>front := f, initia := True\<rparr>) logic
    | _ \<Rightarrow> Code.abort (STR ''Builder_op breaks contract'') (\<lambda>_. \<oslash>))
     else \<oslash>)
    ((Choice (cimage (\<lambda>p. Read (Some p) (\<lambda>x. case x of
      Inr (d, t) \<Rightarrow> builder_op fb ips ops (consumes os p t d) logic
    | Inl _ \<Rightarrow> Code.abort (STR ''Builder_op breaks contract'') (\<lambda> _. \<oslash>))) ips)))
    (let (os', st) = obtain_progress os in send_progress (builder_op fb ips ops os' logic) st)
   )\<close>

thm builder_op.code[of fb inps ops os logic]


lemma
  "builder_op fb inps ops os logic =
Choice
 ((\<lambda>b. case b of
        None \<Rightarrow>
          Choice
           ((\<lambda>b. if b then if initia os then Choice ((\<lambda>os. Silent (builder_op fb inps ops os logic)) |`| logic os) else \<oslash>
                  else Choice ((\<lambda>p. case outpu os p of x # xs \<Rightarrow> trace (STR ''Writing output'') (send_output (builder_op fb inps ops (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic) p x)) |`| cfilter (\<lambda>p. outpu os p \<noteq> []) ops)) |`|
            {|True, False|})
        | Some True \<Rightarrow>
            Choice
             ((\<lambda>b. if b
                    then if fb
                         then Read None
                               (\<lambda>x. case x of Inl (Inl aa) \<Rightarrow> Code.abort STR ''Builder_op breaks contract'' (\<lambda>_. \<oslash>) | Inl (Inr f) \<Rightarrow> trace (STR ''Readingfrontier'') (builder_op fb inps ops (os\<lparr>front := f, initia := True\<rparr>) logic)
                                     | Inr b \<Rightarrow> Code.abort STR ''Builder_op breaks contract'' (\<lambda>_. \<oslash>))
                         else \<oslash>
                    else Choice
                          ((\<lambda>p. Read (Some p) (\<lambda>x. case x of Inl x \<Rightarrow> Code.abort STR ''Builder_op breaks contract'' (\<lambda>_. \<oslash>) | Inr (d, t) \<Rightarrow> builder_op fb inps ops (trace (STR ''Reading data'') (consumes os p t d)) logic)) |`| inps)) |`|
              {|True, False|})
        | Some False \<Rightarrow> let (os', st) = obtain_progress os in trace (STR ''Reporting progress'') (send_progress (builder_op fb inps ops os' logic) st)) |`|
  {|None, Some True, Some False|})"
  unfolding trace_simp
  apply (subst builder_op.code)
  apply simp
  done

subsection \<open>Rules for @{const builder_op}\<close>


lemma step_builder_op_elim:
  assumes \<open>step io (builder_op fb ips ops os logic) op\<close>
  obtains (read_end_None) x where \<open>io = Inp None x\<close> \<open>is_Inr x \<or> is_Inl x \<and> is_Inl (projl x)\<close> \<open>op = \<oslash>\<close>
  | (read_frontier) f where \<open>io = Inp None (Inl (Inr f))\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>front := f, initia := True\<rparr>) logic\<close> \<open>fb\<close>
  | (read_end_Some) p x where \<open>io = Inp (Some p) x\<close> \<open>p |\<in>| ips\<close> \<open>is_Inl x\<close> \<open>op = \<oslash>\<close>
  | (read_data) p d t where \<open>io = Inp (Some p) (Inr (d, t))\<close> \<open>p |\<in>| ips\<close>
    \<open>op = builder_op fb ips ops (consumes os p t d) logic\<close>
  | (write_state) os' st where \<open>io = Out None (Inl (Inl st))\<close> \<open>(os', st) = obtain_progress os\<close>
    \<open>op = builder_op fb ips ops os' logic\<close>
  | (write_data) p x xs where \<open>io = Out (Some p) (Inr x)\<close> \<open>p |\<in>| ops\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic\<close>
  | (silent) os' where \<open>io = Tau\<close> \<open>initia os\<close>
    \<open>os' |\<in>| logic os\<close> \<open>op = builder_op fb ips ops os' logic\<close>
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
        apply (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def split: if_splits list.splits sum.splits)
        done
        thus ?thesis using read_end_None Inp None unexpected by blast
    next
      case frontier
      show ?thesis
      proof (cases \<open>initia os\<close>)
        case True
        hence \<open>fb \<and> op = builder_op fb ips ops (os\<lparr>front := f, initia := True\<rparr>) logic\<close>
          using assms Inp None frontier by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
        thus ?thesis using read_frontier Inp None frontier True by blast
      next
        case False
        hence \<open>fb \<and> op = builder_op fb ips ops (os\<lparr>front := f, initia := True\<rparr>) logic\<close>
          using assms Inp None frontier by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
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
      hence \<open>p' |\<in>| ips \<and> op = \<oslash>\<close> using assms Inp Some by (subst (asm) builder_op.code)
          (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits sum.splits)
      thus ?thesis using read_end_Some Inp Some unexpected by simp
    next
      case data
      hence \<open>p' |\<in>| ips \<and> op = builder_op fb ips ops (consumes os p' t d) logic\<close> using assms Inp Some
        by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
      thus ?thesis using read_data Inp Some data by blast
    qed
  qed
next
  case (Out p x)
  show ?thesis
  proof (cases p)
    case None
    obtain os' st where os'_st: \<open>(os', st) = obtain_progress os\<close> unfolding obtain_progress_def by blast
    hence \<open>x = Inl (Inl st) \<and> op = builder_op fb ips ops os' logic\<close> using assms Out None
      by (subst (asm) builder_op.code) (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
    thus ?thesis using write_state Out None os'_st by blast
  next
    case (Some p')
    then obtain x' xs where x'_xs: \<open>x = Inr x'\<close> \<open>outpu os p' = x' # xs\<close> using assms Out
      apply -
      apply (subst (asm) builder_op.code)
      apply (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
      done
    have \<open>p' |\<in>| ops \<and> op = builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p' := xs)\<rparr>) logic\<close>
      using assms Out Some x'_xs by (subst (asm) builder_op.code)
        (auto 0 0 simp add: drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits list.splits)
    thus ?thesis using write_data Out Some x'_xs by blast
  qed
next
  case Tau
  hence initialized: \<open>initia os\<close> 
    using assms apply -
    apply (subst (asm) builder_op.code)
    apply (auto split: if_splits list.splits prod.splits)
    done
  moreover obtain os' where \<open>os' |\<in>| logic os\<close> \<open>op = builder_op fb ips ops os' logic\<close>
  proof -
    have \<open>Silent op |\<in>| choices (builder_op fb ips ops os logic)\<close> using Tau assms step_choicesE by blast
    thus ?thesis using that
      by (subst (asm) builder_op.code) (auto 0 0 simp add: initialized neq_Nil_conv drop_cap_def drop_caps_def consumes_def obtain_progress_def produces_def produce_def delay_cap_def consume_def mint_cap_def mint_def  split: if_splits)
  qed
  ultimately show ?thesis using silent Tau by blast
qed

 lemma step_builder_op_Read_None[intro]:
  assumes \<open>io = Inp None (Inl (Inr f))\<close> \<open>fb\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>front := f, initia := True\<rparr>) logic\<close>
  shows \<open>step io (builder_op fb ips ops os logic) op\<close>
proof -
  let ?g = \<open>\<lambda>x. case x of Inl (Inr f) \<Rightarrow> builder_op fb ips ops (os\<lparr>front := f,initia := True\<rparr>) logic | _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read None ?g |\<in>| choices (builder_op fb ips ops os logic)\<close> using assms
    by (subst (2) builder_op.code) force
  moreover have \<open>?g (Inl (Inr f)) = op\<close> using assms by simp
  ultimately show ?thesis using assms(1) by blast
qed

lemma step_builder_op_Read_Some[intro]:
  assumes \<open>io = Inp (Some p) (Inr (d, t))\<close> \<open>p |\<in>| ips\<close>
    \<open>op = builder_op fb ips ops (consumes os p t d) logic\<close>
  shows \<open>step io (builder_op fb ips ops os logic) op\<close>
proof -
  let ?f = \<open>\<lambda>x. case x of Inr (d, t) \<Rightarrow> builder_op fb ips ops (consumes os p t d) logic | Inl _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read (Some p) ?f |\<in>| choices (builder_op fb ips ops os logic)\<close> using assms(2,3)
    by (subst (2) builder_op.code) fastforce
  moreover have \<open>?f (Inr (d, t)) = op\<close> using assms by simp
  ultimately show ?thesis using assms(1) by blast
qed

lemma step_builder_op_Write_None[intro]:
  \<open>io = Out None (Inl (Inl st)) \<Longrightarrow>
  (os', st) = obtain_progress os \<Longrightarrow> op = builder_op fb ips ops os' logic \<Longrightarrow>
  step io (builder_op fb ips ops os logic) op\<close>
  by (subst builder_op.code) (auto simp add: has_progress_def obtain_progress_def)

lemma step_builder_op_Write_Some[intro]:
  assumes \<open>io = Out (Some p) (Inr x)\<close> \<open>p |\<in>| ops\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) logic\<close>
  shows \<open>step io (builder_op fb ips ops os logic) op\<close>
  using assms
proof -
  have \<open>send_output op p x |\<in>| choices (builder_op fb ips ops os logic)\<close> using assms(2-)
    by (subst builder_op.code) force
  thus ?thesis using assms(1) by blast
qed

lemma steps_builder_op_Write_Some[intro]:
  assumes \<open>p |\<in>| ops\<close> \<open>outpu os p = xs @ ys\<close>
    \<open>op = builder_op fb ips ops (os\<lparr>outpu := (outpu os)(p := ys)\<rparr>) logic\<close> \<open>zs = map (\<lambda> x. Out (Some p) (Inr x)) xs\<close>
  shows \<open>steps zs (builder_op fb ips ops os logic) op\<close>
  using assms apply -
  apply hypsubst_thin
  apply (induct xs arbitrary: os logic op ys rule: rev_induct)
  apply auto[1]
  apply fastforce
  done

lemma steps_builder_op_Read_Some[intro]:
  assumes \<open>p |\<in>| ips\<close> 
    \<open>op = builder_op fb ips ops (fold (\<lambda> (d, t) os. consumes os p t d) xs os) logic\<close>
  shows \<open>steps (map (\<lambda> x. Inp (Some p) (Inr x)) xs) (builder_op fb ips ops os logic) op\<close>
  using assms apply -
  apply (induct xs arbitrary: os op)
   apply auto[1]
  apply fastforce
  done

lemma step_builder_op_Silent[intro]:
  assumes \<open>io = Tau\<close> \<open>initia os\<close> \<open>os' |\<in>| logic os\<close>
    \<open>op = builder_op fb ips ops os' logic\<close>
  shows \<open>step io (builder_op fb ips ops os logic) op\<close>
proof -
  have \<open>Silent op |\<in>| choices (builder_op fb ips ops os logic)\<close> using assms(2-)
    by (subst builder_op.code) auto
  thus ?thesis using assms(1) by blast
qed

lemma step_builder_op_n_Silents[intro]:
  assumes 
    \<open>os' |\<in>| ((\<lambda> oss. (cUnion (cimage logic (cfilter (\<lambda> os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) oss)))) ^^ n) {| os |}\<close>
    \<open>op = builder_op fb ips ops os' logic\<close>
  shows \<open>(step Tau ^^ n) (builder_op fb ips ops os logic) op\<close>
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


subsection \<open>Inputs of builder_op\<close>



lemma inputs_builder_op:
  assumes \<open>sub_op (Read p f) (builder_op fb ips ops os logic) n\<close>
  shows \<open>p = None \<or> (\<exists>ip. p = Some ip \<and> ip |\<in>| ips)\<close>
  using assms
proof (induct p \<open>builder_op fb ips ops os logic\<close> arbitrary: fb ips ops os logic rule: sub_op_Read_induct)
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
  \<open>inputs (builder_op fb ips ops os logic) \<subseteq> {p. p = None \<or> (\<exists>ip. p = Some ip \<and> ip |\<in>| ips)}\<close>
  using inputs_builder_op inputs_sub_op_Read subsetI
  by (metis (mono_tags, lifting) mem_Collect_eq)

lemma inputs_builder_op_le_alt[dest!]:
  \<open>p \<in> inputs (builder_op fb ips ops os logic) \<Longrightarrow> p = None \<or> (\<exists>ip. p = Some ip \<and> ip |\<in>| ips)\<close>
  using set_mp[OF inputs_builder_op_le, simplified] by fastforce


definition notifier_op where
  "notifier_op ips ops os logic = (builder_op True ips ops os
   (\<lambda> os. logic os (\<lambda> p. filter (\<lambda> t. \<not> frontier_less_equal (front os p) t) (ocaps os p))))"

end