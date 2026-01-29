theory Ooo_Input_op_Correctness

imports
  Ooo_Input_op
begin

lemma timely_input_stream_ooo_input_op_logic:
  assumes \<open>timely_input_stream (es os p) (mset (ocaps os p))\<close> \<open>os' |\<in>| ooo_input_op_logic ops os\<close>
  shows \<open>timely_input_stream (es os' p) (mset (ocaps os' p))\<close>
proof -
  consider (LNil) p' where \<open>es os p' = LNil\<close> \<open>os' = drop_caps os (map (\<lambda>t. Cap t p') (ocaps os p'))\<close>
    \<open>ocaps os p' \<noteq> []\<close>
  | (LCons_Data) p' t d lxs where \<open>es os p' = LCons (Data t d) lxs\<close>
    \<open>os' = produce (os\<lparr>es := (es os)(p' := lxs)\<rparr>) (Cap t p') [en1 os d]\<close>
  | (LCons_Drop) p' t lxs where \<open>es os p' = LCons (Drop t) lxs\<close>
    \<open>os' = drop_cap (os\<lparr>es := (es os)(p' := lxs)\<rparr>) (Cap t p')\<close>
  | (LCons_Mint) p' t lxs where \<open>es os p' = LCons (Mint t) lxs\<close>
    \<open>os' = add_cap (os\<lparr>es := (es os)(p' := lxs)\<rparr>) p' t\<close>
    using assms(2) unfolding ooo_input_op_logic_def by (auto split: llist.splits event.splits)
  thus ?thesis
  proof cases
    case LNil
    show ?thesis
    proof (cases \<open>p = p'\<close>)
      case True
      thus ?thesis using assms(1) LNil(1,3) unfolding timely_input_stream_def by auto
    next
      case False
      then show ?thesis using assms(1) LNil(2) unfolding timely_input_stream_def drop_caps_def by simp
    qed
  next
    case LCons_Data
    thus ?thesis using assms(1) ev_drops.intros(1,2) timely_productive.intros(1)
      unfolding timely_input_stream_def produce_def by fastforce
  next
    case LCons_Drop
    hence \<open>timely_monotone (es os' p) (mset (ocaps os' p))\<close>
      using assms(1) unfolding timely_input_stream_def drop_cap_def by auto
    moreover have \<open>count (mset (ocaps os' p)) t' \<noteq> 0 \<longrightarrow> ev_drops t' (es os' p) (mset (ocaps os' p))\<close> for t'
    proof -
      {
        assume \<open>count (mset (ocaps os' p)) t' \<noteq> 0\<close>
        hence \<open>count (mset (ocaps os p)) t' \<noteq> 0\<close> using LCons_Drop(2) unfolding drop_cap_def
          by (auto split: if_splits dest: set_remove_lastD)
        hence \<open>ev_drops t' (es os p) (mset (ocaps os p))\<close>
          using assms(1) unfolding timely_input_stream_def by blast
        hence \<open>ev_drops t' (es os' p) (mset (ocaps os' p))\<close>
          using LCons_Drop vacant_diff unfolding drop_cap_def by (force intro: ev_drops.intros(1,2))
      }
      thus ?thesis by blast
    qed
    moreover have \<open>timely_productive (es os' p) (mset (ocaps os' p))\<close> using assms(1) LCons_Drop
        timely_productive.intros(1) unfolding timely_input_stream_def drop_cap_def by fastforce
    ultimately show ?thesis unfolding timely_input_stream_def by blast
  next
    case LCons_Mint
    hence \<open>timely_monotone (es os' p) (mset (ocaps os' p))\<close>
      using assms(1) unfolding timely_input_stream_def add_cap_def by auto
    moreover have \<open>count (mset (ocaps os' p)) t' \<noteq> 0 \<longrightarrow> ev_drops t' (es os' p) (mset (ocaps os' p))\<close> for t'
    proof -
      {
        assume \<open>count (mset (ocaps os' p)) t' \<noteq> 0\<close>
        hence \<open>ev_drops t' (es os' p) (mset (ocaps os' p))\<close> using assms(1) LCons_Mint ev_drops.intros(1)
          unfolding timely_input_stream_def add_cap_def by (fastforce simp add: vacant_def)
      }
      thus ?thesis by blast
    qed
    moreover have \<open>timely_productive (es os' p) (mset (ocaps os' p))\<close> using assms(1) LCons_Mint
        timely_productive.intros(1) unfolding timely_input_stream_def add_cap_def by fastforce
    ultimately show ?thesis unfolding timely_input_stream_def by blast
  qed
qed

lemma foldl_ooo_input_os_Drop_Mint:
  assumes \<open>\<forall>e \<in> set xs. \<not> is_Data e\<close> \<open>os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) xs\<close>
  shows \<open>initia os \<Longrightarrow> initia os'\<close> \<open>outpu os' = outpu os\<close> \<open>p' \<noteq> p \<Longrightarrow> ocaps os' p' = ocaps os p'\<close>
    \<open>en1 os' = en1 os\<close> \<open>es os' = (es os)(p := lxs)\<close>
  using assms
proof (induction xs arbitrary: os)
  case (Cons x xs)
  fix os
  assume H1: \<open>\<forall>e \<in> set (x # xs). \<not> is_Data e\<close>
    and H2: \<open>os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (x # xs)\<close>
  let ?os = \<open>ooo_input_os_Drop_Mint p os x\<close>
  have \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) x = ?os\<lparr>es := (es ?os)(p := lxs)\<rparr>\<close>
    using H1 unfolding ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def by (cases x) simp_all (* Why is this much faster than "cases x;simp" ? *)
  hence os'_alt: \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os\<lparr>es := (es ?os)(p := lxs)\<rparr>) xs\<close>
    using H2 unfolding fun_upd_def by simp
  {
    assume \<open>initia os\<close>
    hence \<open>initia ?os\<close>
      using H1 unfolding ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def by (cases x; simp)
    thus \<open>initia os'\<close> using Cons(1) H1 os'_alt by fastforce
  next
    have \<open>outpu ?os = outpu os\<close>
      using H1 unfolding ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def by (cases x; simp)
    thus \<open>outpu os' = outpu os\<close> using Cons(2) H1 os'_alt by fastforce
  next
    assume p': \<open>p' \<noteq> p\<close>
    hence \<open>ocaps ?os p' = ocaps os p'\<close>
      using H1 unfolding ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def by (cases x; simp)
    thus \<open>ocaps os' p' = ocaps os p'\<close> using Cons(3) H1 os'_alt p' by fastforce
  next
    have \<open>en1 ?os = en1 os\<close>
      using H1 unfolding ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def by (cases x; simp)
    thus \<open>en1 os' = en1 os\<close> using Cons(4) H1 os'_alt by fastforce
  next
    have \<open>(es ?os)(p := lxs) = (es os)(p := lxs)\<close>
      using H1 unfolding ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def by (cases x; simp)
    thus \<open>es os' = (es os)(p := lxs)\<close> using Cons(5) H1 os'_alt by fastforce
  }
qed simp_all

lemma timely_input_stream_foldl_ooo_input_os_Drop_Mint:
  \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os (p :: _ :: {countable}))) \<Longrightarrow>
  ldropWhile (Not \<circ> is_Data) (es os p) = LCons e lxs \<Longrightarrow>
  timely_input_stream (es os p) (mset (ocaps os p)) \<Longrightarrow>
  os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es os p))) \<Longrightarrow>
  timely_input_stream lxs (mset (ocaps os' p))\<close>
proof (induction \<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os p))\<close> arbitrary: os)
  case Nil
  have \<open>os' = os\<lparr>es := (es os)(p := lxs)\<rparr>\<close> using Nil(1,5) foldl.simps(1) by metis
  hence ocaps_os': \<open>ocaps os' p = ocaps os p\<close> by simp
  moreover have es_os: \<open>es os p = LCons e lxs\<close> using Nil(1-3) ldropWhile_LCons ldropWhile_simps(1)
      llist.exhaust_sel llist_of.simps(1) llist_of_list_of ltakeWhile_eq_LNil_iff by metis
  moreover have \<open>is_Data e\<close> using Nil(3) ldropWhile_LConsD by fastforce
  ultimately show ?case using Nil(4) unfolding timely_input_stream_def
    by (auto intro: ev_drops.intros(1,2) timely_productive.intros(1))
next
  case (Cons x xs)
  have \<open>\<not> lnull (es os p)\<close> using Cons(4) eq_LConsD ldropWhile_LNil llist.collapse(1) by metis
  hence lhd_LCons_ltl_es: \<open>LCons (lhd (es os p)) (ltl (es os p)) = es os p\<close> by (rule lhd_LCons_ltl)
  have lhd_es: \<open>\<not> is_Data x\<close> \<open>lhd (es os p) = x\<close> using Cons(2,3) comp_apply eq_LConsD llist_of.simps(2)
      llist_of_list_of ltakeWhile.ctr(1) ltakeWhile.sel(1) by (metis (no_types, opaque_lifting))+
  let ?os = \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) x\<close>
  have \<open>xs = list_of (ltakeWhile (Not \<circ> is_Data) (es ?os p))\<close> using Cons(2,3) lhd_es(1)
    by (cases x; simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def; metis lhd_es list.sel(3) ltl_ltakeWhile tl_list_of)
  moreover have \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es ?os p))\<close> using Cons(3) lhd_es
    by (cases x; simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def)
      (metis lfinite_ltl ltl_ltakeWhile event.disc(2), metis lfinite_ltl ltl_ltakeWhile event.disc(3))
  moreover have \<open>ldropWhile (Not \<circ> is_Data) (es ?os p) = LCons e lxs\<close> using Cons(4) lhd_LCons_ltl_es
      lhd_es ldropWhile_simps(2) by (cases x; simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def; metis)
  moreover have \<open>timely_input_stream (es ?os p) (mset (ocaps ?os p))\<close>
  proof -
    have \<open>ocaps os p \<noteq> []\<close>
      using Cons(5) lhd_LCons_ltl_es timely_input_stream_LCons_not_empty mset_zero_iff by metis
    hence \<open>?os |\<in>| ooo_input_op_logic cUNIV os\<close>
      using lhd_LCons_ltl_es lhd_es unfolding ooo_input_os_Drop_Mint_def ooo_input_op_logic_def
      by (auto split: llist.splits event.splits simp add: image_iff)
    thus ?thesis using Cons(5) timely_input_stream_ooo_input_op_logic by fast
  qed
  moreover have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os\<lparr>es := (es ?os)(p := lxs)\<rparr>)
  (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os p)))\<close>
  proof -
    have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>)
  (list_of (ltakeWhile (Not \<circ> is_Data) (LCons x (ltl (es os p)))))\<close>
      using Cons(6) lhd_LCons_ltl_es lhd_es(2) by simp
    also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>)
  (list_of (LCons x (ltakeWhile (Not \<circ> is_Data) (ltl (es os p)))))\<close> using lhd_es(1) by simp
    also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>)
  (x # list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p))))\<close>
      using Cons(3) list_of_LCons lfinite_ltl lhd_es comp_apply event.disc(2) ltl_ltakeWhile
      by (smt (z3))
    also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p)
  (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) x)
  (list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p))))\<close> by simp
    finally show ?thesis using lhd_es(1)
      by (auto intro: arg_cong[where f=\<open>\<lambda>os. foldl _ os _\<close>] simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def split: event.splits)
  qed
  ultimately show ?case using Cons(1) by blast
qed

lemma step_Taus_ooo_input_op_Drop_Mint:
  \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os p)) \<Longrightarrow>
  ldropWhile (Not \<circ> is_Data) (es os p) = LCons (Data t d) lxs \<Longrightarrow> p |\<in>| ops \<Longrightarrow>
  op = ooo_input_op ops os \<Longrightarrow> initia os \<Longrightarrow> timely_monotone (es os p) (mset (ocaps os p)) \<Longrightarrow>
  os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es os p))) \<Longrightarrow>
  os'' = produce os' (Cap t p) [en1 os' d] \<Longrightarrow> op' = ooo_input_op ops os'' \<Longrightarrow>
  (step Tau)\<^sup>*\<^sup>* op op'\<close>
  unfolding ooo_input_op_def
proof (induction \<open>ltakeWhile (Not \<circ> is_Data) (es os p)\<close> arbitrary: os op rule: lfinite_induct)
  case LNil
  have \<open>ldropWhile (Not \<circ> is_Data) (es os p) = es os p\<close> using LNil(1) ldropWhile_LCons
      ldropWhile_LNil llist.sel(1) lnull_def ltakeWhile_eq_LNil_iff neq_LNil_conv by metis
  moreover from this have ocaps_not_empty: \<open>ocaps os p \<noteq> []\<close> using LNil(2,6) timely_monotone.cases
    by force
  ultimately have \<open>os'' |\<in>| ooo_input_op_logic ops os\<close> using LNil(2,3,7,8) ooo_input_op_logic_def
    by force
  thus ?case using LNil(4,5,9) ocaps_not_empty step_builder_op_Silent ooo_input_op_def by blast
next
  case LCons
  obtain e where lhd_es: \<open>\<not> is_Data e\<close> \<open>lhd (es os p) = e\<close> \<open>es os p = LCons e (ltl (es os p))\<close>
    using LCons(2) by fastforce
  let ?os1 = \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) e\<close>
  have ocaps_not_empty: \<open>ocaps os p \<noteq> []\<close> using LCons(8) lhd_es(3) timely_monotone.cases by force
  hence \<open>?os1 |\<in>| ooo_input_op_logic ops os\<close> unfolding ooo_input_op_logic_def ooo_input_os_Drop_Mint_def
    using LCons(5) lhd_es(1,3) event.case_eq_if llist.case(2) cin_cimage_cfilter input_state.fold_congs(13)
      operator_state.unfold_congs input_state.fold_congs(14) by (smt (verit, ccfv_SIG))
  hence \<open>step Tau op (ooo_input_op ops ?os1)\<close>
    using LCons(6,7) ocaps_not_empty step_builder_op_Silent ooo_input_op_def by blast
  moreover have \<open>(step Tau)\<^sup>*\<^sup>* (ooo_input_op ops ?os1) op'\<close>
  proof -
    have es_os1: \<open>es ?os1 p = ltl (es os p)\<close> using lhd_es(1)
      by (auto simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def split: event.splits)
    hence \<open>ltl (ltakeWhile (Not \<circ> is_Data) (es os p)) = ltakeWhile (Not \<circ> is_Data) (es ?os1 p)\<close>
      using LCons(2) lnull_ltakeWhile ltakeWhile.simps(4) by force
    moreover from this have \<open>ldropWhile (Not \<circ> is_Data) (es ?os1 p) = LCons (Data t d) lxs\<close>
      using LCons(2,4) es_os1 ldropWhile_simps(2) lhd_LCons_ltl ltakeWhile.disc(1) by metis
    moreover have \<open>initia ?os1\<close> using LCons(7) lhd_es(1)
      by (auto simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def split: event.splits)
    moreover have \<open>timely_monotone (es ?os1 p) (mset (ocaps ?os1 p))\<close>
    proof (cases e)
      case Data
      thus ?thesis using lhd_es(1) by simp
    next
      case (Drop t')
      hence \<open>ocaps (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) e) p = remove_last t' (ocaps os p)\<close>
        by (simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def)
      thus ?thesis using Drop LCons(8) ocaps_not_empty lhd_es(3) es_os1 timely_monotone.cases
          mset_remove_last event.distinct(2,5) event.inject(2) llist.simps(1) mset_zero_iff
        by (smt (verit, ccfv_threshold))
    next
      case (Mint t')
      hence \<open>ocaps (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) e) p = ocaps os p @ [t']\<close>
        by (simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def)
      thus ?thesis using Mint LCons(8) lhd_es(3) es_os1 timely_monotone.cases by fastforce
    qed
    moreover have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os1\<lparr>es := (es ?os1)(p := lxs)\<rparr>)
  (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p)))\<close>
    proof -
      have \<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os p)) = e # list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p))\<close>
        using LCons(1) lhd_es es_os1 ltakeWhile.ctr(2) not_lnull_conv by fastforce
      hence \<open>os' = foldl (ooo_input_os_Drop_Mint p)
  (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) e)
  (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p)))\<close> using LCons(9) by (simp split: event.splits)
      moreover have \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) e = ?os1\<lparr>es := (es ?os1)(p := lxs)\<rparr>\<close>
        using lhd_es(1) by (auto simp add: ooo_input_os_Drop_Mint_def add_cap_def drop_cap_def split: event.splits)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis using LCons(3,5,10,11) ooo_input_op_def by blast
  qed
  ultimately show ?case by (rule transitive_closurep_trans'(6))
qed

(* Experiment with Eisbach. *)
method sim_cases uses defs elims intros =
  ((unfold defs)?, elim conjE elims; simp only: IO.simps; hypsubst_thin?; auto intro: intros simp flip: defs)

lemma ooo_input_op_source_op:
  defines \<open>invariant f os \<equiv> initia os \<and> en1 os = f \<and> inj f \<and> (\<forall>p. timely_input_stream (es os p) (mset (ocaps os p)))\<close>
    and \<open>my_ooo_input_op os \<equiv> map_op
  (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0 :: 1, p))) (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0 :: 1, p)))
  (ooo_input_op c\<UU> os)\<close>
    and \<open>my_source_op f os \<equiv> map_op (\<lambda>p. (0, p)) (\<lambda>p. (0, p))
  (source_op (\<lambda>p. outpu os p @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os p))))\<close>
  assumes \<open>invariant f os\<close>
  shows \<open>dataflow_op sg (my_ooo_input_op os) \<approx> my_source_op f os\<close>
  using assms(4)
proof (coinduction arbitrary: sg os rule: wbisim_coinduct_upto'')
  case SIM1
  show ?case (is \<open>\<exists>_. _ \<and> wbisim_cong ?R _ _\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    have invariant_initia: \<open>invariant f os \<Longrightarrow> initia os\<close> unfolding invariant_def by blast
    show ?thesis
    proof -
      have "\<exists>op2'. wstep (Out (1, p) (d, t)) (my_source_op f os) op2'
  \<and> wbisim_cong R (dataflow_op sg (my_ooo_input_op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>))) op2'"
        if "invariant f os"
          and "outpu os p = (d, t) # xs"
          and "p \<notin> defaults"
        for p :: 'c
          and d :: 'b
          and t :: 'd
          and xs :: "('b \<times> 'd) buf"
      proof -
        let ?os' = \<open>os\<lparr>outpu := (outpu os)(p := xs)\<rparr>\<close>
        have \<open>step (Out p (d, t))
  (source_op (\<lambda>p. outpu os p @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os p))))
  (source_op (\<lambda>p. outpu ?os' p @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es ?os' p))))\<close>
          using that(2,3) by force
        hence \<open>wstep (Out (1, p) (d, t)) (my_source_op f os) (my_source_op f ?os')\<close>
          using my_source_op_def by auto
        thus ?thesis using that(1) unfolding R_def invariant_def by (force intro!: wbc_base)
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f os) op2'
  \<and> wbisim_cong R (dataflow_op sg (my_ooo_input_op os')) op2'"
        if "invariant f os"
          and os': "os' |\<in>| ooo_input_op_logic c\<UU> os"
        for os' :: "('c, 'b, 'a, 'd, 'e) input_state_scheme"
      proof -
        have my_source_op_os': \<open>my_source_op f os = my_source_op f os'\<close>
          using that unfolding invariant_def my_source_op_def ooo_input_op_logic_def drop_caps_def
            produce_def drop_cap_def add_cap_def
          by (force intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] split: llist.splits event.splits)
        have \<open>timely_input_stream (es os' p') (mset (ocaps os' p'))\<close> for p'
          using timely_input_stream_ooo_input_op_logic that unfolding invariant_def by fast
        hence \<open>invariant f os'\<close> using that unfolding invariant_def ooo_input_op_logic_def drop_caps_def
            produce_def drop_cap_def add_cap_def by (force split: llist.splits event.splits)
        thus ?thesis using my_source_op_os' unfolding R_def by blast
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f os) op2'
  \<and> wbisim_cong R (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 1 (edges sg) st) (pt_tr sg)\<rparr>)
    (my_ooo_input_op os')) op2'"
        if "invariant f os"
          and "has_progress os"
          and "(os', st) = obtain_progress os"
        for st :: "('c, 'd) shared_state"
          and os' :: "('c, 'b, 'a, 'd, 'e) input_state_scheme"
        using that unfolding R_def invariant_def my_source_op_def obtain_progress_def by (force intro!: wbc_base)
      ultimately show ?thesis using SIM1 unfolding R_def[symmetric]
        by - (sim_cases defs: my_ooo_input_op_def ooo_input_op_def elims: step_dataflow_op_elim step_map_op_elim step_builder_op_elim intros: invariant_initia)
    qed
  qed
next
  case SIM2
  show ?case (is \<open>\<exists>_. _ \<and> wbisim_cong ?R _ _\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    show ?thesis
    proof -
      have "\<exists>op2'. wstep (Out (1, p) (d, t)) (dataflow_op sg (my_ooo_input_op os)) op2'
  \<and> wbisim_cong R op2' (map_op (Pair 1) (Pair 1) (source_op ((\<lambda>p. outpu os p @@- lmap (\<lambda>z. case z of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os p)))(p := lxs))))"
        if "invariant f os"
          and d_t_lxs: "outpu os p @@- lmap (\<lambda>z. case z of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os p)) = LCons (d, t) lxs"
          and "p \<notin> defaults"
        for p :: 'c
          and d :: 'b
          and t :: 'd
          and lxs :: "('b \<times> 'd) llist"
      proof (cases \<open>outpu os p\<close>)
        case Nil
        then obtain d' where d': \<open>f d' = d\<close>
          using d_t_lxs append.simps(1) event.case_eq_if lfilter_eq_LConsD lfilter_eq_LNil llist.map(1)
            llist.map_disc_iff llist_of.simps(1) lmap_eq_LCons_conv lnull_lfilter not_lnull_conv
            prod.simps(1) shift_LNil singleton_lshift snoc_shift by (smt (verit, ccfv_threshold))
        have not_Data: \<open>\<forall>e \<in> set (list_of (ltakeWhile (Not \<circ> is_Data) (es os p))). \<not> is_Data e\<close>
          using that(2) Nil lfinite_ltakeWhile llist.disc(2) llist.map_disc_iff lnull_lfilter
            lset_ltakeWhileD lshift_simps(1) o_apply set_list_of by (metis (mono_tags, lifting))
        have not_lnull: \<open>\<not> lnull (ldropWhile (Not \<circ> is_Data) (es os p))\<close> using that(2) Nil by force
        hence \<open>lhd (ldropWhile (Not \<circ> is_Data) (es os p)) = Data t d'\<close> using that(1,2) d'
            event.case_eq_if event.collapse(1) inj_eq lhd_LCons lhd_lfilter llist.set_intros(1)
            lmap_eq_LCons_conv local.Nil lset_lfilter lshift_simps(1) mem_Collect_eq prod.simps(1)
          unfolding invariant_def by (smt (verit, best))
        hence ldropWhile_LCons_t_d': \<open>ldropWhile (Not \<circ> is_Data) (es os p)
  = LCons (Data t d') (ltl (ldropWhile (Not \<circ> is_Data) (es os p)))\<close> using not_lnull lhd_LCons_ltl by metis
        have lfinite: \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os p))\<close>
          using lfinite_ltakeWhile lnull_ldropWhile not_lnull by metis
        let ?os' = \<open>foldl (ooo_input_os_Drop_Mint p)
  (os\<lparr>es := (es os)(p := ltl (ldropWhile (Not \<circ> is_Data) (es os p)))\<rparr>)
  (list_of (ltakeWhile (Not \<circ> is_Data) (es os p)))\<close>
        let ?os'' = \<open>?os'\<lparr>produ := produ ?os' @ [(p, t, 1)], outpu := (outpu os)(p := [])\<rparr>\<close>
        have initialized: \<open>initia ?os'\<close> using foldl_ooo_input_os_Drop_Mint(1) that(1) not_Data
          unfolding invariant_def by fast
        have outpu_os': \<open>outpu ?os' = outpu os\<close> using foldl_ooo_input_os_Drop_Mint(2) not_Data by metis
        have ocaps_os': \<open>\<forall>p' \<noteq> p. ocaps ?os' p' = ocaps os p'\<close>
          using foldl_ooo_input_os_Drop_Mint(3) not_Data by fast
        have en1_os': \<open>en1 ?os' = en1 os\<close> using foldl_ooo_input_os_Drop_Mint(4) not_Data by metis
        have es_os': \<open>es ?os' = (es os)(p := ltl (ldropWhile (Not \<circ> is_Data) (es os p)))\<close>
          using foldl_ooo_input_os_Drop_Mint(5) not_Data by metis
        have wstep: \<open>wstep (Out (1, p) (d, t)) (dataflow_op sg (my_ooo_input_op os)) (dataflow_op sg (my_ooo_input_op ?os''))\<close> (is \<open>wstep _ _ ?op2'\<close>)
        proof -
          have \<open>(step Tau)\<^sup>*\<^sup>* (ooo_input_op c\<UU> os) (ooo_input_op c\<UU> (produce ?os' (Cap t p) [d]))\<close>
            using that(1,3) d' lfinite ldropWhile_LCons_t_d' en1_os' step_Taus_ooo_input_op_Drop_Mint[where os=os]
            unfolding invariant_def timely_input_stream_def by auto
          hence step_Taus: \<open>(step Tau)\<^sup>*\<^sup>* (dataflow_op sg (my_ooo_input_op os)) (dataflow_op sg (my_ooo_input_op (produce ?os' (Cap t p) [d])))\<close>
            unfolding my_ooo_input_op_def by blast
          have \<open>step (Out (Some p) (Inr (d, t))) (ooo_input_op c\<UU> (produce ?os' (Cap t p) [d])) (ooo_input_op c\<UU> ?os'')\<close>
            using that(3) Nil initialized outpu_os' step_builder_op_Write_Some
            unfolding ooo_input_op_def produce_def by auto
          hence step_Out: \<open>step (Out (1, p) (d, t)) (dataflow_op sg (my_ooo_input_op (produce ?os' (Cap t p) [d]))) ?op2'\<close>
            unfolding my_ooo_input_op_def by fastforce
          show ?thesis using step_Taus step_Out wstep_trans(1) by meson
        qed
        have \<open>timely_input_stream (es ?os'' p') (mset (ocaps ?os'' p'))\<close> for p'
          using timely_input_stream_foldl_ooo_input_os_Drop_Mint[OF lfinite ldropWhile_LCons_t_d']
            that(1) es_os' ocaps_os' unfolding invariant_def by simp
        hence invariant: \<open>invariant f ?os''\<close>
          using that(1) initialized en1_os' unfolding invariant_def by simp
        have my_source_op: \<open>my_source_op f ?os'' = map_op (Pair 1) (Pair 1)
  (source_op ((\<lambda>p. outpu os p @@- lmap (\<lambda>z. case z of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os p)))(p := lxs)))\<close>
          using that(2) Nil es_os' unfolding unfold my_source_op_def
          by (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] dest!: arg_cong[where f=ltl and y=\<open>LCons _ lxs\<close>] simp add: ltl_lfilter)
        show ?thesis using wstep invariant my_source_op unfolding R_def by (force intro!: wbc_base)
      next
        case (Cons x xs)
        hence x_d_t: \<open>x = (d, t)\<close> using that(2) by simp
        let ?os' = \<open>os\<lparr>outpu := (outpu os)(p := xs)\<rparr>\<close>
        have \<open>step (Out (Some p) (Inr (d, t))) (ooo_input_op c\<UU> os) (ooo_input_op c\<UU> ?os')\<close>
          using that(1,3) Cons x_d_t step_builder_op_Write_Some unfolding invariant_def ooo_input_op_def by auto
        hence \<open>wstep (Out (1, p) (d, t)) (dataflow_op sg (my_ooo_input_op os)) (dataflow_op sg (my_ooo_input_op ?os'))\<close>
          unfolding my_ooo_input_op_def by force
        moreover have \<open>my_source_op f ?os' = map_op (Pair 1) (Pair 1)
  (source_op ((\<lambda>p. outpu os p @@- lmap (\<lambda>z. case z of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os p)))(p := lxs)))\<close>
          using that(2) Cons unfolding my_source_op_def
          by (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: fun_eq_iff)
        ultimately show ?thesis using that(1) unfolding R_def invariant_def by (force intro!: wbc_base)
      qed
      thus ?thesis using SIM2 unfolding R_def[symmetric]
        by (sim_cases defs: my_source_op_def elims: step_map_op_elim step_source_op_elim)
    qed
  qed
qed

(* record ('p, 'd, 'd1, 'd2, 'd3, 't) input_state_ty3 = "('p, 'd, 'd1, 'd2, 't) input_state2" +  es3:: "('t, 'd3) event llist"

definition ooo_input_ty3_op where
  "ooo_input_ty3_op os = builder_op {||} {| 1, 2, 3|} os (\<lambda> os. (cimage (\<lambda>p.
  (if p = 1 
  then
   (case es1 os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr> es1 := lxs \<rparr>) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr> es1 := lxs \<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (os\<lparr> es1 := lxs \<rparr>) p t)
  else (if p = 2 then
    (case es2 os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr> es2 := lxs \<rparr>) (Cap t p) [en2 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr> es2 := lxs \<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (os\<lparr> es2 := lxs \<rparr>) p t) 
  else (case es3 os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr> es3 := lxs \<rparr>) (Cap t p) [en3 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr> es3 := lxs \<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (os\<lparr> es3 := lxs \<rparr>) p t) )))
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) {| 1, 2, 3|})))" *)

end