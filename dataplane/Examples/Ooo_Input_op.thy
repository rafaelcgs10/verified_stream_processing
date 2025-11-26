theory Ooo_Input_op

imports
  Dataplane.Timely_Stream
  Source_op
begin

record ('p, 'd, 'd1, 't) input_state = "('p, 'd, 'd1, 't) operator_state_ty" + es:: "'p \<Rightarrow> ('t, 'd1) event llist"

definition \<open>ooo_input_op_logic ops os = cimage (\<lambda>p. case es os p of
    LNil \<Rightarrow> drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> add_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) p t)
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) ops)\<close>

definition ooo_input_op where
  "ooo_input_op ops os = builder_op {||} ops os (ooo_input_op_logic ops)"

abbreviation ooo_input_os_Drop_Mint where
  \<open>ooo_input_os_Drop_Mint p os e \<equiv> (case e of
    Drop t \<Rightarrow> drop_cap os (Cap t p)
  | Mint t \<Rightarrow> add_cap os p t)\<close>

lemma initia_foldl_ooo_input_os_Drop_Mint:
  \<open>initia os \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> os' = foldl (ooo_input_os_Drop_Mint p) os xs \<Longrightarrow> initia os'\<close>
  by (induction xs arbitrary: os) (auto split: event.splits)

lemma initia_foldl_ooo_input_os_Drop_Mint_es_update:
  \<open>initia os \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> os' = (foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) xs) \<Longrightarrow>
  initia os'\<close>
  by (rule initia_foldl_ooo_input_os_Drop_Mint) simp_all

lemma outpu_foldl_ooo_input_os_Drop_Mint:
  \<open>outpu os p = ys \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> os' = foldl (ooo_input_os_Drop_Mint p) os xs \<Longrightarrow>
  outpu os' p = ys\<close>
  by (induction xs arbitrary: os) (auto split: event.splits)

lemma outpu_foldl_ooo_input_os_Drop_Mint_es_update:
  \<open>outpu os p = ys \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) xs \<Longrightarrow>
  outpu os' p = ys\<close>
  by (rule outpu_foldl_ooo_input_os_Drop_Mint) simp_all

lemma en1_foldl_ooo_input_os_Drop_Mint:
  \<open>en1 os = f \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> os' = foldl (ooo_input_os_Drop_Mint p) os xs \<Longrightarrow> en1 os' = f\<close>
  by (induction xs arbitrary: os) (auto split: event.splits)

lemma en1_foldl_ooo_input_os_Drop_Mint_es_update:
  \<open>en1 os = f \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) xs \<Longrightarrow> en1 os' = f\<close>
  by (rule en1_foldl_ooo_input_os_Drop_Mint[where os=\<open>os\<lparr>es := (es os)(p := lxs)\<rparr>\<close>]) simp_all

lemma es_foldl_ooo_input_os_Drop_Mint:
  \<open>es os p = lxs \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> os' = foldl (ooo_input_os_Drop_Mint p) os xs \<Longrightarrow> es os' p = lxs\<close>
  by (induction xs arbitrary: os) (auto split: event.splits)

lemma monotone_ooo_input_os_Drop_Mint_es_update:
  \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os p)) \<Longrightarrow> ldropWhile (Not \<circ> is_Data) (es os p) = LCons e lxs \<Longrightarrow>
  monotone (es os p) (mset (ocaps os p)) \<Longrightarrow>
  os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es os p))) \<Longrightarrow>
  monotone lxs (mset (ocaps os' p))\<close>
proof (induction \<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os p))\<close> arbitrary: os)
  case Nil
  have \<open>os' = os\<lparr>es := (es os)(p := lxs)\<rparr>\<close>
    using Nil(1,5) foldl.simps(1) by metis
  hence \<open>ocaps os' p = ocaps os p\<close>
    by simp
  moreover have \<open>es os p = LCons e lxs\<close>
    using Nil(1-3) ldropWhile_LCons ldropWhile_simps(1) llist.exhaust_sel llist_of.simps(1)
      llist_of_list_of ltakeWhile_eq_LNil_iff by metis
  moreover have \<open>is_Data e\<close>
    using Nil(3) ldropWhile_LConsD by fastforce
  ultimately show ?case
    using Nil(4) monotone.cases by force
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case Data
    thus ?thesis
      using Cons(2,3) comp_apply eq_LConsD event.disc(1) llist_of.simps(2) llist_of_list_of
        ltakeWhile.ctr(1) ltakeWhile.sel(1) by (metis (no_types, lifting))
  next
    case (Drop t)
    let ?os' = \<open>drop_cap (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) (Cap t p)\<close>
    have head_es: \<open>lhd (es os p) = Drop t\<close>
      using Cons(2,3) Drop eq_LConsD llist_of.simps(2) llist_of_list_of ltakeWhile.ctr(1)
        ltakeWhile.sel(1) by metis
    have not_null_es: \<open>\<not> lnull (es os p)\<close>
      using Cons(4) eq_LConsD ldropWhile_LNil llist.collapse(1) by metis
    hence lhd_LCons_ltl_es: \<open>LCons (lhd (es os p)) (ltl (es os p)) = es os p\<close>
      by (rule lhd_LCons_ltl)
    have \<open>xs = list_of (ltakeWhile (Not \<circ> is_Data) (es ?os' p))\<close>
    proof -
      have \<open>xs = list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p)))\<close>
        using Cons(2,3) head_es ltl_ltakeWhile tl_list_of list.sel(3) ltakeWhile_eq_LNil_iff not_Cons_self
        by metis
      thus ?thesis
        by simp
    qed
    moreover have \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es ?os' p))\<close>
      using Cons(3) head_es by simp (metis lfinite_ltl ltl_ltakeWhile event.disc(2))
    moreover have \<open>ldropWhile (Not \<circ> is_Data) (es ?os' p) = LCons e lxs\<close>
    proof -
      have \<open>ldropWhile (Not \<circ> is_Data) (LCons (lhd (es os p)) (ltl (es os p))) = LCons e lxs\<close>
        using Cons(4) lhd_LCons_ltl_es by simp
      thus ?thesis
        using head_es by simp
    qed
    moreover have \<open>monotone (es ?os' p) (mset (ocaps ?os' p))\<close>
      by simp (smt (verit) Cons(5) head_es mset_remove_last monotone.cases event.distinct(2,5) event.simps(2) lhd_LCons_ltl_es llist.simps(1,2))
    moreover have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os'\<lparr>es := (es ?os')(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os' p)))\<close>
    proof -
      have es_upd: \<open>os\<lparr>es := (es os)(p := lxs), inter := inter os @ [(p, t, - 1)], ocaps := map_entry p (remove_last t) (ocaps os)\<rparr>
  = os\<lparr>inter := inter os @ [(p, t, - 1)], ocaps := map_entry p (remove_last t) (ocaps os), es := (es os)(p := lxs)\<rparr>\<close>
        by simp
      have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (LCons (Drop t) (ltl (es os p)))))\<close>
        using Cons(6) lhd_LCons_ltl_es head_es by simp
      also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (LCons (Drop t) (ltakeWhile (Not \<circ> is_Data) (ltl (es os p)))))\<close>
        by simp
      also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Drop t # list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p))))\<close>
        using Cons(3) list_of_LCons_conv lfinite_ltl head_es comp_apply event.disc(2) ltl_ltakeWhile
        by (smt (z3))
      also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (drop_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p)) (list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p))))\<close>
        by simp
      finally show ?thesis
        using es_upd by simp
    qed
    ultimately show ?thesis
      using Cons(1) by blast
  next
    case (Mint t)
    let ?os' = \<open>add_cap (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) p t\<close>
    have head_es: \<open>lhd (es os p) = Mint t\<close>
      using Cons(2,3) Mint eq_LConsD llist_of.simps(2) llist_of_list_of ltakeWhile.ctr(1)
        ltakeWhile.sel(1) by metis
    have not_null_es: \<open>\<not> lnull (es os p)\<close>
      using Cons(4) eq_LConsD ldropWhile_LNil llist.collapse(1) by metis
    hence lhd_LCons_ltl_es: \<open>LCons (lhd (es os p)) (ltl (es os p)) = es os p\<close>
      by (rule lhd_LCons_ltl)
    have \<open>xs = list_of (ltakeWhile (Not \<circ> is_Data) (es ?os' p))\<close>
    proof -
      have \<open>xs = list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p)))\<close>
        using Cons(2,3) head_es ltl_ltakeWhile tl_list_of list.sel(3) ltakeWhile_eq_LNil_iff not_Cons_self
        by metis
      thus ?thesis
        by simp
    qed
    moreover have \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es ?os' p))\<close>
      using Cons(3) head_es by simp (metis lfinite_ltl ltl_ltakeWhile event.disc(3))
    moreover have \<open>ldropWhile (Not \<circ> is_Data) (es ?os' p) = LCons e lxs\<close>
    proof -
      have \<open>ldropWhile (Not \<circ> is_Data) (LCons (lhd (es os p)) (ltl (es os p))) = LCons e lxs\<close>
        using Cons(4) lhd_LCons_ltl_es by simp
      thus ?thesis
        using head_es by simp
    qed
    moreover have \<open>monotone (es ?os' p) (mset (ocaps ?os' p))\<close>
      apply simp
      using Cons(5) head_es monotone.cases lhd_LCons_ltl_es by force
    moreover have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os'\<lparr>es := (es ?os')(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os' p)))\<close>
    proof -
      have es_upd: \<open>os\<lparr>es := (es os)(p := lxs), inter := inter os @ [(p, t, 1)], ocaps := (ocaps os)(p := ocaps os p @ [t])\<rparr>
  = os\<lparr>inter := inter os @ [(p, t, 1)], ocaps := (ocaps os)(p := ocaps os p @ [t]), es := (es os)(p := lxs)\<rparr>\<close>
        by simp
      have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (LCons (Mint t) (ltl (es os p)))))\<close>
        using Cons(6) lhd_LCons_ltl_es head_es by simp
      also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (LCons (Mint t) (ltakeWhile (Not \<circ> is_Data) (ltl (es os p)))))\<close>
        by simp
      also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Mint t # list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p))))\<close>
        using Cons(3) list_of_LCons_conv lfinite_ltl head_es comp_apply event.disc(3) ltl_ltakeWhile
        by (smt (z3))
      also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (add_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) p t) (list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p))))\<close>
        by simp
      finally show ?thesis
        using es_upd by simp
    qed
    ultimately show ?thesis
      using Cons(1) by blast
  qed
qed

lemma step_Taus_ooo_input_op_Drop_Mint:
  \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os p)) \<Longrightarrow>
  ldropWhile (Not \<circ> is_Data) (es os p) = LCons (Data t d) lxs \<Longrightarrow> p |\<in>| ops \<Longrightarrow>
  op = ooo_input_op ops os \<Longrightarrow> initia os \<Longrightarrow> monotone (es os p) (mset (ocaps os p)) \<Longrightarrow>
  os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es os p))) \<Longrightarrow>
  os'' = produce os' (Cap t p) [en1 os' d] \<Longrightarrow> op' = ooo_input_op ops os'' \<Longrightarrow>
  (step Tau)\<^sup>*\<^sup>* op op'\<close>
  unfolding ooo_input_op_def
proof (induction \<open>ltakeWhile (Not \<circ> is_Data) (es os p)\<close> arbitrary: os op rule: lfinite_induct)
  case LNil
  have \<open>ldropWhile (Not \<circ> is_Data) (es os p) = es os p\<close>
    using LNil(1) ldropWhile_LCons ldropWhile_LNil llist.sel(1) lnull_def ltakeWhile_eq_LNil_iff neq_LNil_conv
    by metis
  moreover from this have \<open>ocaps os p \<noteq> []\<close>
    using LNil(2,6) monotone.cases by force
  ultimately have \<open>os'' |\<in>| ooo_input_op_logic ops os\<close>
    using LNil(2,3,7,8) ooo_input_op_logic_def by force
  thus ?case
    using LNil(4,5,9) step_builder_op_Silent ooo_input_op_def by blast
next
  case LCons
  obtain e where head_es: \<open>\<not> is_Data e\<close> \<open>lhd (es os p) = e\<close> \<open>es os p = LCons e (ltl (es os p))\<close>
    using LCons(2) by fastforce
  let ?os1 = \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := map_entry p ltl (es os)\<rparr>) e\<close>
  have ocaps_not_empty: \<open>ocaps os p \<noteq> []\<close>
    using LCons(8) head_es(3) monotone.cases by force
  hence \<open>?os1 |\<in>| ooo_input_op_logic ops os\<close>
    unfolding ooo_input_op_logic_def
    using LCons(5) head_es(1,3) cin_cimage_cfilter event.case_eq_if input_state.fold_congs(12)
      llist.case(2) operator_state.unfold_congs(3,8) by (smt (verit))
  hence \<open>step Tau op (ooo_input_op ops ?os1)\<close>
    using LCons(6,7) step_builder_op_Silent[of os] ooo_input_op_def by blast
  moreover have \<open>(step Tau)\<^sup>*\<^sup>* (ooo_input_op ops ?os1) op'\<close>
  proof -
    have es_os1: \<open>es ?os1 p = ltl (es os p)\<close>
      using head_es(1) by (auto split: event.splits)
    hence \<open>ltl (ltakeWhile (Not \<circ> is_Data) (es os p)) = ltakeWhile (Not \<circ> is_Data) (es ?os1 p)\<close>
      using LCons(2) lnull_ltakeWhile ltakeWhile.simps(4) by force
    moreover from this have \<open>ldropWhile (Not \<circ> is_Data) (es ?os1 p) = LCons (Data t d) lxs\<close>
      using LCons(2,4) es_os1 ldropWhile_simps(2) lhd_LCons_ltl ltakeWhile.disc(1) by metis
    moreover have \<open>initia ?os1\<close>
      using LCons(7) head_es(1) by (auto split: event.splits)
    moreover have \<open>monotone (es ?os1 p) (mset (ocaps ?os1 p))\<close>
    proof (cases e)
      case Data
      thus ?thesis
        using head_es(1) by simp
    next
      case (Drop t')
      hence \<open>ocaps (ooo_input_os_Drop_Mint p (os\<lparr>es := map_entry p ltl (es os)\<rparr>) e) p = remove_last t' (ocaps os p)\<close>
        by simp
      thus ?thesis
       using Drop LCons(8) ocaps_not_empty head_es(3) es_os1 monotone.cases
       mset_remove_last event.distinct(2,5) event.inject(2) llist.simps(1) mset_zero_iff
       by (smt (verit, ccfv_threshold))
    next
      case Mint
      thus ?thesis
        using LCons(8) head_es(3) monotone.cases by fastforce
    qed
    moreover have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os1\<lparr>es := (es ?os1)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p)))\<close>
    proof -
      have \<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os p)) = e # list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p))\<close>
        using LCons(1) head_es es_os1 ltakeWhile.ctr(2) not_lnull_conv by fastforce
      hence \<open>os' = foldl (ooo_input_os_Drop_Mint p) (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) e) (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p)))\<close>
        using LCons(9) by (simp split: event.splits)
      moreover have \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) e =
  (ooo_input_os_Drop_Mint p (os\<lparr>es := map_entry p ltl (es os)\<rparr>) e)\<lparr>es := (es (ooo_input_os_Drop_Mint p (os\<lparr>es := map_entry p ltl (es os)\<rparr>) e))(p := lxs)\<rparr>\<close>
        using head_es(1) by (auto split: event.splits)
      ultimately show ?thesis
        by simp
    qed
    ultimately show ?thesis
      using LCons(3,5,10,11) ooo_input_op_def by blast
  qed
  ultimately show ?case
    by (rule transitive_closurep_trans'(6))
qed

abbreviation ooo_inp_op where
  \<open>ooo_inp_op os \<equiv>
  map_op (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0 :: 1, p))) (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0 :: 1, p)))
  (ooo_input_op {|0 :: 1|} os)\<close>

abbreviation ooo_inp_summary where
  \<open>ooo_inp_summary \<equiv> (\<lambda>l1 l2.
  if l1 = Loc (0 :: 1) (Trg (0 :: 1)) \<and> l2 = Loc (0 :: 1) (Src (0 :: 1))
  then antichain {0}
  else {}\<^sub>A)\<close>

lemma ooo_input_op_source_op:
  \<open>summ sg = ooo_inp_summary \<Longrightarrow>
  initia os \<Longrightarrow>
  en1 os = id \<Longrightarrow>
  monotone (es os 0) (mset (ocaps os 0)) \<Longrightarrow>
  dataflow_op sg (ooo_inp_op os)
  \<approx> map_op (\<lambda>(p :: 1). (0, p)) (\<lambda>p. (0, p))
    (source_op (\<lambda>p. outpu os p @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (d, t)) (lfilter is_Data (es os p))))\<close>
  unfolding ooo_input_op_def ooo_input_op_logic_def
proof (coinduction arbitrary: sg os rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    apply (elim step_dataflow_op_elim step_map_op_elim step_builder_op_elim conjE; simp; hypsubst_thin?; simp)
    subgoal
      apply (intro exI conjI)
       apply (rule step_wstep)
       apply (rule step_map_op)
        apply (rule step_source_op_Out_intro)
          apply (simp_all add: defaults_num1_def)
      apply (rule wbc_base)
      apply (intro exI conjI)
           apply (rule refl)
          apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op])
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
           apply (rule refl)
          apply simp_all
         apply (auto 0 0 intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] arg_cong[where f=\<open>lshift _\<close>] simp add: produce_def fun_eq_iff split: llist.splits event.splits)
      subgoal
        using monotone.cases by fastforce
      subgoal
        using monotone.cases by blast
      subgoal
        using monotone.cases mset_remove_last event.simps(2,5,9) llist.simps(1) mset_zero_iff
        by (smt (verit))
      subgoal
        using monotone.cases by fastforce
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
           apply (rule refl)
          apply (auto intro: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: produce_def split: if_splits)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
           apply (rule refl)
          apply (auto split: option.splits)
      done
    done
next
  case SIM2
  then show ?case
    apply (elim step_map_op_elim step_source_op_elim conjE; simp; hypsubst_thin?; simp)
    subgoal for x lxs
      apply (cases x; cases \<open>outpu os 0\<close>; simp)
      subgoal for d t
        apply (subgoal_tac \<open>ldropWhile (Not \<circ> is_Data) (es os 0) = LCons (Data t d) (ltl (ldropWhile (Not \<circ> is_Data) (es os 0)))\<close>)
         apply (subgoal_tac \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os 0))\<close>)
          apply (subgoal_tac \<open>initia (foldl
                   (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>)
                           (add_cap os 1))
                   (os\<lparr>es := (es os)(1 := ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os 1)))\<rparr>) (list_of (ltakeWhile (\<lambda>x. \<not> is_Data x) (es os 1))))
               \<close>)
           apply (subgoal_tac \<open>en1 (foldl
                   (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>)
                           (add_cap os 1))
                   (os\<lparr>es := (es os)(1 := ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os 1)))\<rparr>) (list_of (ltakeWhile (\<lambda>x. \<not> is_Data x) (es os 1))))
               = id\<close>)
        subgoal
          apply (rule exI)
          apply (rule conjI)
           apply (rule wstep_trans(1))
            apply (rule step_Taus_dataflow_op_Taus_intro)
            apply (rule step_star_map_op)
            apply (rule step_Taus_ooo_input_op_Drop_Mint[where p=1 and os=os and ops=\<open>{|1|}\<close>])
                    apply simp_all
            apply (unfold ooo_input_op_def)
            apply (unfold ooo_input_op_logic_def)
            apply simp
           apply (rule step_Out_dataflow_op_Out_Inr_intro)
           apply (rule step_map_op)
            apply (rule step_builder_op_Write_Some[where p=1])
                apply (simp_all add: produce_def)
            apply (drule outpu_foldl_ooo_input_os_Drop_Mint_es_update[where p=1 and xs=\<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os 0))\<close> and lxs=\<open>ltl (ldropWhile (Not \<circ> is_Data) (es os 1))\<close>])
          using set_list_of ltakeWhile_all comp_apply lset_ltakeWhileD ltakeWhile_cong zero_one
              apply (smt (verit, best))
             apply (rule refl)
            apply simp
            apply (subgoal_tac \<open>(ooo_input_os_Drop_Mint 1 :: (1, 'c, 'c, 'a, 'd) input_state_scheme \<Rightarrow> ('a, 'c) event \<Rightarrow> (1, 'c, 'c, 'a, 'd) input_state_scheme)
  = (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>) (add_cap os 1))\<close>)
             apply simp
          using event.case apply simp
           apply simp
          apply (rule wbc_base)
          apply (subgoal_tac \<open>es (foldl
             (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>) (add_cap os 1))
             (os\<lparr>es := (es os)(1 := ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os 1)))\<rparr>) (list_of (ltakeWhile (\<lambda>x. \<not> is_Data x) (es os 1))))
         1 = ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os 1))\<close>)
           apply (intro exI conjI)
                apply (rule refl)
               apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: fun_eq_iff)
          using ltl_lfilter ext comp_apply ltl_lmap ltl_simps(2) apply (metis (lifting))
           apply (rule monotone_ooo_input_os_Drop_Mint_es_update)
              apply simp
             apply simp
            apply assumption
           apply simp
          apply (rule es_foldl_ooo_input_os_Drop_Mint[where os=\<open>(os\<lparr>es := (es os)(1 := ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os 1)))\<rparr>)\<close> and xs=\<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os 0))\<close>])
            apply simp
          using set_list_of ltakeWhile_all comp_apply lset_ltakeWhileD ltakeWhile_cong zero_one
           apply (smt (verit, best))
          apply simp
          done
        using event.case apply simp
           apply (drule en1_foldl_ooo_input_os_Drop_Mint_es_update[where p=1 and xs=\<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os 0))\<close> and lxs=\<open>ltl (ldropWhile (Not \<circ> is_Data) (es os 1))\<close>])
        using set_list_of ltakeWhile_all comp_apply lset_ltakeWhileD ltakeWhile_cong zero_one
             apply (smt (verit, best))
            apply (rule refl)
           apply (subgoal_tac \<open>(ooo_input_os_Drop_Mint 1 :: (1, 'c, 'c, 'a, 'd) input_state_scheme \<Rightarrow> ('a, 'c) event \<Rightarrow> (1, 'c, 'c, 'a, 'd) input_state_scheme)
  = (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>) (add_cap os 1))\<close>)
            apply simp
        using event.case apply simp
          apply (drule initia_foldl_ooo_input_os_Drop_Mint_es_update[where p=1 and xs=\<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os 0))\<close> and lxs=\<open>ltl (ldropWhile (Not \<circ> is_Data) (es os 1))\<close>])
        using set_list_of ltakeWhile_all comp_apply lset_ltakeWhileD ltakeWhile_cong zero_one
            apply (smt (verit, best))
           apply (rule refl)
          apply (subgoal_tac \<open>(ooo_input_os_Drop_Mint 1 :: (1, 'c, 'c, 'a, 'd) input_state_scheme \<Rightarrow> ('a, 'c) event \<Rightarrow> (1, 'c, 'c, 'a, 'd) input_state_scheme)
  = (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>) (add_cap os 1))\<close>)
           apply simp
        using event.case apply simp
        using lfinite_ltakeWhile apply fastforce
        using lfilter_eq_LCons event.case_eq_if event.collapse(1) lfilter_eq_LConsD lmap_eq_LCons_conv
          ltl_simps(2) prod.sel(1,2) zero_one
        apply (smt (verit, ccfv_threshold))
        done
      subgoal
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply (rule step_Out_dataflow_op_Out_Inr_intro)
         apply (rule step_map_op)
          apply (rule step_builder_op_Write_Some[where p=1])
              apply simp_all
         apply simp
        apply (rule wbc_base)
        apply (intro exI conjI)
             apply (rule refl)
            apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op])
        done
      done
    done
qed

record ('p, 'd, 'd1, 'd2, 't) input_state2 = "('p, 'd, 'd1, 'd2, 't) operator_state_ty2" + 
  es1:: "('t, 'd1) event llist" es2:: "('t, 'd2) event llist"

definition input_ty_fun where
  "input_ty_fun ess_update ess os p = (case ess os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (ess_update (\<lambda> l. lxs) os) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (ess_update (\<lambda> l. lxs) os) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (ess_update (\<lambda> l. lxs) os) p t)"

definition ooo_input_ty2_op where
  "ooo_input_ty2_op os = builder_op {||} {|1 :: 2, 2|} os (\<lambda> os. (cimage (\<lambda>p.
  (if p = 1 
  then
   input_ty_fun es1_update es1 os p
  else
   input_ty_fun es2_update es2 os p))
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) {| 1, 2|})))"




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