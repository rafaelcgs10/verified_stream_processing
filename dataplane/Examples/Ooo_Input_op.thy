theory Ooo_Input_op

imports
  Dataplane.Timely_Stream
  "../Timely_Infrastructure"
begin

record ('p, 'd, 'd1, 't) input_state = "('p, 'd, 'd1, 't) operator_state_ty" + es:: "'p \<Rightarrow> ('t, 'd1) event llist"

definition \<open>ooo_input_op_logic ops os = cimage (\<lambda>p. case es os p of
    LNil \<Rightarrow> drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> add_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) p t)
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) ops)\<close>

definition ooo_input_op where
  "ooo_input_op ops os = builder_op False {||} ops os (ooo_input_op_logic ops)"


record ('p, 'd, 'd1, 'd2, 't) input_state2 = "('p, 'd, 'd1, 'd2, 't) operator_state_ty2" + 
  es1:: "('t, 'd1) event llist" es2:: "('t, 'd2) event llist"

definition input_ty_fun where
  "input_ty_fun ess_update ess os p = (case ess os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (ess_update (\<lambda> l. lxs) os) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (ess_update (\<lambda> l. lxs) os) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (ess_update (\<lambda> l. lxs) os) p t)"

definition ooo_input_ty2_op where
  "ooo_input_ty2_op os = builder_op False {||} {|1 :: 2, 2|} os (\<lambda> os. (cimage (\<lambda>p.
  (if p = 1 
  then
   input_ty_fun es1_update es1 os p
  else
   input_ty_fun es2_update es2 os p))
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) {| 1, 2|})))"

definition ooo_input_os_Drop_Mint where
  \<open>ooo_input_os_Drop_Mint p os e = (case e of
    Drop t \<Rightarrow> drop_cap os (Cap t p)
  | Mint t \<Rightarrow> add_cap os p t)\<close>

lemma foldl_ooo_input_os_Drop_Mint:
  assumes \<open>\<forall>e \<in> set xs. \<not> is_Data e\<close> \<open>os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) xs\<close>
  shows \<open>initia os \<Longrightarrow> initia os'\<close> \<open>outpu os p = ys \<Longrightarrow> outpu os' p = ys\<close> \<open>en1 os = f \<Longrightarrow> en1 os' = f\<close> \<open>es os' p = lxs\<close>
  using assms
proof (induction xs arbitrary: os)
  case (Cons x xs)
  fix os
  assume H1: \<open>\<forall>e \<in> set (x # xs). \<not> is_Data e\<close>
    and H2: \<open>os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (x # xs)\<close>
  let ?os = \<open>ooo_input_os_Drop_Mint p os x\<close>
  have \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) x = ?os\<lparr>es := (es ?os)(p := lxs)\<rparr>\<close>
    using H1 by (cases x) (simp_all add: ooo_input_os_Drop_Mint_def)
  hence os'_alt: \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os\<lparr>es := (es ?os)(p := lxs)\<rparr>) xs\<close>
    using H2 by (simp add: fun_upd_def)
  {
    assume \<open>initia os\<close>
    hence \<open>initia ?os\<close> using H1 by (cases x; simp add: ooo_input_os_Drop_Mint_def)
    thus \<open>initia os'\<close> using Cons(1) H1 os'_alt by fastforce
  next
    assume \<open>outpu os p = ys\<close>
    hence \<open>outpu ?os p = ys\<close> using H1 by (cases x; simp add: ooo_input_os_Drop_Mint_def)
    thus \<open>outpu os' p = ys\<close> using Cons(2) H1 os'_alt by fastforce
  next
    assume \<open>en1 os = f\<close>
    hence \<open>en1 ?os = f\<close> using H1 by (cases x; simp add: ooo_input_os_Drop_Mint_def)
    thus \<open>en1 os' = f\<close> using Cons(3) H1 os'_alt by fastforce
  next
    show \<open>es os' p = lxs\<close> using Cons(4) H1 os'_alt by fastforce
  }
qed simp_all

lemma monotone_foldl_ooo_input_os_Drop_Mint:
  \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os p)) \<Longrightarrow> ldropWhile (Not \<circ> is_Data) (es os p) = LCons e lxs \<Longrightarrow>
  timely_monotone (es os p) (mset (ocaps os p)) \<Longrightarrow>
  os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es os p))) \<Longrightarrow>
  timely_monotone lxs (mset (ocaps os' p))\<close>
proof (induction \<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os p))\<close> arbitrary: os)
  case Nil
  have \<open>os' = os\<lparr>es := (es os)(p := lxs)\<rparr>\<close> using Nil(1,5) foldl.simps(1) by metis
  hence \<open>ocaps os' p = ocaps os p\<close> by simp
  moreover have \<open>es os p = LCons e lxs\<close> using Nil(1-3) ldropWhile_LCons ldropWhile_simps(1)
      llist.exhaust_sel llist_of.simps(1) llist_of_list_of ltakeWhile_eq_LNil_iff by metis
  moreover have \<open>is_Data e\<close> using Nil(3) ldropWhile_LConsD by fastforce
  ultimately show ?case using Nil(4) timely_monotone.cases by force
next
  case (Cons x xs)
  have \<open>\<not> lnull (es os p)\<close> using Cons(4) eq_LConsD ldropWhile_LNil llist.collapse(1) by metis
  hence lhd_LCons_ltl_es: \<open>LCons (lhd (es os p)) (ltl (es os p)) = es os p\<close> by (rule lhd_LCons_ltl)
  have lhd_es: \<open>\<not> is_Data x\<close> \<open>lhd (es os p) = x\<close> using Cons(2,3) comp_apply eq_LConsD llist_of.simps(2)
      llist_of_list_of ltakeWhile.ctr(1) ltakeWhile.sel(1) by (metis (no_types, opaque_lifting))+
  let ?os = \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) x\<close>
  have \<open>xs = list_of (ltakeWhile (Not \<circ> is_Data) (es ?os p))\<close> using Cons(2,3) lhd_es(1)
    by (cases x; simp add: ooo_input_os_Drop_Mint_def; metis lhd_es list.sel(3) ltl_ltakeWhile tl_list_of)
  moreover have \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es ?os p))\<close> using Cons(3) lhd_es
    by (cases x; simp add: ooo_input_os_Drop_Mint_def)
      (metis lfinite_ltl ltl_ltakeWhile event.disc(2), metis lfinite_ltl ltl_ltakeWhile event.disc(3))
  moreover have \<open>ldropWhile (Not \<circ> is_Data) (es ?os p) = LCons e lxs\<close> using Cons(4) lhd_LCons_ltl_es
      lhd_es ldropWhile_simps(2) by (cases x; simp add: ooo_input_os_Drop_Mint_def; metis)
  moreover have \<open>timely_monotone (es ?os p) (mset (ocaps ?os p))\<close>
    using Cons(5) lhd_LCons_ltl_es lhd_es timely_monotone.cases mset_remove_last
    by (cases x; simp add: ooo_input_os_Drop_Mint_def; fastforce)
  moreover have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os\<lparr>es := (es ?os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os p)))\<close>
  proof -
    have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (LCons x (ltl (es os p)))))\<close>
      using Cons(6) lhd_LCons_ltl_es lhd_es(2) by simp
    also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (list_of (LCons x (ltakeWhile (Not \<circ> is_Data) (ltl (es os p)))))\<close>
      using lhd_es(1) by simp
    also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (os\<lparr>es := (es os)(p := lxs)\<rparr>) (x # list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p))))\<close>
      using Cons(3) list_of_LCons_conv lfinite_ltl lhd_es comp_apply event.disc(2) ltl_ltakeWhile
      by (smt (z3))
    also have \<open>\<dots> = foldl (ooo_input_os_Drop_Mint p) (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) x) (list_of (ltakeWhile (Not \<circ> is_Data) (ltl (es os p))))\<close>
      by (simp add: ooo_input_os_Drop_Mint_def)
    finally show ?thesis using lhd_es(1)
      by (auto intro: arg_cong[where f=\<open>\<lambda>os. foldl _ os _\<close>] simp add: ooo_input_os_Drop_Mint_def split: event.splits)
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
  thus ?case
    using LNil(4,5,9) ocaps_not_empty step_builder_op_Silent ooo_input_op_def by blast
next
  case LCons
  obtain e where lhd_es: \<open>\<not> is_Data e\<close> \<open>lhd (es os p) = e\<close> \<open>es os p = LCons e (ltl (es os p))\<close>
    using LCons(2) by fastforce
  let ?os1 = \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) e\<close>
  have ocaps_not_empty: \<open>ocaps os p \<noteq> []\<close> using LCons(8) lhd_es(3) timely_monotone.cases by force
  hence \<open>?os1 |\<in>| ooo_input_op_logic ops os\<close> unfolding ooo_input_op_logic_def ooo_input_os_Drop_Mint_def
    using LCons(5) lhd_es(1,3) event.case_eq_if llist.case(2) cin_cimage_cfilter input_state.fold_congs(13)
      operator_state.unfold_congs(3,8) by (smt (verit))
  hence \<open>step Tau op (ooo_input_op ops ?os1)\<close>
    using LCons(6,7) ocaps_not_empty step_builder_op_Silent ooo_input_op_def by blast
  moreover have \<open>(step Tau)\<^sup>*\<^sup>* (ooo_input_op ops ?os1) op'\<close>
  proof -
    have es_os1: \<open>es ?os1 p = ltl (es os p)\<close> using lhd_es(1)
      by (auto simp add: ooo_input_os_Drop_Mint_def split: event.splits)
    hence \<open>ltl (ltakeWhile (Not \<circ> is_Data) (es os p)) = ltakeWhile (Not \<circ> is_Data) (es ?os1 p)\<close>
      using LCons(2) lnull_ltakeWhile ltakeWhile.simps(4) by force
    moreover from this have \<open>ldropWhile (Not \<circ> is_Data) (es ?os1 p) = LCons (Data t d) lxs\<close>
      using LCons(2,4) es_os1 ldropWhile_simps(2) lhd_LCons_ltl ltakeWhile.disc(1) by metis
    moreover have \<open>initia ?os1\<close> using LCons(7) lhd_es(1)
      by (auto simp add: ooo_input_os_Drop_Mint_def split: event.splits)
    moreover have \<open>timely_monotone (es ?os1 p) (mset (ocaps ?os1 p))\<close>
    proof (cases e)
      case Data
      thus ?thesis using lhd_es(1) by simp
    next
      case (Drop t')
      hence \<open>ocaps (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) e) p = remove_last t' (ocaps os p)\<close>
        by (simp add: ooo_input_os_Drop_Mint_def)
      thus ?thesis using Drop LCons(8) ocaps_not_empty lhd_es(3) es_os1 timely_monotone.cases
          mset_remove_last event.distinct(2,5) event.inject(2) llist.simps(1) mset_zero_iff
        by (smt (verit, ccfv_threshold))
    next
      case (Mint t')
      hence \<open>ocaps (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) e) p = ocaps os p @ [t']\<close>
        by (simp add: ooo_input_os_Drop_Mint_def)
      thus ?thesis using Mint LCons(8) lhd_es(3) es_os1 timely_monotone.cases by fastforce
    qed
    moreover have \<open>os' = foldl (ooo_input_os_Drop_Mint p) (?os1\<lparr>es := (es ?os1)(p := lxs)\<rparr>) (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p)))\<close>
    proof -
      have \<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os p)) = e # list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p))\<close>
        using LCons(1) lhd_es es_os1 ltakeWhile.ctr(2) not_lnull_conv by fastforce
      hence \<open>os' = foldl (ooo_input_os_Drop_Mint p) (ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) e) (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p)))\<close>
        using LCons(9) by (simp split: event.splits)
      moreover have \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := lxs)\<rparr>) e = ?os1\<lparr>es := (es ?os1)(p := lxs)\<rparr>\<close>
        using lhd_es(1) by (auto simp add: ooo_input_os_Drop_Mint_def split: event.splits)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis using LCons(3,5,10,11) ooo_input_op_def by blast
  qed
  ultimately show ?case by (rule transitive_closurep_trans'(6))
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