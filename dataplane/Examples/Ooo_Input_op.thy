theory Ooo_Input_op

imports
  Dataplane.Timely_Stream
  Source_op
begin

record ('p, 'd, 'd1, 't) input_state = "('p, 'd, 'd1, 't) operator_state_ty" + es:: "'p \<Rightarrow> ('t, 'd1) event llist"

abbreviation \<open>ooo_input_op_logic ops os \<equiv> cimage (\<lambda>p. case es os p of
    LNil \<Rightarrow> drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> add_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) p t)
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) ops)\<close>

definition ooo_input_op where
  "ooo_input_op ops os = builder_op {||} ops os (ooo_input_op_logic ops)"

abbreviation ooo_inp_op where
  \<open>ooo_inp_op ops os \<equiv>
  map_op (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0 :: 1, p))) (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0 :: 1, p)))
  (ooo_input_op ops os)\<close>

abbreviation ooo_inp_summary where
  \<open>ooo_inp_summary \<equiv> (\<lambda>l1 l2.
  if l1 = Loc (0 :: 1) (Trg (0 :: 1)) \<and> l2 = Loc (0 :: 1) (Src (0 :: 1))
  then antichain {0}
  else {}\<^sub>A)\<close>

abbreviation ooo_input_os_Drop_Mint where
  \<open>ooo_input_os_Drop_Mint p os e \<equiv> (case e of
    Drop t \<Rightarrow> drop_cap os (Cap t p)
  | Mint t \<Rightarrow> add_cap os p t)\<close>

lemma initia_foldl_ooo_input_os_Drop_Mint:
  \<open>initia os \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> initia (foldl (ooo_input_os_Drop_Mint p) os xs)\<close>
  by (induction xs arbitrary: os) (auto split: event.splits)

lemma outpu_foldl_ooo_input_os_Drop_Mint:
  \<open>outpu os p = [] \<Longrightarrow> \<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> outpu (foldl (ooo_input_os_Drop_Mint p) os xs) p = []\<close>
  by (induction xs arbitrary: os) (auto split: event.splits)

lemma en1_foldl_ooo_input_os_Drop_Mint:
  \<open>\<forall>e \<in> set xs. \<not> is_Data e \<Longrightarrow> en1 os = en1 (foldl (ooo_input_os_Drop_Mint p) os xs)\<close>
  by (induction xs arbitrary: os) (auto split: event.splits)

(* TODO prove and move *)
lemma mset_remove_last:
  \<open>mset (remove_last x xs) = mset xs - {#x#}\<close>
  apply (induction x xs rule: remove_last.induct)
  sorry

lemma step_Taus_ooo_input_op_Drop_Mint:
  \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os p)) \<Longrightarrow>
  ldropWhile (Not \<circ> is_Data) (es os p) = LCons (Data t d) lxs \<Longrightarrow> p |\<in>| ops \<Longrightarrow>
  op = ooo_input_op ops os \<Longrightarrow> initia os \<Longrightarrow> monotone (es os p) (mset (ocaps os p)) \<Longrightarrow>
  os' = foldl (ooo_input_os_Drop_Mint p) os (list_of (ltakeWhile (Not \<circ> is_Data) (es os p))) \<Longrightarrow>
  os'' = produce (os'\<lparr>es := (es os')(p := lxs)\<rparr>) (Cap t p) [en1 os' d] \<Longrightarrow> op' = ooo_input_op ops os'' \<Longrightarrow>
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
    using LNil(2,3,7,8) by force
  thus ?case
    using LNil(4,5,9) step_builder_op_Silent ooo_input_op_def by blast
next
  case LCons
  obtain e where head_es: \<open>\<not> is_Data e\<close> \<open>lhd (es os p) = e\<close> \<open>es os p = LCons e (ltl (es os p))\<close>
    using LCons(2) by fastforce
  let ?os1 = \<open>ooo_input_os_Drop_Mint p (os\<lparr>es := (es os)(p := ltl (es os p))\<rparr>) e\<close>
  have ocaps_not_empty: \<open>ocaps os p \<noteq> []\<close>
    using LCons(8) head_es(3) monotone.cases by force
  hence \<open>?os1 |\<in>| ooo_input_op_logic ops os\<close>
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
      using LCons(8) ocaps_not_empty head_es es_os1 monotone.cases
      apply (auto split: event.splits)
      using mset_remove_last event.distinct(1,6) event.inject(2) llist.inject monotone.cases mset_zero_iff
       apply (smt (verit))
      apply fastforce
      done
    moreover have \<open>os' = foldl (ooo_input_os_Drop_Mint p) ?os1 (list_of (ltakeWhile (Not \<circ> is_Data) (es ?os1 p)))\<close>
      using LCons(9) es_os1
      (* TODO Fix the hypothesis on os'. *)
      sorry
    ultimately show ?thesis
      using LCons(3,5,10,11) ooo_input_op_def by blast
  qed
  ultimately show ?case
    by (rule transitive_closurep_trans'(6))
  oops

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