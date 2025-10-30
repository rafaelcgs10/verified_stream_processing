theory Ooo_Input_top

imports
  Dataplane.Watermarked_Stream
  Source_op
begin

(* TODO move *)
abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"
abbreviation "send_progress op st \<equiv> Write op None (Inl (Inl st))"
abbreviation "obtain_progress os \<equiv> (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"
abbreviation "drop_cap os cap \<equiv> (os\<lparr> inter := inter os @ [(out cap, time cap, -1)] \<rparr>)"
abbreviation "drop_caps os caps \<equiv> (os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, -1)) caps \<rparr>)"
abbreviation "mint_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"
abbreviation \<open>mint os caps p t \<equiv> if t \<in> set (caps p) then (caps, os) else (caps(p := caps p @ [t]), mint_cap os p t)\<close>

corec ooo_input_top where
  \<open>ooo_input_top os caps ins = choice3
  (Choice (cimage (\<lambda>p. case ins p of
    LCons (Data t d) lxs \<Rightarrow> Silent (ooo_input_top (produce os (Cap t p) [d]) caps (ins(p := lxs)))
  | LCons (Watermark wm) lxs \<Rightarrow>
      let (caps', os') = mint os caps p wm;
          A = antichain (minimal_antichain (set (caps' p)));
          dropped_caps = map (\<lambda>t. Cap t p)
            (filter (if lnull lxs then \<top> else Not \<circ> frontier_less_equal A) (caps' p));
          caps'' = caps'(p := filter (if lnull lxs then \<bottom> else frontier_less_equal A) (caps' p));
          os'' = drop_caps os' dropped_caps
      in Silent (ooo_input_top os'' caps'' (ins(p := lxs))))
    (cfilter (\<lambda>p. ins p \<noteq> LNil) c\<UU>)))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (ooo_input_top (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) caps ins) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (ooo_input_top os' caps ins) st)\<close>

lemma step_ooo_input_top_elim:
  assumes \<open>step io (ooo_input_top os caps ins) op\<close>
  obtains p t d lxs where \<open>io = Tau\<close> \<open>ins p = LCons (Data t d) lxs\<close>
    \<open>op = ooo_input_top (produce os (Cap t p) [d]) caps (ins(p := lxs))\<close> \<open>p \<notin> defaults\<close>
  | p wm lxs caps' os' A dropped_caps caps'' os'' where \<open>io = Tau\<close> \<open>ins p = LCons (Watermark wm) lxs\<close>
    \<open>(caps', os') = mint os caps p wm\<close> \<open>A = antichain (minimal_antichain (set (caps' p)))\<close>
    \<open>dropped_caps = map (\<lambda>t. Cap t p) (filter (if lnull lxs then \<top> else Not \<circ> frontier_less_equal A) (caps' p))\<close>
    \<open>caps'' = caps'(p := filter (if lnull lxs then \<bottom> else frontier_less_equal A) (caps' p))\<close>
    \<open>os'' = drop_caps os' dropped_caps\<close>
    \<open>op = ooo_input_top os'' caps'' (ins(p := lxs))\<close> \<open>p \<notin> defaults\<close>
  | p x xs where \<open>io = Out (Some p) (Inr x)\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = ooo_input_top (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) caps ins\<close> \<open>p \<notin> defaults\<close>
  | os' st where \<open>io = Out None (Inl (Inl st))\<close> \<open>(os', st) = obtain_progress os\<close> \<open>op = ooo_input_top os' caps ins\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) ooo_input_top.code)
  apply (cases io)
    apply (auto split: list.splits llist.splits event.splits prod.splits if_splits)
          apply blast+
  done

lemma step_ooo_input_top_Write_Some[intro]:
  \<open>outpu os p = x # xs \<Longrightarrow> op = ooo_input_top (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) caps ins \<Longrightarrow> p \<notin> defaults \<Longrightarrow>
  step (Out (Some p) (Inr x)) (ooo_input_top os caps ins) op\<close>
  by (subst ooo_input_top.code) force

lemma step_ooo_input_top_Write_None[intro]:
  \<open>(os', st) = obtain_progress os \<Longrightarrow> op = ooo_input_top os' caps ins \<Longrightarrow> p \<notin> defaults \<Longrightarrow>
  step (Out None (Inl (Inl st))) (ooo_input_top os caps ins) op\<close>
  by (subst ooo_input_top.code) auto

lemma step_ooo_input_top_Silent_Data[intro]:
  \<open>ins p = LCons (Data t d) lxs \<Longrightarrow> op = ooo_input_top (produce os (Cap t p) [d]) caps (ins(p := lxs)) \<Longrightarrow>
  p \<notin> defaults \<Longrightarrow> step Tau (ooo_input_top os caps ins) op\<close>
  by (subst ooo_input_top.code) fastforce

lemma step_ooo_input_top_Silent_Watermark[intro]:
  \<open>ins p = LCons (Watermark wm) lxs \<Longrightarrow>
  (caps', os') = mint os caps p wm \<Longrightarrow>
  A = antichain (minimal_antichain (set (caps' p))) \<Longrightarrow>
  dropped_caps = map (\<lambda>t. Cap t p) (filter (if lnull lxs then \<top> else Not \<circ> frontier_less_equal A) (caps' p)) \<Longrightarrow>
  caps'' = caps'(p := filter (if lnull lxs then \<bottom> else frontier_less_equal A) (caps' p)) \<Longrightarrow>
  os'' = drop_caps os' dropped_caps \<Longrightarrow> op = ooo_input_top os'' caps'' (ins(p := lxs)) \<Longrightarrow> p \<notin> defaults \<Longrightarrow>
  step Tau (ooo_input_top os caps ins) op\<close>
  by (subst ooo_input_top.code) (fastforce intro: bexI[of _ p])

(* TODO move *)
lemma snd_foldl:
  \<open>snd (foldl (\<lambda>(a, b) x. (f a b x, g b x)) (a, b) xs) = foldl g b xs\<close>
  by (induction xs arbitrary: a b) simp_all

lemma foldl_id2:
  \<open>foldl (\<lambda>x y. x) x xs = x\<close>
  by (induction xs) simp_all

abbreviation ooo_input_os_caps_Watermark where
  \<open>ooo_input_os_caps_Watermark p wm os caps \<equiv>
  (let (caps', os') = mint os caps p wm;
       A = antichain (minimal_antichain (set (caps' p)));
       dropped_caps = map (\<lambda>t. Cap t p) (filter (Not \<circ> frontier_less_equal A) (caps' p));
       caps'' = caps'(p := filter (frontier_less_equal A) (caps' p));
       os'' = drop_caps os' dropped_caps
  in (os'', caps''))\<close>

lemma step_Taus_ooo_input_top:
  \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (ins p)) \<Longrightarrow>
  ldropWhile (Not \<circ> is_Data) (ins p) = LCons (Data t d) lxs \<Longrightarrow>
  (os', caps') = foldl (\<lambda>(os, caps) wm. ooo_input_os_caps_Watermark p wm os caps)
    (os, caps) (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) (ins p)))) \<Longrightarrow>
  os'' = produce os' (Cap t p) [d] \<Longrightarrow> op = ooo_input_top os'' caps' (ins(p := lxs)) \<Longrightarrow> p \<notin> defaults \<Longrightarrow>
  (step Tau)\<^sup>*\<^sup>* (ooo_input_top os caps ins) op\<close>
proof (induction \<open>ltakeWhile (Not \<circ> is_Data) (ins p)\<close> arbitrary: ins os caps rule: lfinite_induct)
  case LNil
  hence \<open>ldropWhile (Not \<circ> is_Data) (ins p) = ins p\<close>
    using ldropWhile_LCons ldropWhile_LNil llist.sel(1) lnull_def ltakeWhile_eq_LNil_iff neq_LNil_conv
    by (metis (no_types, opaque_lifting))
  hence \<open>step Tau (ooo_input_top os caps ins)
  (ooo_input_top (produce os (Cap t p) [d]) caps (ins(p := lxs)))\<close>
    using LNil step_ooo_input_top_Silent_Data by auto
  thus ?case
    using LNil by (auto simp add: lnull_def)
next
  case LCons
  then show ?case
  proof -
    obtain wm where 1: \<open>lhd (ins p) = Watermark wm\<close> \<open>ins p = LCons (Watermark wm) (ltl (ins p))\<close>
      using LCons(2) event.collapse(2) ltakeWhile.disc(1) llist.collapse(2) o_def by metis
    obtain os1 caps1 where os1_caps1_def: \<open>(os1, caps1) = ooo_input_os_caps_Watermark p wm os caps\<close>
      by fastforce
    have \<open>ltl (ltakeWhile (Not \<circ> is_Data) (ins p)) = ltakeWhile (Not \<circ> is_Data) (ltl (ins p))\<close>
      using LCons(2) lnull_ltakeWhile ltakeWhile.simps(4) by blast
    moreover have 2: \<open>ldropWhile (Not \<circ> is_Data) (ltl (ins p)) = LCons (Data t d) lxs\<close>
      using LCons(2,4) ldropWhile_simps(2) lhd_LCons_ltl ltakeWhile.disc(1) by metis
    moreover have \<open>(os', caps') =
    foldl (\<lambda>(os, caps) wm. ooo_input_os_caps_Watermark p wm os caps) (os1, caps1)
     (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) (ltl (ins p)))))\<close>
    proof -
      have \<open>(os', caps') = foldl (\<lambda>(os, caps) wm. ooo_input_os_caps_Watermark p wm os caps)
  (os, caps) (wm # list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) (ltl (ins p)))))\<close>
        using LCons(1,2,5) 1 lhd_LCons_ltl ltakeWhile.ctr(2) by fastforce
      thus ?thesis
        by (simp add: os1_caps1_def)
    qed
    ultimately have \<open>(step Tau)\<^sup>*\<^sup>* (ooo_input_top os1 caps1 (ins(p := ltl (ins p)))) op\<close>
      using LCons fun_upd_same fun_upd_upd by (metis (no_types, lifting))
    moreover have \<open>step Tau (ooo_input_top os caps ins) (ooo_input_top os1 caps1 (ins(p := ltl (ins p))))\<close>
    proof -
      obtain caps' os' where caps'_os'_def: \<open>(caps', os') = mint os caps p wm\<close>
        by fastforce
      let ?A = \<open>antichain (minimal_antichain (set (caps' p)))\<close>
      let ?dropped_caps = \<open>map (\<lambda>t. Cap t p) (filter (if lnull (ltl (ins p)) then \<top> else Not \<circ> frontier_less_equal ?A) (caps' p))\<close>
      have \<open>caps1 = caps'(p := filter (if lnull (ltl (ins p)) then \<bottom> else frontier_less_equal ?A) (caps' p))\<close>
        using os1_caps1_def caps'_os'_def 2 eq_LConsD ldropWhile_LNil lnull_def prod.simps(1,2)
        by (smt (verit, best))
      moreover have \<open>os1 = drop_caps os' ?dropped_caps\<close>
        using os1_caps1_def caps'_os'_def 2 eq_LConsD ldropWhile_LNil lnull_def
          operator_state.fold_congs(2) prod.case_eq_if prod.sel(1) snd_eqD
        by (smt (verit))
      ultimately show ?thesis
        using step_ooo_input_top_Silent_Watermark[of ins p wm \<open>ltl (ins p)\<close> caps' os' caps os ?A ?dropped_caps caps1 os1]
          LCons(8) 1 by (auto simp add: os1_caps1_def caps'_os'_def)
    qed
    ultimately show ?thesis
      using transitive_closurep_trans'(6) by (metis (no_types, lifting))
  qed
qed

lemma outpu_fst_foldl_ooo_input_os_caps_Watermark_Nil:
  \<open>outpu os p = [] \<Longrightarrow>
  outpu (fst (foldl (\<lambda>(os, caps) wm. (ooo_input_os_caps_Watermark p wm os caps))
    (os, caps) lxs)) p = []\<close>
  by (induction lxs arbitrary: os caps) simp_all

abbreviation ooo_inp_op where
  \<open>ooo_inp_op os n ins \<equiv>
  map_op (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0, p))) (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0, p)))
  (ooo_input_top os n ins)\<close>

abbreviation ooo_inp_summary where
  \<open>ooo_inp_summary \<equiv> (\<lambda>l1 l2.
  if l1 = Loc (0 :: 1) (Trg (0 :: 1)) \<and> l2 = Loc (0 :: 1) (Src (0 :: 1))
  then antichain {0}
  else {}\<^sub>A)\<close>

lemma
  \<open>summ sg = ooo_inp_summary \<Longrightarrow>
  dataflow_op sg (ooo_inp_op os caps ins)
  \<approx> map_op (\<lambda>(p :: 1). (0, p)) (\<lambda>p. (0, p))
    (source_op (\<lambda>p. outpu os p @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (d, t)) (lfilter is_Data (ins p))))\<close>
proof (coinduction arbitrary: sg os caps ins rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    apply (elim step_dataflow_op_elim step_map_op_elim step_ooo_input_top_elim conjE; simp; hypsubst_thin?)
    subgoal
      apply (intro exI conjI[rotated, OF wbc_base])
       apply fast
      apply (rule step_wstep)
      apply (rule step_map_op)
       apply (rule step_source_op_Out_intro)
         apply auto
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
        apply (auto intro: arg_cong[where ?f=\<open>map_op (Pair 0) (Pair 0)\<close>] arg_cong[where ?f=source_op] simp add: produce_def)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
        apply (rule refl)
       apply (auto intro: arg_cong[where ?f=\<open>map_op (Pair 0) (Pair 0)\<close>] arg_cong[where ?f=source_op] simp add: produce_def split: if_splits)
      done
    subgoal
      apply (intro exI conjI[rotated, OF wbc_base])
       apply auto
      done
    done
next
  case SIM2
  then show ?case
    apply (elim step_map_op_elim step_source_op_elim conjE; simp; hypsubst_thin?; simp)
    subgoal for x lxs
      apply (cases x; cases \<open>outpu os 0\<close>; simp)
      subgoal for d t
        apply (rule exI)
        apply (rule conjI)
         apply (rule wstep_trans(1))
          apply (rule step_Taus_dataflow_op_Taus_intro)
          apply (rule step_star_map_op)
          apply (rule step_Taus_ooo_input_top)
               apply (simp_all add: split_pairs snd_foldl)
        using lfinite_ltakeWhile apply fastforce
          apply (subgoal_tac \<open>ldropWhile (Not \<circ> is_Data) (ins 0) = LCons (Data t d) (ltl (ldropWhile (Not \<circ> is_Data) (ins 0)))\<close>)
           apply fastforce
        using lfilter_eq_LCons event.case_eq_if event.collapse(1) lfilter_eq_LConsD lmap_eq_LCons_conv
          ltl_simps(2) prod.sel(1,2)
          apply (smt (verit, ccfv_threshold) zero_one)
         apply (rule step_Out_dataflow_op_Out_Inr_intro)
         apply (rule step_map_op)
          apply (rule step_ooo_input_top_Write_Some)
            apply (simp_all add: produce_def)
         apply (drule outpu_fst_foldl_ooo_input_os_caps_Watermark_Nil)
         apply fastforce
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)
         apply (auto intro!: arg_cong[where ?f=\<open>map_op (Pair 0) (Pair 0)\<close>] arg_cong[where ?f=source_op] simp add: foldl_id2 fun_eq_iff)
        using ltl_lfilter ext comp_apply ltl_lmap ltl_simps(2) apply (metis (lifting))
        done
      subgoal
        apply (intro exI conjI[rotated, OF wbc_base])
         apply (auto intro!: arg_cong[where ?f=\<open>map_op (Pair 0) (Pair 0)\<close>] arg_cong[where ?f=source_op])
        done
      done
    done
qed

end