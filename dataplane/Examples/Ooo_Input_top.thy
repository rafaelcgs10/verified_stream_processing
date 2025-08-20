theory Ooo_Input_top

imports
  Dataplane.Timely_Infrastructure
  Source_op
begin

datatype ('t :: order, 'd) event = Data (time: 't) (data: 'd) | Watermark (time: 't)

(* TODO move *)
abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"
abbreviation "send_progress op st \<equiv> Write op None (Inl (Inl st))"
abbreviation "obtain_progress os \<equiv> (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"
abbreviation "drop_cap os cap \<equiv> (os\<lparr> inter := inter os @ [(out cap, capability.time cap, -1)] \<rparr>)"

corec ooo_input_top where
  \<open>ooo_input_top os n ins = choice3
  (Choice (cimage (\<lambda>p. case ldropWhile (Not \<circ> is_Data) (ins p) of
    LCons (Data ts d) lxs \<Rightarrow>
      let n' = n(p := foldl (+) (n p) (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs))));
          cap = Cap (n' p) p;
          os' = if ldropWhile (Not \<circ> is_Data) lxs = LNil then drop_cap os cap else delay_cap os cap ts;
          os'' = produce os' (Cap (capability.time cap + ts) p) [d]
      in Silent (ooo_input_top os'' n' (ins(p := lxs))))
    (cfilter (\<lambda>p. ldropWhile (Not \<circ> is_Data) (ins p) \<noteq> LNil) c\<UU>)))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (ooo_input_top (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) n ins) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (ooo_input_top os' n ins) st)\<close>

lemma step_ooo_input_top_elim:
  assumes \<open>step io (ooo_input_top os n ins) op\<close>
  obtains p ts d lxs n' cap os' os'' where \<open>io = Tau\<close> \<open>ldropWhile (Not \<circ> is_Data) (ins p) = LCons (Data ts d) lxs\<close>
    \<open>n' = n(p := foldl (+) (n p) (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs))))\<close>
    \<open>cap = Cap (n' p) p\<close> \<open>os' = (if ldropWhile (Not \<circ> is_Data) lxs = LNil then drop_cap os cap else delay_cap os cap ts)\<close>
    \<open>os'' = produce os' (Cap (capability.time cap + ts) p) [d]\<close> \<open>op = ooo_input_top os'' n' (ins(p := lxs))\<close> \<open>p \<notin> defaults\<close>
  | p x xs where \<open>io = Out (Some p) (Inr x)\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = ooo_input_top (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) n ins\<close> \<open>p \<notin> defaults\<close>
  | os' st where \<open>io = Out None (Inl (Inl st))\<close> \<open>obtain_progress os = (os', st)\<close> \<open>op = ooo_input_top os' n ins\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) ooo_input_top.code)
  apply (cases io)
    apply (auto split: list.splits llist.splits event.splits)
  using ldropWhile_LConsD apply fastforce+
  done

lemma step_ooo_input_top_Write_Some[intro]:
  \<open>outpu os p = x # xs \<Longrightarrow> op = ooo_input_top (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) n ins \<Longrightarrow> p \<notin> defaults \<Longrightarrow>
  step (Out (Some p) (Inr x)) (ooo_input_top os n ins) op\<close>
  apply (subst ooo_input_top.code)
  by force

lemma step_ooo_input_top_Write_None[intro]:
  \<open>(os', st) = obtain_progress os \<Longrightarrow> op = ooo_input_top os' n ins \<Longrightarrow> p \<notin> defaults \<Longrightarrow>
  step (Out None (Inl (Inl st))) (ooo_input_top os n ins) op\<close>
  apply (subst ooo_input_top.code)
  by auto

lemma step_ooo_input_top_Silent[intro]:
  \<open>ldropWhile (Not \<circ> is_Data) (ins p) = LCons (Data ts d) lxs \<Longrightarrow>
  n' = n(p := foldl (+) (n p) (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs)))) \<Longrightarrow>
  cap = Cap (n' p) p \<Longrightarrow>
  os' = (if ldropWhile (Not \<circ> is_Data) lxs = LNil then drop_cap os cap else delay_cap os cap ts) \<Longrightarrow>
  os'' = produce os' (Cap (capability.time cap + ts) p) [d] \<Longrightarrow> op = ooo_input_top os'' n' (ins(p := lxs)) \<Longrightarrow>
  p \<notin> defaults \<Longrightarrow> step Tau (ooo_input_top os n ins) op\<close>
  apply (subst ooo_input_top.code)
  apply simp
  by fastforce

corec events_to_pairs where
  \<open>events_to_pairs n lxs = (case ldropWhile (Not \<circ> is_Data) lxs of
    LNil \<Rightarrow> LNil
  | LCons (Data ts d) lxs \<Rightarrow>
    let n' = foldl (+) n (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs)))
    in LCons (d, n' + ts) (events_to_pairs n' lxs))\<close>

lemma events_to_pairs_LNil:
  \<open>events_to_pairs n lxs = LNil \<longleftrightarrow> ldropWhile (Not \<circ> is_Data) lxs = LNil\<close>
proof
  assume \<open>events_to_pairs n lxs = LNil\<close>
  hence \<open>(case ldropWhile (Not \<circ> is_Data) lxs of
    LNil \<Rightarrow> LNil
  | LCons (Data ts d) lxs \<Rightarrow>
    let n' = foldl (+) n (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs)))
    in LCons (d, n' + ts) (events_to_pairs n' lxs))
  = LNil\<close>
    by (subst (asm) events_to_pairs.code)
  thus \<open>ldropWhile (Not \<circ> is_Data) lxs = LNil\<close>
    by (auto split: llist.splits event.splits dest: ldropWhile_LConsD)
next
  assume \<open>ldropWhile (Not \<circ> is_Data) lxs = LNil\<close>
  hence \<open>(case ldropWhile (Not \<circ> is_Data) lxs of
    LNil \<Rightarrow> LNil
  | LCons (Data ts d) lxs \<Rightarrow>
    let n' = foldl (+) n (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs)))
    in LCons (d, n' + ts) (events_to_pairs n' lxs))
  = LNil\<close>
    by simp
  thus \<open>events_to_pairs n lxs = LNil\<close>
    by (subst events_to_pairs.code)
qed

lemma event_to_Data:
  assumes \<open>events_to_pairs n lxs = LCons x lxs'\<close>
  obtains ts d lxs'' n' where \<open>ldropWhile (Not \<circ> is_Data) lxs = LCons (Data ts d) lxs''\<close>
    \<open>n' = foldl (+) n (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs'')))\<close>
    \<open>x = (d, n' + ts)\<close> \<open>lxs' = events_to_pairs n' lxs''\<close>
proof (atomize_elim)
  have \<open>(case ldropWhile (Not \<circ> is_Data) lxs of
    LNil \<Rightarrow> LNil
  | LCons (Data ts d) lxs \<Rightarrow>
    let n' = foldl (+) n (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs)))
    in LCons (d, n' + ts) (events_to_pairs n' lxs))
  = LCons x lxs'\<close> using assms by (subst (asm) events_to_pairs.code)
  thus \<open>\<exists>ts d lxs'' n'.
       ldropWhile (Not \<circ> is_Data) lxs = LCons (Data ts d) lxs'' \<and>
       n' = foldl (+) n (list_of (lmap event.time (ltakeWhile (Not \<circ> is_Data) lxs''))) \<and>
       x = (d, n' + ts) \<and> lxs' = events_to_pairs n' lxs''\<close>
    by (auto split: llist.splits event.splits dest: ldropWhile_LConsD)
qed

abbreviation ooo_inp_op where
  \<open>ooo_inp_op os n ins \<equiv>
  map_op (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0, p))) (case_option (Inl (0 :: 1)) (\<lambda>p. Inr (0, p)))
  (ooo_input_top os n ins)\<close>

abbreviation ooo_inp_summary where
  \<open>ooo_inp_summary \<equiv> (\<lambda>l1 l2.
   if l1 = Loc (0 :: 1) (Trg (0 :: 1)) \<and> l2 = Loc (0 :: 1)  (Src (0 :: 1))
   then frontier {#0 :: nat#}\<^sub>z
   else {}\<^sub>A)\<close>

lemma
  \<open>summ sg = ooo_inp_summary \<Longrightarrow>
  dataflow_op sg (ooo_inp_op os1 n ins)
  \<approx> map_op (\<lambda>(p :: 1). (0, p)) (\<lambda>p. (0, p)) (source_op (\<lambda>p. outpu os1 p @@- events_to_pairs (n p) (ins p)))\<close>
proof (coinduction arbitrary: sg os1 n ins rule: wbisim_coinduct_upto'')
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
         apply (rule refl)
        apply (rule arg_cong[where ?f=\<open>map_op (Pair 0) (Pair 0)\<close>])
        apply (rule arg_cong[where ?f=source_op])
        apply (simp add: fun_eq_iff produce_def)
        apply (rule arg_cong[where ?f=\<open>\<lambda>x. outpu os1 1 @@- x\<close>])
        apply (subst events_to_pairs.code)
        apply simp_all
      done
    subgoal
      apply (intro exI conjI[rotated, OF wbc_base])
       apply auto
      done
    done
next
  case SIM2
  then show ?case
    apply (elim step_map_op_elim step_source_op_elim conjE; simp; hypsubst_thin?)
    subgoal for _ _ x lxs
      apply (cases \<open>outpu os1 0\<close>; simp)
      subgoal
        apply (erule event_to_Data)
        subgoal for ts d lxs' n'
          apply (rule exI[of _ \<open>dataflow_op sg (map_op (case_option (Inl 1) (\<lambda>p. Inr (0, 1))) (case_option (Inl 1) (\<lambda>p. Inr (0, 1)))
  (ooo_input_top ((produce (if ldropWhile (Not \<circ> is_Data) lxs' = LNil then drop_cap os1 (Cap n' 0) else delay_cap os1 (Cap n' 0) (snd x - n')) (Cap (snd x) 0) [fst x])\<lparr>outpu := (outpu os1)(0 := [])\<rparr>) (\<lambda>_. n') (ins(0 := lxs'))))\<close>])
          apply (rule conjI)
           apply (rule wstep_trans_base(1))
            apply (rule step_Tau_dataflow_op_Tau_intro)
            apply (rule step_map_op)
             apply (rule step_ooo_input_top_Silent)
                   apply (auto simp add: produce_def)
             apply (rule step_map_op)
              apply (rule step_ooo_input_top_Write_Some)
                apply simp_all
             apply (rule arg_cong3[where ?f=ooo_input_top])
               apply (simp_all add: fun_eq_iff)
            apply (rule step_map_op)
             apply (rule step_ooo_input_top_Write_Some)
               apply simp_all
            apply (rule arg_cong3[where ?f=ooo_input_top])
              apply (simp_all add: fun_eq_iff)
           apply (rule wbc_base)
           apply (intro exI conjI)
              apply (auto simp add: fun_upd_def)
          apply (rule wbc_base)
          apply (intro exI conjI)
             apply (auto simp add: fun_upd_def)
          done
        done
      subgoal
        apply (intro exI conjI[rotated, OF wbc_base])
         apply (auto intro!: arg_cong[where ?f=\<open>map_op (Pair 0) (Pair 0)\<close>] arg_cong[where ?f=source_op])
        done
      done
    done
qed

end