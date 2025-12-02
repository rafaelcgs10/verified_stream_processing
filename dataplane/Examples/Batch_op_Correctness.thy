theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Ooo_Input_op
  Batch_op
  "../MyProduct_Instances"
  "../AntichainOrder"
   Dataplane.LList_Haskell_Setup
  Traces_op
begin

partial_function (llist) batch_fun_spec where
 "batch_fun_spec f buf caps lxs = (case lxs of
    LNil \<Rightarrow> (
    let compl_batches = (\<lambda> t. map fst ((filter (\<lambda> (d, t'). t' = t)) buf)) in
    let outs =  map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (rmdups {} (map snd buf)) in
    llist_of outs)
  | LCons (Data t (d :: 'd1)) lxs' \<Rightarrow> batch_fun_spec f ((d, t) # buf) caps lxs'
  | LCons (Mint t) lxs' \<Rightarrow> batch_fun_spec f buf (caps @ [t]) lxs'
  | LCons (Drop t) lxs' \<Rightarrow> (
    let below_caps = filter (\<lambda> t'. \<not> frontier_less_equal (frontier (zmset_of (mset caps - {# t #}))) t') (rmdups {} (map snd buf)) in
    let compl_batches = (\<lambda> t. map fst (filter (\<lambda> (d, t'). t' = t \<and> t' \<in> set below_caps) buf)) in
    let outs = concat (map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (filter (\<lambda> t. t \<in> set below_caps) (rmdups {} (map snd buf)))) in
    let buf' = filter (\<lambda> (d, t). t \<notin> set below_caps) buf in
    LCons outs (batch_fun_spec f buf' (remove1 t caps) lxs')))"

fun foo where
 "foo f lxs buf caps = (case lxs of
    [] \<Rightarrow> (
    let below_caps = filter (\<lambda> t'. \<not> frontier_less_equal (frontier (zmset_of (mset caps))) t') (rmdups {} (map snd buf)) in
    let compl_batches = (\<lambda> t. map fst (filter (\<lambda> (d, t'). t' = t \<and> t' \<in> set below_caps) buf)) in
    let outs = concat (map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (filter (\<lambda> t. t \<in> set below_caps) (rmdups {} (map snd buf)))) in
    let buf' = filter (\<lambda> (d, t). t \<notin> set below_caps) buf in
    (outs, buf', caps))
  | (Data t (d :: 'd1)) # lxs' \<Rightarrow> foo f lxs' ((d, t) # buf) caps
  | (Mint t) # lxs' \<Rightarrow> foo f lxs' buf (caps @ [t])
  | (Drop t) # lxs' \<Rightarrow> foo f lxs' buf (remove1 t caps))"

declare batch_fun_spec.simps[code]

(* filter cUNIV to not have empty outputs*)
corec spec_op where
  "spec_op m (f :: 'a list \<Rightarrow> 'b list) lxs buf caps outp = choice2
   (Choice ((cimage (\<lambda> n. 
     let (outs, buf', caps') = foo f (ltaken n lxs) buf caps in
     (case outp @ outs of x # xs \<Rightarrow> (Write (spec_op m f (ldropn n lxs) buf' caps' xs) 1 x))) (
      cfilter (\<lambda> n. fst (foo f (ltaken n lxs) buf caps) \<noteq> [])
      (cset_of_llist (llist_of ([0..< Suc m])))))))
    (case outp of 
       [] \<Rightarrow> \<oslash>
     | x # xs \<Rightarrow> Write (spec_op m f lxs buf caps xs) 1 x)"

abbreviation "t0 \<equiv> MyPair (0 :: nat) (0 :: nat)"
abbreviation "t_1_0 \<equiv> MyPair (Suc 0) (0 :: nat)"
abbreviation "t_0_1 \<equiv> MyPair (0 :: nat) (Suc 0)"
abbreviation "t_1_1 \<equiv> MyPair (Suc 0) (Suc 0)"

lemma t0_is_bot[simp]:
  "\<bottom> = MyPair (0 :: nat) (0 :: nat)"
  by (simp add: bot_myprod_def bot_nat_def)

abbreviation "inps1 \<equiv> llist_of [Mint 1, Data 1 44, Data 1 6, Data (0 :: nat) (0 :: nat), Data 0 42, Drop 0, Data 1 43]"

abbreviation "list_inps2 \<equiv> 
 [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"

value "[frontier {# t0, t_1_1, t_1_0, t_0_1 #}\<^sub>z, frontier {# t_1_1, t_1_0, t_0_1 #}\<^sub>z, frontier {# t_1_0, t_0_1 #}\<^sub>z, frontier {# t_0_1 #}\<^sub>z, frontier {#}\<^sub>z] "
value "[frontier {# t0, t_1_1, t_1_0, t_0_1 #}\<^sub>z, frontier {# t_1_0, t_0_1 #}\<^sub>z, frontier {# t_0_1 #}\<^sub>z, frontier {#}\<^sub>z] "
value "[frontier {# t0, t_1_1, t_1_0, t_0_1 #}\<^sub>z, frontier {# t_0_1 #}\<^sub>z, frontier {#}\<^sub>z] "
value "[frontier {# t0, t_1_1, t_1_0, t_0_1 #}\<^sub>z, frontier {#}\<^sub>z] "

abbreviation "inps2 \<equiv> llist_of list_inps2"

abbreviation \<open>r1 \<equiv> lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) [] [\<bottom>] inps1)\<close>
value r1

abbreviation \<open>r2 \<equiv> lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) [] [\<bottom>] inps2)\<close>
value r2

abbreviation "spec_op_test \<equiv> (spec_op (length list_inps2) (\<lambda> b. [Max (set b)]) inps2 [] [\<bottom>] []) :: (1, 1, nat \<times> (nat, nat) myprod) op"


record ('nid, 'p, 't, 'd) dataplane_state =
  ecaps :: "('nid, 'p) location \<Rightarrow> 't zmultiset"
  icaps :: "('nid, 'p) location \<Rightarrow> 't zmultiset"
  cbufs :: "'nid \<Rightarrow> 'p \<Rightarrow> ('d \<times> 't) buf"
  obufs :: "'nid \<Rightarrow> 'p \<Rightarrow> ('d \<times> 't) buf"
  ibufs :: "'nid \<Rightarrow> 'p \<Rightarrow> ('d \<times> 't) buf"
  logcs :: "'nid \<Rightarrow> (('p \<Rightarrow> 't antichain) \<Rightarrow> ('p \<Rightarrow> ('d \<times> 't) buf) \<Rightarrow> ('p \<Rightarrow> 't zmultiset) \<Rightarrow>
                    ('p \<Rightarrow> ('d \<times> 't) buf) \<times> ('p \<Rightarrow> ('d \<times> 't) buf) \<times> ('p \<Rightarrow> 't zmultiset)) stream"

abbreviation "dataplane_state ec ic cb ob ib lgc \<equiv> \<lparr>
  ecaps = ec,
  icaps = ic,
  cbufs = cb,
  obufs = ob,
  ibufs = ib,
  logcs = lgc
 \<rparr>"

definition caps_report_action where
  "caps_report_action ds ds' = 
  (\<exists> l. ds' = ds\<lparr>ecaps := (ecaps ds)(l := ecaps ds l + icaps ds l), icaps := (icaps ds)(l := {#}\<^sub>z) \<rparr>)"

definition consumes_action where
  "consumes_action summary ds ds' = (\<exists> nid pfx sfx icaps' icaps''.
   (\<forall> p. pfx p @ sfx p = cbufs ds nid p) \<and>
   icaps' = (\<lambda> l. case l of Loc nid' (Trg p) \<Rightarrow> if nid = nid' then to_zmset (map snd (pfx p)) else {#}\<^sub>z | _ \<Rightarrow> {#}\<^sub>z) \<and>
   icaps'' = (\<lambda> l'. sum (\<lambda> l. icaps' l -++- (summary l l')) UNIV) \<and>
   ds' = ds\<lparr> 
     cbufs := (cbufs ds)(nid := \<lambda> p. sfx p),
     ibufs := (ibufs ds)(nid := \<lambda> p. ibufs ds nid p @ pfx p),
     icaps := (\<lambda> l. icaps ds l - icaps' l + icaps'' l)
    \<rparr>)"

definition implied_frontier where
  "implied_frontier summary caps loc = 
  frontier (\<Sum>loc'\<in>UNIV. after_summary (dataflow_topology.zmset_frontier (caps loc')) (dataflow_topology.path_summary summary loc' loc))"
declare implied_frontier_def[code del]

definition "sound_output outs caps = (\<forall> p t d. (d, t) \<in> set (outs p) \<longrightarrow> zcount (caps p) t > 0)"

definition "caps_to_location_Src nid caps l = (case l of Loc nid' (Src p) \<Rightarrow> if nid' = nid then caps p else {#}\<^sub>z | _ \<Rightarrow> {#}\<^sub>z)"

lemma caps_to_location_Src_add_simp[simp]:
  "caps_to_location_Src nid M1 l + caps_to_location_Src nid M2 l = 
   caps_to_location_Src nid (\<lambda> p. M1 p + M2 p) l"
  unfolding caps_to_location_Src_def
  by (auto split: location.splits port.splits)

lemma caps_to_location_Src_diff_location[simp]:
  "nid \<noteq> node l \<Longrightarrow> caps_to_location_Src nid M l = {#}\<^sub>z"
  unfolding caps_to_location_Src_def
  by (auto split: location.splits port.splits)


definition "outputs_to_internal_channels summary nid outs nid' p' =
  (concat (map (\<lambda> p. if summary (Loc nid (Src p)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A then outs p else []) Enum.enum))"

lemma outputs_to_internal_channels_empty_simp[simp]:
  "outputs_to_internal_channels summary nid (\<lambda> _. []) = (\<lambda> _ _. [])"
  unfolding outputs_to_internal_channels_def
  apply force
  done

definition "outputs_to_visible_channels summary nid outs nid' p' =
  (if nid = nid' \<and> (\<forall> l. summary (Loc nid' (Src p')) l = {}\<^sub>A) then outs p' else [])"

lemma outputs_to_visible_channels_empty_simp[simp]:
  "outputs_to_visible_channels summary nid (\<lambda> _. []) = (\<lambda> _ _. [])"
  unfolding outputs_to_visible_channels_def
  apply (rule ext)+
  apply clarsimp
  done



definition produces_action where
  "produces_action summary ds ds' = 
  (\<exists> nid pfxbuf pfxbuf' sfxbuf outs  ccaps f imp_fron caps ccaps_l cbufs' obufs'.
    f = shd (logcs ds nid) \<and>
    (\<forall> p. pfxbuf p @ sfxbuf p = ibufs ds nid p) \<and>
    caps = (\<lambda> p. icaps ds (Loc nid (Src p)) + ecaps ds (Loc nid (Src p))) \<and>
    imp_fron = (\<lambda> p. implied_frontier summary (ecaps ds) (Loc nid (Trg p))) \<and>
    (pfxbuf', outs, ccaps) = f imp_fron pfxbuf caps \<and> 
    ccaps_l = caps_to_location_Src nid ccaps \<and>
    cbufs' = outputs_to_internal_channels summary nid outs \<and>
    obufs' = outputs_to_visible_channels summary nid outs \<and>
    sound_output outs caps \<and>
    ds' = ds\<lparr> 
     ibufs := (ibufs ds)(nid := (\<lambda> p. pfxbuf' p @ sfxbuf p)),
     icaps := (\<lambda> l. icaps ds l + ccaps_l l),
     cbufs := (\<lambda> nid p. cbufs ds nid p @ cbufs' nid p),
     logcs := (logcs ds)(nid := stl (logcs ds nid)),
     obufs := (\<lambda> nid p. obufs ds nid p @ obufs' nid p)
     \<rparr>)"

definition timely_action where
  "timely_action summary ds ds' =
  (caps_report_action ds ds' \<or> consumes_action summary ds ds' \<or> produces_action summary ds ds')"

coinductive timely_trace for summary where                                                                         
  tt_silent[intro!]: 
  "timely_action summary ds ds' \<Longrightarrow> timely_trace summary n ds' outs \<Longrightarrow> timely_trace summary (Suc n) ds outs"
| tt_visible[intro!]: 
  "outs (nid, p) = LCons x lxs \<Longrightarrow>
   outs' = outs((nid, p) := lxs) \<Longrightarrow>
   ds' = ds\<lparr> obufs := \<lambda> nid' p'. if nid' = nid \<and> p' = p then xs else obufs ds nid' p' \<rparr> \<Longrightarrow>
   obufs ds nid p = x # xs \<Longrightarrow> timely_trace summary n ds' outs' \<Longrightarrow> timely_trace summary 0 ds outs"
| tt_stop[intro!]:
  "(\<forall> nid p. obufs ds nid p = []) \<Longrightarrow>timely_trace summary 0 ds outs"

primcorec lgc_input where
  "lgc_input inps = SCons (\<lambda> imp_fron pfxbuf caps.
  (pfxbuf,
    \<lambda> p. case inps p of LCons (Data t d) lxs \<Rightarrow> [(d, t)] | _ \<Rightarrow> [],
    \<lambda> p. case inps p of
       LCons (Mint t) lxs \<Rightarrow> {# t #}\<^sub>z
     | LCons (Drop t) lxs \<Rightarrow> - {# t #}\<^sub>z
     | LCons _ _ \<Rightarrow> {#}\<^sub>z
     | LNil \<Rightarrow> - caps p )
   ) (lgc_input (\<lambda> p. ltl (inps p)))"

definition "my_max t pfxbuf = Max (set (map fst (filter (\<lambda> (d, t'). t = t') (pfxbuf 1))))"

abbreviation "lgc_max \<equiv> sconst (\<lambda> imp_fron pfxbuf caps.
    let below_caps = filter_zmset (\<lambda> t'. \<not> frontier_less_equal (imp_fron 1) t') (caps 1) in
    let ts = rmdups {} (map snd (filter (\<lambda> (d, t). t \<in>#\<^sub>z below_caps) (pfxbuf 1))) in  (
    \<lambda> p. filter (\<lambda> (d, t). t \<notin>#\<^sub>z below_caps) (pfxbuf 1),
    \<lambda> p. map (\<lambda> t. (my_max t pfxbuf, t)) ts,
    \<lambda> p. - below_caps )
   )"

abbreviation "DS \<equiv> dataplane_state (\<lambda> l. case l of Loc nid (Src p) \<Rightarrow> {# \<bottom> #}\<^sub>z | _ \<Rightarrow> {#}\<^sub>z) (\<lambda> _. {#}\<^sub>z) (\<lambda> _ _. []) (\<lambda> _ _. []) (\<lambda> _ _. []) (\<lambda> (nid :: 2). if nid = 0 then lgc_input (\<lambda> _ :: 1. inps2) else lgc_max)"

definition "my_summ = (\<lambda> l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then antichain_from_list [\<bottom>]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then antichain_from_list [\<bottom>]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [\<bottom>]
   else {}\<^sub>A)"


lemma my_summ_simps[simp]:
  "my_summ l l = {}\<^sub>A"
  "my_summ (Loc 0 (Trg 1)) (Loc 0 (Src 1)) = antichain_from_list [\<bottom>]"
  "my_summ (Loc 0 (Trg 1)) (Loc 1 (Trg 1)) = {}\<^sub>A"
  "my_summ (Loc 0 (Trg 1)) (Loc 1 (Src 1)) = {}\<^sub>A"
  "my_summ (Loc 0 (Src 1)) (Loc 1 (Trg 1)) = antichain_from_list [\<bottom>]"
  "my_summ (Loc 1 (Trg 1)) (Loc 1 (Src 1)) = antichain_from_list [\<bottom>]"
  unfolding my_summ_def
       apply auto
  done

lemma path_weight_my_summ_simps[simp]:
  "graph.path_weight my_summ l1 l2 = (
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1)) 
   then antichain_from_list [\<bottom>]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then antichain_from_list [\<bottom>]
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [\<bottom>]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 1 (Trg 0)
   then antichain_from_list [\<bottom>]
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [\<bottom>]
   else if l1 = Loc 0 (Src 0) \<and> l2 = Loc 1 (Src 0)
   then antichain_from_list [\<bottom>]
   else if l1 = l2
   then antichain_from_list [\<bottom>]
   else {}\<^sub>A)"
  oops

lemma implied_frontier_my_summ[simp]:
  "implied_frontier my_summ caps (Loc 1 (Trg 1)) = 
   frontier (dataflow_topology.zmset_frontier (caps (Loc 1 (Trg 1))) +
   dataflow_topology.zmset_frontier (caps (Loc 0 (Src 1))) +
   dataflow_topology.zmset_frontier (caps (Loc 0 (Trg 1))))"
(*   unfolding implied_frontier_def
  using loc_2_1_cases[where l=loc] apply -
  apply (elim disjE)
  subgoal
    apply simp
 *)
  sorry

abbreviation "my_14 \<equiv> Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))"

lemma
  "timely_trace my_summ my_14 DS (\<lambda> (nid, p). if nid = 0 then LNil else LCons (10, MyPair 1 1) (LCons (7, MyPair 0 1) (LCons (3, MyPair 1 0) LNil)))"
  apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 0])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. {# t_1_0 #}\<^sub>z"])
   apply clarsimp
  apply (simp add: sound_output_def)

  apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 0])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. {# t_0_1 #}\<^sub>z"])
  apply (simp add: sound_output_def)

  apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 0])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. {# t_1_1 #}\<^sub>z"])
    apply (simp add: sound_output_def)


  apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 0])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. - {# t0 #}\<^sub>z"])
  apply (simp add: sound_output_def)

  apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
  apply (rule exI[of _ 0])
   apply (intro exI conjI)
            apply (rule refl)+
           apply simp
          apply (rule refl)+
        apply simp
       apply simp
      apply (rule refl)+
  subgoal
    unfolding sound_output_def
    apply simp
    apply code_simp
    done
      apply (rule refl)+


  apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
  apply (rule exI[of _ 0])
   apply (intro exI conjI)
            apply (rule refl)+
           apply simp
          apply (rule refl)+
        apply simp
       apply simp
      apply (rule refl)+
  subgoal
    unfolding sound_output_def
    apply simp
    done
   apply (rule refl)+
  apply simp

  apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 0])
   apply (intro exI conjI)
            apply (rule refl)+
           apply simp
          apply (rule refl)+
        apply simp
       apply simp
      apply (rule refl)+
  subgoal
    unfolding sound_output_def
    apply simp
    apply code_simp
    done
   apply (rule refl)+
  apply simp

  apply (rule tt_silent)
 unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 0])
   apply (intro exI conjI)
            apply (rule refl)+
           apply simp
          apply (rule refl)+
        apply simp
       apply simp
      apply (rule refl)+
  subgoal
    unfolding sound_output_def
    apply simp
    apply code_simp
    done
   apply (rule refl)+
  apply clarsimp

 apply (rule tt_silent)
 unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 0])
   apply (intro exI conjI)
            apply (rule refl)+
           apply simp
          apply (rule refl)+
        apply simp
       apply simp
      apply (rule refl)+
  subgoal
    unfolding sound_output_def
    apply simp
    done
   apply (rule refl)+
  apply clarsimp

 apply (rule tt_silent)
 unfolding timely_action_def
   apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 0])
   apply (intro exI conjI)
            apply (rule refl)+
           apply simp
          apply (rule refl)+
        apply simp
       apply simp
      apply (rule refl)+
  subgoal
    unfolding sound_output_def
    apply simp
    done
   apply (rule refl)+
  apply clarsimp

 apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI1)
  unfolding caps_report_action_def
   apply (rule exI[of _ "Loc 0 (Src 1)"])
   apply simp

 apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI2)
   apply (rule disjI1)
  unfolding consumes_action_def
   apply (rule exI[of _ 1])
   apply (rule exI[of _ "\<lambda> _. [(10, t_1_1), (7, t_0_1), (3, t_1_0)]"])
  apply (rule exI[of _ "\<lambda> _. []"])
   apply (intro exI conjI)
      apply (clarsimp simp add: outputs_to_internal_channels_def)
      apply (intro conjI impI)
  subgoal
    unfolding antichain_from_list_antichain antichain_from_list_is_empty my_summ_def
    apply simp
    apply (subst (asm) antichain_not_empty)
      apply (auto simp add: incomparable_def)
    done
  subgoal premises
    by code_simp
  apply (rule refl)+
  apply simp

 apply (rule tt_silent)
  unfolding timely_action_def
   apply (rule disjI1)
  unfolding caps_report_action_def
   apply (rule exI[of _ "Loc 1 (Trg 1)"])
   apply (rule refl)
  apply simp

  apply (rule tt_silent)
 unfolding timely_action_def
  apply (rule disjI2)+
  unfolding produces_action_def
   apply (rule exI[of _ 1])
   apply (rule exI[of _ "\<lambda> _. [(10, t_1_1), (7, t_0_1), (3, t_1_0)]"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. []"])
   apply (rule exI[of _ "\<lambda> _. [(10, t_1_1), (7, t_0_1), (3, t_1_0)]"])
   apply (rule exI[of _ "\<lambda> _. - {# t_1_1, t_0_1, t_1_0, t0 #}\<^sub>z"])
   apply (intro exI conjI)
            apply (rule refl)+
           apply simp
          apply (rule refl)+
  subgoal
    apply (simp only: prod_eq_iff)
    subgoal
      apply (simp add: neg_neg_multiset caps_to_location_Src_def)
      apply (simp add: my_max_def caps_to_location_Src_def uminus_add_zmset add_del_zmset weird_singleton)
      done
    done
              apply (rule refl)+
  subgoal
    unfolding sound_output_def my_summ_def
    apply (auto simp add: weird_singleton split: location.splits)
    done
              apply (rule refl)+
  apply simp
  apply (rule tt_visible[where p=1 and nid=1])
      apply simp
  apply (rule refl)+
   apply (simp add: outputs_to_visible_channels_def my_summ_def)

  apply (rule tt_visible[where p=1 and nid=1])
      apply simp
  apply (rule refl)+
   apply (simp add: outputs_to_visible_channels_def my_summ_def)

  apply (rule tt_visible[where p=1 and nid=1])
      apply simp
  apply (rule refl)+
   apply (simp add: outputs_to_visible_channels_def my_summ_def)

  apply (rule tt_stop)
  apply (intro impI allI conjI)
  apply simp
  apply (intro impI allI conjI)
  defer
      apply (auto simp add: antichain_from_list_antichain weird_singleton outputs_to_visible_channels_def my_summ_def)[1]
  apply (metis empty_antichain.rep_eq insert_not_empty set_antichain_antichain_singleton)
      apply (auto simp add: antichain_from_list_antichain weird_singleton outputs_to_visible_channels_def my_summ_def)[1]
  apply (metis empty_antichain.rep_eq insert_not_empty set_antichain_antichain_singleton)
      apply (auto simp add: outputs_to_visible_channels_def antichain_from_list_antichain weird_singleton my_summ_def)
  apply (metis empty_antichain.rep_eq insert_not_empty set_antichain_antichain_singleton)
  done

lemma
  assumes \<open>(x, t) \<in> lset (outs (1, 1))\<close>
  and \<open>SM = dataplane_state ec ic cb ob ib (\<lambda> (nid :: 2). if nid = 0 then lgc_input (\<lambda> _ :: 1. inps) else lgc_max)\<close>
  and \<open>ob = (\<lambda> nid p. if nid = 1 \<and> p = 1 then ob1 else [])\<close>
  and \<open>timely_trace my_summ n SM outs\<close>
obtains \<open>x \<in> (Data t) -` lset (map (\<lambda> (d, t). Data t d) (ib 1 1) @@- map (\<lambda> (d, t). Data t d) (cb 1 1) @@- inps)\<close> | \<open>(x, t) \<in> set ob1\<close>
  using assms apply -
  apply hypsubst_thin
  apply atomize_elim
    apply (induct "outs (1, 1)" rule: lset_induct)
  subgoal for lxs
    apply (drule sym)
      apply simp
      apply (induct n)
      apply simp_all
    subgoal
      apply (erule timely_trace.cases)
        apply simp_all
      subgoal for outsa nid xa lxsa outs' ds' xs ds n
        apply hypsubst_thin
        apply (rule disjI2)+
        apply (metis (mono_tags, lifting) dataplane_state.simps(4) list.distinct(1) list.set_intros(1) llist.inject)
        done
      subgoal for ds outs'
        apply hypsubst_thin

  find_theorems lset lnth

end

term "[Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"

abbreviation init_input_state where
"init_input_state su inps \<equiv> \<lparr> 
   summar = su,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = undefined,
   ocaps = (\<lambda> _. [\<bottom>]),
   initia = False,
   nfron = False,
   en1 = Inl,
   de1 = projl,
   es = inps
   \<rparr>"
abbreviation "l1 inps \<equiv> Logic (ooo_input_op {|1|} (init_input_state default_internal_summary inps)) default_internal_summary"

abbreviation init_operator_state_ty2 where
"init_operator_state_ty2 su \<equiv> \<lparr> 
   summar = su,
   consu = [],
   inter = [],
   produ = [],
   input = (\<lambda> _. []),
   outpu = (\<lambda> _. []),
   front = undefined,
   ocaps = (\<lambda> _. [\<bottom>]),
   initia = False,
   nfron = False,
   en1 = Inl,
   de1 = projl,
   en2 = Inr,
   de2 = projr
   \<rparr>"
abbreviation "l2 \<equiv> Logic (batch_fun_op (init_operator_state_ty2 default_internal_summary) (\<lambda> b. if b = [] then trace (STR ''Empty batch! ! !'') [] else [Max (set b)])) default_internal_summary"

abbreviation "test_dt2 \<equiv> Comp [(0, 1) \<mapsto> (0, 1)] (l1 (\<lambda> _. inps2)) l2"

abbreviation "test_op2 \<equiv> compile_dataflow test_dt2 :: (2 \<times> 1, 2 \<times> 1, _) op"


term Set.the_elem
(* 
value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op1)"
 *)
value r1

value [GHC] "crmdups id {|Suc 0, Suc 0|}"


definition "my_test =  (trace_exec test_op2)"

value [GHC] my_test


value "frontier {# t_1_1, t_0_1, t_1_0 #}\<^sub>z"

term DEBUG

definition "looping = check_prefix [VOut (1, 1) (Inr 3, MyPair 1 0)] test_op2"

 (* 
value [GHC] "check_prefix [VOut (1, 1) (Inr 10, MyPair 1 1)] test_op2"
 *)

value [GHC] "check_prefix [VOut (1, 1) (Inr 7, MyPair 0 1)] test_op2"
(* 
value [GHC] "check_prefix [VOut (1, 1) (Inr 3, MyPair 1 0)] test_op2"
 *)

value [GHC] "trace_exec spec_op_test"

print_classes

(* 
value [GHC] "check_prefix [VOut 1 (7, MyPair 0 1)] spec_op_test"
value [GHC] "check_prefix [VOut 1 (3, MyPair 1 0)] spec_op_test"
value [GHC] "check_prefix [VOut 1 (10, MyPair 1 1)] spec_op_test"

 *)


(*
 value [GHC] "check_prefix [VOut (1, 1) (Inr 3, MyPair 1 0)] test_op2"
 *)



(* value [GHC] "approx_in 30 [VOut (1, 1) (Inr 3, MyPair 1 0)] test_op2"

 *)
term DEBUG

thm cUnion_code

term cUn
end

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "tt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_fun_op os f)"

abbreviation "inp_tt_op os1 cbuf os2 f \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] cbuf (inp_op (os1\<lparr> en1 := Inl \<rparr>)) (tt_op (os2\<lparr> de1 := projl, en2 := Inr \<rparr>) f))"


definition \<open>subgraph_inv dtt cgs c = (let (su, _) = compile_dataflow_tree dtt in
 \<lparr> pt_tr = change_multiplicities su cgs c,
   edges = (\<lambda> l1. [l2 \<leftarrow> Enum.enum. \<not> is_empty_antichain (su l1 l2) \<and> is_Src (port l1) \<and> is_Trg (port l2) ]),
   summ = su \<rparr>)\<close>



term "[Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)]"

lemma dataflow_op_inp_tt_op_wbisim_source_op_aux:
  fixes lxs :: \<open>('t :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}, 'd1) event llist\<close>
  and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
  and os1 :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
  and os2 :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
assumes
  buffers_inv: 
  \<open>es os1 1 = lxs\<close>
  \<open>outpu os1 1 = map (\<lambda> (d, t). (Inl d, t)) out_os1\<close>
  \<open>input os2 1 = map (\<lambda> (d, t). (Inl d, t)) inp_os2\<close>
  \<open>buf = out_os1 @ cbuf @ inp_os2\<close>
  and
  subgraph_inv:
  \<open>(a, st1) = obtain_progress os1\<close>   
  \<open>(b, st2) = obtain_progress os2\<close>
  \<open>cgs = extract_progress 0 (edges sg) st1 @ extract_progress 1 (edges sg) st2\<close>
  \<open>sg = subgraph_inv test_dt1 cgs c\<close>
  \<open>c' = pt_tr sg\<close>
  and
  c_pts_inv:
  \<open>c_pts c' (Loc 0 (Trg 1)) = {#}\<^sub>z\<close>
  \<open>c_pts c' (Loc 0 (Src 1)) = zmset_of (mset (ocaps os1 1))\<close>
  \<open>c_pts c' (Loc 1 (Trg 0)) = zmset_of (mset (map snd buf))\<close>
  \<open>c_pts c' (Loc 1 (Src 1)) = zmset_of (mset (ocaps os2 1))\<close>
  and
  c_imp_inv:
  \<open>front os2 1 \<le> frontier (c_imp c (Loc 1 (Trg 0)))\<close>

shows 
  \<open>dataflow_op sg (inp_tt_op os1 (\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (Inl d, t)) cbuf) os2 f) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. outpu os2 1 @@- lmap (\<lambda> (d, t). (Inr d, t)) (lconcat (batch_fun_spec f lxs buf caps))))\<close>

  term "ocaps os1 1"

end
