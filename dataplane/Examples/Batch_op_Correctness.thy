theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Source_op
  Ooo_Input_op
  Batch_op
  "../MyProduct_Instances"
  "../AntichainOrder"
   Dataplane.LList_Haskell_Setup
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

definition "t0 \<equiv> \<bottom>"
definition "t_1_0 \<equiv> MyPair (Suc 0) (0 :: nat)"
definition "t_0_1 \<equiv> MyPair (0 :: nat) (Suc 0)"
definition "t_1_1 \<equiv> MyPair (Suc 0) (Suc 0)"

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

record ('nid, 'p, 't, 'd) timely_state =
  ecaps :: "('nid, 'p) location \<Rightarrow> 't zmultiset"
  icaps :: "('nid, 'p) location \<Rightarrow> 't zmultiset"
  cbufs :: "'nid \<Rightarrow> 'p \<Rightarrow> ('d \<times> 't) buf"

(*   opact :: "('nid, 'p) location \<Rightarrow> 'p \<Rightarrow> ('p \<Rightarrow> 't antichain) \<Rightarrow> ('d \<times> 't) option"
 *)
(* 
definition source_op_action where
  "source_op_act inps p f = (case inps p of LCons (Data t d) lxs \<Rightarrow> Some (d, t))"
 *)

definition caps_report_action where
  "caps_report_action ts ts' = 
  (\<exists> l. ts' = ts\<lparr>ecaps := (ecaps ts)(l := ecaps ts l + icaps ts l), icaps := (icaps ts)(l := {#}\<^sub>z) \<rparr>)"

definition operator_action where
  "operator_action ts ts' = 
  (\<exists> nid prfbuf sfxbuf ys prfbuf' caps_cgs.
    (\<forall> p. prfbuf p @ sfxbuf p = cbufs ts nid p) \<and>
    ts' = ts\<lparr> 
     cbufs := (cbufs ts)(nid := (\<lambda> p. prfbuf' p @ sfxbuf p)),
     icaps := (icaps ts)(\<lambda> p. undefined) \<rparr>)"



definition timely_silent_action where
  "timely_silent_action ts ts' = (caps_report_action ts ts')"

coinductive timely_trace where                                                                         
  tt_silent[intro]: 
  "timely_trace summa f n ts' \<Longrightarrow> timely_silent_action ts ts' \<Longrightarrow> timely_trace summa f (Suc n) ts"


(* | tt_Mint[intro!]: 
  "timely_trace sid summa R n bufs (caps(Loc sid (Src p) := caps (Loc sid (Src p)) + {# t #}\<^sub>z)) (inps(p := lxs)) outs \<Longrightarrow> 
   inps p = LCons (Mint t) lxs \<Longrightarrow>
   timely_trace sid summa R (Suc n) buf caps inps outs"
| tt_Drop[intro!]: 
  "timely_trace sid summa R n bufs (caps(Loc sid (Src p) := caps (Loc sid (Src p)) - {# t #}\<^sub>z)) (inps(p := lxs)) outs \<Longrightarrow> 
   inps p = LCons (Drop t) lxs \<Longrightarrow>
   timely_trace sid summa R (Suc n) buf caps inps outs" *)

(*
| tt_Drop[intro!]: "timely_trace f n buf (remove1 t caps) lxs outs \<Longrightarrow> timely_trace f (Suc n) buf caps (LCons (Drop t) lxs) outs"
| tt_Out[intro!]: "timely_trace f n (unread_buf @ read_buf') caps inps next_outs \<Longrightarrow>
  below_caps = filter (\<lambda> t. \<not> frontier_less_equal (frontier (to_zmset caps)) (t :: 't :: order)) (rmdups {} (map snd read_buf)) \<Longrightarrow>
  buf = unread_buf @ read_buf \<Longrightarrow>
  compl_batches = (\<lambda> t. map fst (filter (\<lambda> (d, t'). t' = t \<and> t \<in> set compl_caps) read_buf)) \<Longrightarrow>
  read_buf' = filter (\<lambda> (d, t). t \<notin> set below_caps) read_buf \<Longrightarrow>
  new_outs = concat (map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (filter (\<lambda> t. t \<in> set below_caps) (rmdups {} (map snd read_buf)))) \<Longrightarrow>
  new_outs \<noteq> [] \<Longrightarrow>
  outs = new_outs @@- next_outs \<Longrightarrow>
  timely_trace f 0 buf caps inps outs"
| tt_LNil[intro!]: "timely_trace f m [] [] LNil LNil" *)

end

lemma timely_trace_test_1:
  "timely_trace (\<lambda> b. [Max (set b)]) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))) [] [t0] inps2 (LCons (10, MyPair 1 1) (LCons (7, MyPair 0 1) (LCons (3, MyPair 1 0) LNil)))"
  apply (simp only: llist_of.simps)
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
    apply (rule tt_Out[where n=0 and unread_buf=Nil and compl_caps="[t_1_1, t_0_1, t_1_0]" and next_outs=LNil, rotated])
         apply (rule refl)+
        apply simp
         apply (rule refl)+
    apply code_simp+
  apply (rule tt_LNil)
  done

lemma timely_trace_test_2:
  "timely_trace (\<lambda> b. [Max (set b)]) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) [] [t0] inps2 (LCons (3, MyPair 1 0) (LCons (10, MyPair 1 1) (LCons (7, MyPair 0 1) LNil)))"
  apply (simp only: llist_of.simps)
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply (rule tt_Out[where n="Suc 0" and unread_buf=Nil  and compl_caps="[t_1_1, t_1_0]" and new_outs="[(3, MyPair 1 0)]", rotated])
         apply (rule refl)+
        apply simp
         apply (rule refl)+
     apply code_simp
    apply simp
   defer
   apply rule
   apply (rule tt_Out[where n="0" and unread_buf=Nil and compl_caps="[t_1_1, t_1_0, t_0_1]"  and next_outs=LNil, rotated])
         apply (rule refl)+
     apply code_simp
    apply (rule refl)+
   apply code_simp
   apply rule
  apply code_simp
  done

term "[Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"

lemma timely_trace_test_3:
  "timely_trace (\<lambda> b. [Max (set b)]) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))) [] [t0] inps2 (LCons (7, MyPair 0 1) (LCons (10, MyPair 1 1) (LCons (3, MyPair 1 0) LNil)))"
  apply (simp only: llist_of.simps)
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  oops

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


definition "my_test = lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op2)"

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



value [GHC] "approx_in 30 [VOut (1, 1) (Inr 3, MyPair 1 0)] test_op2"


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
