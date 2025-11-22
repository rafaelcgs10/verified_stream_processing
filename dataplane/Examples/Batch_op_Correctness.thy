theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Source_op
  Ooo_Input_op
  Batch_op
  "../MyProduct_Instances"
  "../AntichainOrder"
begin


partial_function (llist) batch_fun_spec where
 "batch_fun_spec f lxs buf caps = (case lxs of
    LNil \<Rightarrow> (
    let compl_batches = (\<lambda> t. map fst ((filter (\<lambda> (d, t'). t' = t)) buf)) in
    let outs =  map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (rmdups {} (map snd buf)) in
    llist_of outs)
  | LCons (Data t (d :: 'd1)) lxs' \<Rightarrow> batch_fun_spec f lxs' (buf @ [(d, t)]) caps
  | LCons (Mint t) lxs' \<Rightarrow> batch_fun_spec f lxs' buf (caps @ [t])
  | LCons (Drop t) lxs' \<Rightarrow> (
    let below_caps = filter (\<lambda> t. \<not> frontier_less_equal (frontier (zmset_of (mset caps - {# t #}))) t) caps in
    let compl_batches = (\<lambda> t. map fst (filter (\<lambda> (d, t'). t' = t \<and> t' \<in> set below_caps) buf)) in
    let outs = concat (map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (filter (\<lambda> t. t \<in> set below_caps) (rmdups {} (map snd buf)))) in
    let buf' = filter (\<lambda> (d, t). t \<notin> set below_caps) buf in
    LCons outs (batch_fun_spec f lxs' buf' (remove_last t caps))))"

declare batch_fun_spec.simps[code]

abbreviation "t1 \<equiv> MyPair (Suc 0) (0 :: nat)"
abbreviation "t2 \<equiv> MyPair (0 :: nat) (Suc 0)"
abbreviation "t3 \<equiv> MyPair (Suc 0) (Suc 0)"

term DEBUG

abbreviation "inps1 \<equiv> llist_of [Data (0 :: nat) (0 :: nat), Data 0 42, Mint 1, Drop 0, Data 1 43]"

abbreviation "inps2 \<equiv> llist_of [Mint t1, Mint t2, Mint t3, Data t3 10, Drop t3, Data t2 7, Data t1 (-2 :: int), Data t2 (-1), Data t1 (- 3), Drop t1, Drop t2]"

value \<open>list_of (lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) inps1 [] []))\<close>

value \<open>list_of (lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) inps2 [] []))\<close>

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
abbreviation "l2 \<equiv> Logic (batch_fun_op (init_operator_state_ty2 default_internal_summary) (\<lambda> b. if b = [] then [] else [Max (set b)])) default_internal_summary"

abbreviation "main_dt \<equiv> Comp [(0, 1) \<mapsto> (0, 1)] (l1 (\<lambda> _. inps1)) l2"

abbreviation "dt \<equiv> compile_dataflow main_dt :: (2 \<times> 1, 2 \<times> 1, (nat + nat) \<times> nat) op"

lemma one_minus[code]:
  "(1 :: 1) - x = 1"
  by auto
lemma one_plus[code]:
  "(1 :: 1) + x = 1"
  by auto

partial_function (llist) lrmdups_aux where
  "lrmdups_aux f S lxs = (case lxs of LNil \<Rightarrow> LNil | LCons x lxs \<Rightarrow> (if f x \<in> S then lrmdups_aux f S lxs else LCons x (lrmdups_aux f (insert (f x) S) lxs)))"
declare lrmdups_aux.simps[code]

definition "lrmdups f = lrmdups_aux f {}"

definition "compress_cfilter P xs = cfilter P xs"

friend_of_corec lappend where
  "lappend xs lys = (case xs of LNil \<Rightarrow> (case lys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs)
    | LCons x xs \<Rightarrow> LCons x (lappend xs lys))"
  subgoal by (cases xs; cases lys; simp)
  subgoal by transfer_prover
  done


(* definition "my_eval = compress_cfilter ((\<noteq>) [])(eval 18 dt)"
value [GHC] "my_eval"  *)
 
definition "my_check = approx_in 20 [VOut (1, 1) (Inr 4, 1), VOut (1, 1) (Inr 10, 0)] dt"
(* 
definition "my_check = approx_in 24 [VOut (1, 1) (Inr 0, 0)] dt" *)
(* 
value [GHC] "my_check"
 *)

definition "rmdup_traces xs = xs"

abbreviation "flat_choices ops \<equiv> cUnion (cimage choices ops)"

abbreviation "is_Visible x \<equiv> is_Write x \<or> is_Read x"

context includes cset.lifting begin
lift_definition ccard :: "'m cset \<Rightarrow> nat" is card .
end

lemma ccard_code[code]:
  "ccard (cset_of_llist xs) = the_enat (llength xs)"
  sorry

abbreviation "optm ops \<equiv> let ops' = (cfilter (is_Visible o snd) ops) in if ccard ops' > 0 then ops' else ops"

code_printing
  type_constructor llist \<rightharpoonup>
    (Haskell) "![(_)]"
  | constant LNil \<rightharpoonup>
    (Haskell) "[]"
  | constant LCons \<rightharpoonup>
    (Haskell) infix 5 ":"
  | class_instance llist :: equal \<rightharpoonup>
    (Haskell) -
  | constant "HOL.equal :: 'a llist \<Rightarrow> 'a llist \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) infix 4 "=="
  | constant "lappend" \<rightharpoonup>
    (Haskell) infixr 5 "++"
  | constant lmap \<rightharpoonup>
    (Haskell) "map"
  | constant lfilter \<rightharpoonup>
    (Haskell) "filter"
  | constant lconcat \<rightharpoonup>
    (Haskell) "Prelude.concat"
  | constant lhd \<rightharpoonup>
    (Haskell) "Prelude.head"
  | constant hd \<rightharpoonup>
    (Haskell) "Prelude.head"
  | constant ltl \<rightharpoonup>
    (Haskell) "Prelude.tail"
  | constant tl \<rightharpoonup>
    (Haskell) "Prelude.tail"
  | constant lzip \<rightharpoonup>
    (Haskell) "zip"
  | constant llist.lnull \<rightharpoonup>
    (Haskell) "null"
  | constant ltakeWhile \<rightharpoonup>
    (Haskell) "takeWhile"
  | constant ldropWhile \<rightharpoonup>
    (Haskell) "dropWhile"
  | constant llist_all \<rightharpoonup>
    (Haskell) "all"
  | constant llist_of \<rightharpoonup>
    (Haskell) "id"

definition "csetid (xs :: 'm cset) = xs"

code_printing code_module "Cset" \<rightharpoonup> (Haskell)
  \<open>module Cset (foo, Cset (..) ) where
newtype Cset a = Cset [a];

foo (Cset []) = Cset [];
foo (Cset xs) = Cset [Prelude.head xs];

\<close> 

code_printing
  type_constructor cset \<rightharpoonup>
    (Haskell) "Cset.Cset _"
  | constant cset_of_llist \<rightharpoonup>
    (Haskell) "Cset.Cset"
  | constant csetid \<rightharpoonup>
    (Haskell) "Cset.foo"

term choice5
lemma choice5_code[code]:
  "choice5 op1 op2 op3 op4 op5 = Choice {||}"
  sorry

fun fast_eval' :: "nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('i, 'o, 'd :: {countable}) op \<Rightarrow> (('i, 'o, 'd) VIO list \<times> ('i, 'o, 'd) op) cset"  where
  "fast_eval' 0 m i op = {|([], op)|}"
| "fast_eval' n m 0 op = {||}"
| "fast_eval' (Suc n) m i (Write op p x) = (cimage (\<lambda>(t, op). (VOut p x # t, op)) (fast_eval' n m m op))"
| "fast_eval' (Suc n) m i (Read p f) = (cUnion (cimage (\<lambda>x. cimage (\<lambda>(t, op). (VInp p x # t, op)) (fast_eval' n m m (f x))) (cUNIV :: 'd cset)))"
| "fast_eval' n m (Suc i) (Silent op) = (cimage (\<lambda>(t, op). (t, op)) (fast_eval' n m i op))"
| "fast_eval' n m (Suc i) (Choice ops) = (
  if ops = {||} then {|([], \<oslash>)|} else
 (let ops' = (cUnion (cimage (fast_eval' n m i) ops)) in if ops' = {||} then {||} else ops'))"

definition "fast_eval n m op = (cfilter ((\<noteq>) []) (cimage fst ((fast_eval' n m m op))))"


definition "my_fast_eval = csetid (cimage (map (\<lambda> (d, t). (projr d, t)) o map vdata) (fast_eval 1 100 dt))"

term DEBUG

value [GHC] my_fast_eval


end


definition safe_cthe_elem where "safe_cthe_elem C = (if C = {||} then None else Some (cthe_elem C))"


lemma safe_cthe_elem_code[code]:
  "safe_cthe_elem (cset_of_llist xs) = Some (lhd xs)"
  sorry

(* lemma cthe_elem_code[code]:
  "cthe_elem (cset_of_llist xs) = Set.the_elem (lset xs)"
  apply transfer
  apply auto
  done *)

fun hd_in_traces where
  "hd_in_traces n (Write op p x) = (Some ((VOut p x), op))"
| "hd_in_traces n (Read p f) = (Some ((VInp p undefined), f undefined))"
| "hd_in_traces (Suc n) (Silent op) = hd_in_traces n op"
| "hd_in_traces (Suc n) (Choice ops) = 
  (let ops' = cimage the (cfilter ((\<noteq>) None) (cimage (hd_in_traces n) ops)) in
  (if ops' = {||} then None else safe_cthe_elem ops'))"
| "hd_in_traces 0 op = None"

fun in_traces where
  "in_traces 0 op i = []"
| "in_traces (Suc n) op i = (case hd_in_traces i op of None \<Rightarrow> [] | Some (io, op') \<Rightarrow> io # in_traces n op' i)"

definition "my_fast_check3 = in_traces 1 dt 10"

(* 
value [GHC] "my_fast_check3"

 *)


  export_code safe_cthe_elem in Haskell 
  module_name Test26

end


abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "bt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_fun_op os f)"

abbreviation "inp_bt_op os1 cbuf os2 f \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] cbuf (inp_op (os1\<lparr> en1 := Inl \<rparr>)) (bt_op (os2\<lparr> de1 := projl, en2 := Inr \<rparr>) f))"


definition \<open>subgraph_inv dtt cgs c = (let (su, _) = compile_dataflow_tree dtt in
 \<lparr> pt_tr = change_multiplicities su cgs c,
   edges = (\<lambda> l1. [l2 \<leftarrow> Enum.enum. \<not> is_empty_antichain (su l1 l2) \<and> is_Src (port l1) \<and> is_Trg (port l2) ]),
   summ = su \<rparr>)\<close>



term "[Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)]"

lemma dataflow_op_inp_bt_op_wbisim_source_op_aux:
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
  \<open>sg = subgraph_inv main_dt cgs c\<close>
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
  \<open>dataflow_op sg (inp_bt_op os1 (\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (Inl d, t)) cbuf) os2 f) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. outpu os2 1 @@- lmap (\<lambda> (d, t). (Inr d, t)) (lconcat (batch_fun_spec f lxs buf caps))))\<close>

  term "ocaps os1 1"

end
