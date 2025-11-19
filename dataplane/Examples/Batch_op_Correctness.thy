theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Source_op
  Ooo_Input_op
  Batch_op
  "../MyProduct_Instances"
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

abbreviation "inps1 \<equiv> llist_of [Data 1 4, Data (0 :: nat) (10 :: nat), Data 0 0, Data 2 11]"

abbreviation "inps2 \<equiv> llist_of [Mint t1, Mint t2, Mint t3, Data t3 10, Drop t3, Data t2 7, Data t1 (-2 :: int), Data t2 (-1), Data t1 (- 3), Drop t1, Drop t2]"

value \<open>list_of (lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) inps1 [] []))\<close>
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
   ocaps = (\<lambda> _. [0]),
   initia = False,
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
   ocaps = (\<lambda> _. [0]),
   initia = False,
   en1 = Inl,
   de1 = projl,
   en2 = Inr,
   de2 = projr
   \<rparr>"
abbreviation "l2 \<equiv> Logic (batch_fun_op (init_operator_state_ty2 default_internal_summary) (\<lambda> b. if b = [] then [] else [Max (set b)])) default_internal_summary"

abbreviation "dt \<equiv> compile_dataflow (Comp [(0, 1) \<mapsto> (0, 1)] (l1 (\<lambda> _. inps1)) l2) :: (1 \<times> 1, 1 \<times> 1, (nat + nat) \<times> nat) op"

lemma one_minus[code]:
  "(1 :: 1) - x = 1"
  by auto
lemma one_plus[code]:
  "(1 :: 1) + x = 1"
  by auto

find_theorems eval'

find_theorems cset_of_llist cUnion

partial_function (llist) lrmdups_aux where
  "lrmdups_aux f S lxs = (case lxs of LNil \<Rightarrow> LNil | LCons x lxs \<Rightarrow> (if f x \<in> S then lrmdups_aux f S lxs else LCons x (lrmdups_aux f (insert (f x) S) lxs)))"
declare lrmdups_aux.simps[code]

definition "lrmdups f = lrmdups_aux f {}"

definition "compress_cfilter P xs = cfilter P xs"

lemma compress_cfilter_code[code]: "compress_cfilter P (cset_of_llist xs) = cfilter P (cset_of_llist (lrmdups id xs))"
  sorry

friend_of_corec lappend where
  "lappend xs lys = (case xs of LNil \<Rightarrow> (case lys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs)
    | LCons x xs \<Rightarrow> LCons x (lappend xs lys))"
  subgoal by (cases xs; cases lys; simp)
  subgoal by transfer_prover
  done


definition "my_eval = compress_cfilter ((\<noteq>) [])(eval 18 dt)"
value [GHC] "my_eval" 
 
definition "my_check = approx_in 20 [VOut (1, 1) (Inr 4, 1), VOut (1, 1) (Inr 10, 0)] dt"
(* 
definition "my_check = approx_in 24 [VOut (1, 1) (Inr 0, 0)] dt" *)
(* 
value [GHC] "my_check"
 *)

definition "rmdup_traces xs = xs"

abbreviation "flat_choices ops \<equiv> cUnion (cimage choices ops)"

find_consts "_ cset"

context includes cset.lifting begin
lift_definition ccard :: "'m cset \<Rightarrow> nat" is card .
end

term the_enat

lemma ccard_code[code]:
  "ccard (cset_of_llist xs) = the_enat (llength xs)"
  sorry
abbreviation "is_Visible x \<equiv> is_Write x \<or> is_Read x"

abbreviation "optm ops \<equiv> let ops' = (cfilter (is_Visible o snd) ops) in if ccard ops' > 0 then ops' else ops"

fun fast_eval' :: "nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('i, 'o, 'd :: {countable}) op \<Rightarrow> (('i, 'o, 'd) VIO list \<times> ('i, 'o, 'd) op) cset"  where
  "fast_eval' 0 m i op = {|([], op)|}"
| "fast_eval' n m 0 op = {||}"
| "fast_eval' (Suc n) m i (Write op p x) = cimage (\<lambda>(t, op). (VOut p x # t, op)) (fast_eval' n m m op)"
| "fast_eval' (Suc n) m i (Read p f) = cUnion (cimage (\<lambda>x. cimage (\<lambda>(t, op). (VInp p x # t, op)) (fast_eval' n m m (f x))) (cUNIV :: 'd cset))"
| "fast_eval' n m (Suc i) (Silent op) = (cimage (\<lambda>(t, op). (t, op)) (fast_eval' n m i op))"
| "fast_eval' n m (Suc i) (Choice ops) = (if ops = {||} then {|([], \<oslash>)|} else (let ops' = cUnion (cimage (fast_eval' n m i) ops) in optm ops'))"

definition "fast_eval n m op = cimage fst (fast_eval' n m m op)"


definition "my_fast_eval = compress_cfilter ((\<noteq>) []) (fast_eval 1 14 dt)"
value [GHC] "my_fast_eval" 

definition "fast_approx_in n m pfx op = 
  (\<not> cis_empty (cfilter (\<lambda>xs. Sublist.prefix pfx xs) (cimage fst (fast_eval' n m m op))))"

definition "my_fast_check = fast_approx_in 3 14 [VOut (1, 1) (Inr 4, 1), VOut (1, 1) (Inr 10, 0), VOut (1, 1) (Inr 11, 2)] dt"

value [GHC] "my_fast_check" 


(* export_code my_test in Haskell 
  module_name Test
 *)

abbreviation "inp_op os \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op {|1|} os)"
abbreviation "bt_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_fun_op os f)"

abbreviation "inp_bt_op os1 cbuf os2 f \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] cbuf (inp_op (os1\<lparr> en1 := Inl \<rparr>)) (bt_op (os2\<lparr> de1 := projl, en2 := Inr \<rparr>) f))"

lemma dataflow_op_inp_bt_op_wbisim_source_op_aux:
  fixes lxs :: \<open>('t :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}, 'd1) event llist\<close>
  and f :: \<open>'d1 buf \<Rightarrow> 'd2 buf\<close>
  and os1 :: \<open>(1, 'd1 + 'd2, 'd1, 't) input_state\<close>
  and os2 :: \<open>(1, 'd1 + 'd2, 'd1, 'd2, 't) operator_state_ty2\<close>
assumes
  state_inv: 
   \<open>es os1 1 = lxs\<close>
   \<open>outpu os1 1 = map (\<lambda> (d, t). (Inl d, t)) outpos1\<close>
   \<open>input os2 1 = map (\<lambda> (d, t). (Inl d, t)) inpos2\<close>
   \<open>buf = outpos1 @ cbuf @ inpos\<close>
shows 
  \<open>dataflow_op sg (inp_bt_op os1 (\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (Inl d, t)) cbuf) os2 f) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. outpu os2 1 @@- lmap (\<lambda> (d, t). (Inr d, t)) (lconcat (batch_fun_spec f lxs' buf caps))))\<close>


  term outpos1
  term buf
  oops


end
