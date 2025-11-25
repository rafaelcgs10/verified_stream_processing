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
  | LCons (Data t (d :: 'd1)) lxs' \<Rightarrow> batch_fun_spec f lxs' ((d, t) # buf) caps
  | LCons (Mint t) lxs' \<Rightarrow> batch_fun_spec f lxs' buf (caps @ [t])
  | LCons (Drop t) lxs' \<Rightarrow> (
    let below_caps = filter (\<lambda> t'. \<not> frontier_less_equal (frontier (zmset_of (mset caps - {# t #}))) t') (rmdups {} (map snd buf)) in
    let compl_batches = (\<lambda> t. map fst (filter (\<lambda> (d, t'). t' = t \<and> t' \<in> set below_caps) buf)) in
    let outs = concat (map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (filter (\<lambda> t. t \<in> set below_caps) (rmdups {} (map snd buf)))) in
    let buf' = filter (\<lambda> (d, t). t \<notin> set below_caps) buf in
    LCons outs (batch_fun_spec f lxs' buf' (remove1 t caps))))"

fun foo where
 "foo f lxs buf caps = (case lxs of
    [] \<Rightarrow> ([], buf, caps)
  | (Data t (d :: 'd1)) # lxs' \<Rightarrow> foo f lxs' ((d, t) # buf) caps
  | (Mint t) # lxs' \<Rightarrow> foo f lxs' buf (caps @ [t])
  | (Drop t) # lxs' \<Rightarrow> (
    let below_caps = filter (\<lambda> t'. \<not> frontier_less_equal (frontier (zmset_of (mset caps - {# t #}))) t') (rmdups {} (map snd buf)) in
    let compl_batches = (\<lambda> t. map fst (filter (\<lambda> (d, t'). t' = t \<and> t' \<in> set below_caps) buf)) in
    let outs = concat (map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (filter (\<lambda> t. t \<in> set below_caps) (rmdups {} (map snd buf)))) in
    let buf' = filter (\<lambda> (d, t). t \<notin> set below_caps) buf in
    let (outs', buf'', caps'') = foo f lxs' buf' (remove1 t caps) in
    (outs @ outs', buf'', caps'')))"

term batch_fun_spec

declare batch_fun_spec.simps[code]

(* filter cUNIV to not have empty outputs*)
corec spec_op where
  "spec_op (f :: 'a list \<Rightarrow> 'b list) lxs buf caps outp = choice2
   (Choice ((cimage (\<lambda> n. 
     let (outs, buf', caps') = foo f (ltaken n lxs) buf caps in
     (case outp @ outs of x # xs \<Rightarrow> (Write (spec_op f (ldropn n lxs) buf' caps' xs) 1 x))) (
      cfilter (\<lambda> n. fst (foo f (ltaken n lxs) buf caps) \<noteq> [])
      (cUNIV :: nat cset)))))
    (case outp of 
       [] \<Rightarrow> \<oslash>
     | x # xs \<Rightarrow> Write (spec_op f lxs buf caps xs) 1 x)"

corec nd_source_op where
  "nd_source_op inps = choice2
   (source_op inps)
   (Choice (cimage undefined (cUNIV :: nat cset)))"

definition "t0 \<equiv> \<bottom>"
definition "t_1_0 \<equiv> MyPair (Suc 0) (0 :: nat)"
definition "t_0_1 \<equiv> MyPair (0 :: nat) (Suc 0)"
definition "t_1_1 \<equiv> MyPair (Suc 0) (Suc 0)"

abbreviation "inps1 \<equiv> llist_of [Mint 1, Data 1 44, Data 1 6, Data (0 :: nat) (0 :: nat), Data 0 42, Drop 0, Data 1 43]"

abbreviation "inps2 \<equiv> 
 llist_of [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1, Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"

abbreviation \<open>r1 \<equiv> lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) inps1 [] [\<bottom>])\<close>

value r1

abbreviation \<open>r2 \<equiv> lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) inps2 [] [\<bottom>])\<close>

value r2

abbreviation "spec_op_test \<equiv> (spec_op (\<lambda> b. [Max (set b)]) inps2 [] [\<bottom>] []) :: (1, 1, nat \<times> (nat, nat) myprod) op"

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
(* 
abbreviation "test_dt1 \<equiv> Comp [(0, 1) \<mapsto> (0, 1)] (l1 (\<lambda> _. inps1)) l2"
 *)
abbreviation "test_dt2 \<equiv> Comp [(0, 1) \<mapsto> (0, 1)] (l1 (\<lambda> _. inps2)) l2"

(* abbreviation "test_op1 \<equiv> compile_dataflow test_dt1 :: (2 \<times> 1, 2 \<times> 1, (nat + nat) \<times> nat) op"
 *)

abbreviation "test_op2 \<equiv> compile_dataflow test_dt2 :: (2 \<times> 1, 2 \<times> 1, _) op"


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

definition "crmdups (f :: 'a \<Rightarrow> 'b) (C :: 'a cset) = C"
declare crmdups_def[code del]

lemma crmdups_code[code]:
  "crmdups f (cset_of_llist xs) = cset_of_llist (lrmdups f xs)"
  sorry

definition "compress_cfilter P xs = cfilter P xs"

friend_of_corec lappend where
  "lappend xs lys = (case xs of LNil \<Rightarrow> (case lys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs)
    | LCons x xs \<Rightarrow> LCons x (lappend xs lys))"
  subgoal by (cases xs; cases lys; simp)
  subgoal by transfer_prover
  done

declare csome_elem_def[code del]
declare cthe_elem_def[code del]


definition "csingleton (xs :: 'm cset) = xs"
declare csingleton_def[code del]

definition "cnub (C :: (_ :: equal) cset) = C"
declare cnub_def[code del]

definition "ctake (n :: nat) (C :: (_ :: equal) cset) = C"
declare ctake_def[code del]


code_printing code_module "Cset" \<rightharpoonup> (Haskell)
\<open>
module Cset (csingleton, chd, Cset (..), Nat (..), cnub, clast, ctake, safe_nth, ndrop, ntake) where
import qualified Data.List;

newtype Cset a = Cset [a];
newtype Nat = Nat Integer;

csingleton (Cset []) = Cset [];
csingleton (Cset xs) = Cset [Prelude.head xs];

chd (Cset xs) = Prelude.head xs;
clast (Cset xs) = Prelude.last xs;

cnub (Cset xs) = Cset (Data.List.nub xs);

safe_nth xs n = xs !! ((mod (Prelude.fromInteger n) (length  xs)));

ctake (Nat n) (Cset xs) = Cset (Prelude.take (Prelude.fromInteger n) xs);

ndrop (Nat n) xs = drop (Prelude.fromInteger n) xs;
ntake (Nat n) xs = take (Prelude.fromInteger n) xs;

\<close> 

declare ltaken.simps[code del]

code_printing
  type_constructor cset \<rightharpoonup>
    (Haskell) "Cset.Cset _"
  | type_constructor nat \<rightharpoonup>
    (Haskell) "Cset.Nat"
  | constant Nat \<rightharpoonup>
    (Haskell) "Cset.Nat"
  | constant cset_of_llist \<rightharpoonup>
    (Haskell) "Cset.Cset"
  | constant csingleton \<rightharpoonup>
    (Haskell) "Cset.csingleton"
  | constant cthe_elem \<rightharpoonup>
    (Haskell) "Cset.chd"
  | constant csome_elem \<rightharpoonup>
    (Haskell) "Cset.clast"
  | constant cnub \<rightharpoonup>
    (Haskell) "Cset.cnub"
  | constant ctake \<rightharpoonup>
    (Haskell) "Cset.ctake"
  | type_constructor llist \<rightharpoonup>
    (Haskell) "![(_)]"
  | constant LNil \<rightharpoonup>
    (Haskell) "[]"
  | constant LCons \<rightharpoonup>
    (Haskell) infix 3 ":"
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
  | constant lmerge \<rightharpoonup>
    (Haskell) "Prelude.concat"
  | constant lhd \<rightharpoonup>
    (Haskell) "Prelude.head"
  | constant hd \<rightharpoonup>
    (Haskell) "Prelude.head"
  | constant ltl \<rightharpoonup>
    (Haskell) "Prelude.tail"
  | constant tl \<rightharpoonup>
    (Haskell) "Prelude.tail"
  | constant last \<rightharpoonup>
    (Haskell) "Prelude.last"
  | constant lzip \<rightharpoonup>
    (Haskell) "zip"
  | constant llist.lnull \<rightharpoonup>
    (Haskell) "null"
  | constant ltakeWhile \<rightharpoonup>
    (Haskell) "takeWhile"
  | constant ldropWhile \<rightharpoonup>
    (Haskell) "dropWhile"
  | constant ldropn \<rightharpoonup>
    (Haskell) "Cset.ndrop"
  | constant ldrop \<rightharpoonup>
    (Haskell) "Cset.ndrop"
  | constant ltaken \<rightharpoonup>
    (Haskell) "Cset.ntake"
  | constant llist_all \<rightharpoonup>
    (Haskell) "all"
  | constant llist_of \<rightharpoonup>
    (Haskell) "id"

fun wsteps_at :: "('i, 'o, 'd :: countable) op \<Rightarrow> _" where
  "wsteps_at (Write op p x) n = {|(VOut p x, op)|}"
| "wsteps_at (Read p f) n = cimage (\<lambda>x. (VInp p x, f x)) (cUNIV :: 'd cset)"
| "wsteps_at (Silent op) (Suc n) = wsteps_at op n"
| "wsteps_at (Choice ops) (Suc n) = cUnion (cimage (\<lambda> op. wsteps_at op n) ops)"
| "wsteps_at op 0 = {||}"

definition "wsteps_exec op = cUnion (cimage (wsteps_at op) cUNIV)"

lemma wsteps_exec_Write[simp]: "wsteps_exec (Write op p x) = {|(VOut p x, op)|}"
  unfolding wsteps_exec_def by (auto simp: cset_eq_iff)

lemma wsteps_exec_Read[simp]: "wsteps_exec (Read p f) = cimage (\<lambda>x. (VInp p x, f x)) (cUNIV :: _ cset)"
  unfolding wsteps_exec_def by (auto simp: cset_eq_iff)

lemma wsteps_exec_Silent[simp]:
  "wsteps_exec (Silent op) = wsteps_exec op"
  unfolding wsteps_exec_def
  apply safe
  subgoal premises prems for a b n
    using prems(2-) apply -
    apply (induct "Silent op" n arbitrary: op rule: wsteps_at.induct)
     apply auto
    done
  subgoal for a b n
    apply (simp add: wsteps_exec_def)
    apply (rule exI[of _ "Suc n"])
    apply auto
    done
  done

lemma wsteps_exec_Choice[simp]:
  "wsteps_exec (Choice ops) = cUnion (wsteps_exec |`| ops)"
  unfolding wsteps_exec_def
  apply safe
  subgoal premises prems for a b n
    using prems(2-) apply -
    apply (induct "Choice ops" n arbitrary: ops rule: wsteps_at.induct)
     apply auto
    done
  subgoal for a b x n
    apply (simp add: wsteps_exec_def)
    apply (rule exI[of _ "Suc n"])
    apply auto
    done
  done

declare wsteps_exec_def[code del]
lemmas wsteps_exec_code[code] = wsteps_exec_Read wsteps_exec_Write wsteps_exec_Silent wsteps_exec_Choice


corec trace_exec where
  "trace_exec op = (let ops = wsteps_exec op in                      
   if \<not> cis_empty ops then let (io, op') = cthe_elem ops in LCons io (trace_exec op')
   else LNil)"


term Set.the_elem
(* 
value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op1)"
 *)
value r1

value [GHC] "crmdups id {|Suc 0, Suc 0|}"


instantiation myprod :: (cenum, cenum) cenum begin
definition cenum_myprod :: "('a, 'b) myprod llist" where "cenum_myprod = lmerge (lmap (\<lambda> x. lmap (MyPair x) cenum) cenum)"
instance
  apply standard
  unfolding cenum_myprod_def from_prod_def lset_lmap
  apply (auto simp: cenum_prod_def image_iff inj_on_def order_less_subst2 UNIV_cenum[symmetric] cenum_distinct
      intro!: ldistinct_linterleave ldistinct_lmerge
      dest!: cenum_distinct[unfolded ldistinct_conv_lnth, rule_format, THEN notE, rotated -1] split: myprod.splits)
  subgoal for x
    apply (cases x)
    apply auto
    done
  done
end

definition "my_test = lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op2)"

value [GHC] my_test



value [GHC] "ltaken 2 (trace_exec spec_op_test)"

value "frontier {# t_1_1, t_0_1, t_1_0 #}\<^sub>z"

term DEBUG


value "\<not> frontier_less_equal (frontier {# t_1_0, t_1_1, t_0_1 #}\<^sub>z) t_1_0"


fun check_prefix where
  "check_prefix [] op = True"
| "check_prefix (io # ios) op = 
  (let ios_ops = cfilter (\<lambda> (io', op). io = io') (wsteps_exec op) in
   if ios_ops = {||} then False
   else
   True |\<in>| (cimage (check_prefix ios) (cimage snd ios_ops)))"


term 
"llist_of [Mint t_1_0, Mint t_0_1, Mint t_1_1, Drop t0, Data t_1_1 10, Drop t_1_1,
 Data t_0_1 7, Data t_1_0 (3 :: nat), Drop t_1_0, Drop t_0_1]"


value [GHC] "check_prefix [VOut (1, 1) (Inr 10, MyPair 1 1)] test_op2"

value [GHC] "check_prefix [VOut (1, 1) (Inr 7, MyPair 0 1)] test_op2"



value [GHC] "check_prefix [VOut 1 (7, MyPair 0 1)] spec_op_test"


value [GHC] "check_prefix [VOut 1 (3, MyPair 1 0)] spec_op_test"

value [GHC] "check_prefix [VOut 1 (10, MyPair 1 )] spec_op_test"


(* 
 value [GHC] "check_prefix [VOut (1, 1) (Inr 3, MyPair 1 0)] test_op2"
 
 *)
(* 
value [GHC] "approx_in 27 [VOut (1, 1) (Inr 3, MyPair 1 0)] test_op2"
 *)

thm cUnion_code

term cUn
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
  \<open>dataflow_op sg (inp_bt_op os1 (\<lambda> p. case p of Inl x \<Rightarrow> [] | Inr x \<Rightarrow> map (\<lambda> (d, t). Inr (Inl d, t)) cbuf) os2 f) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. outpu os2 1 @@- lmap (\<lambda> (d, t). (Inr d, t)) (lconcat (batch_fun_spec f lxs buf caps))))\<close>

  term "ocaps os1 1"

end
