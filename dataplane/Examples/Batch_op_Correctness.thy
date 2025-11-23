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

abbreviation "t0 \<equiv> \<bottom>"
abbreviation "t1 \<equiv> MyPair (Suc 0) (0 :: nat)"
abbreviation "t2 \<equiv> MyPair (0 :: nat) (Suc 0)"
abbreviation "t3 \<equiv> MyPair (Suc 0) (Suc 0)"

abbreviation "inps1 \<equiv> llist_of [Mint 1, Data 1 44, Data 1 6, Data (0 :: nat) (0 :: nat), Data 0 42, Drop 0, Data 1 43]"

abbreviation "inps2 \<equiv> llist_of [Mint t1, Mint t2, Mint t3, Drop t0, Data t3 10, Drop t3, Data t2 7, Data t1 (2 :: nat), Data t2 (Suc 0), Data t1 3, Drop t1, Drop t2]"

abbreviation \<open>r1 \<equiv> lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) inps1 [] [\<bottom>])\<close>

value r1

abbreviation \<open>r2 \<equiv> lconcat (batch_fun_spec (\<lambda> b. [Max (set b)]) inps2 [] [\<bottom>])\<close>

value r2

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

abbreviation "test_dt1 \<equiv> Comp [(0, 1) \<mapsto> (0, 1)] (l1 (\<lambda> _. inps1)) l2"
abbreviation "test_dt2 \<equiv> Comp [(0, 1) \<mapsto> (0, 1)] (l1 (\<lambda> _. inps2)) l2"

abbreviation "test_op1 \<equiv> compile_dataflow test_dt1 :: (2 \<times> 1, 2 \<times> 1, (nat + nat) \<times> nat) op"
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

definition "compress_cfilter P xs = cfilter P xs"

friend_of_corec lappend where
  "lappend xs lys = (case xs of LNil \<Rightarrow> (case lys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs)
    | LCons x xs \<Rightarrow> LCons x (lappend xs lys))"
  subgoal by (cases xs; cases lys; simp)
  subgoal by transfer_prover
  done

declare csome_elem_def[code del]
declare cthe_elem_def[code del]

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

definition "csingleton (xs :: 'm cset) = xs"

code_printing code_module "Cset" \<rightharpoonup> (Haskell)
  \<open>module Cset (csingleton, chd, Cset (..) ) where
newtype Cset a = Cset [a];

csingleton (Cset []) = Cset [];
csingleton (Cset xs) = Cset [Prelude.head xs];

chd (Cset xs) = Prelude.head xs;

\<close> 

code_printing
  type_constructor cset \<rightharpoonup>
    (Haskell) "Cset.Cset _"
  | constant cset_of_llist \<rightharpoonup>
    (Haskell) "Cset.Cset"
  | constant csingleton \<rightharpoonup>
    (Haskell) "Cset.csingleton"
  | constant cthe_elem \<rightharpoonup>
    (Haskell) "Cset.chd"
  | constant csome_elem \<rightharpoonup>
    (Haskell) "Cset.chd"

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
   if \<not> cis_empty ops then let (io, op') = csome_elem ops in LCons io (trace_exec op')
   else LNil)"


value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op1)"
value r1

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

value [GHC] "lmap (\<lambda> io. case io of VOut p (x, t) \<Rightarrow> (projr x, t)) (trace_exec test_op2)"
value r2

print_classes

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
