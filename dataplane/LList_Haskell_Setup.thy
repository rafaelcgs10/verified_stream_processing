theory LList_Haskell_Setup

imports
  "Coinductive.Coinductive_List"
  Nondeterministic_Dataflow.CSet_LList_Impl
  "Timely_Infrastructure"
begin


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

lemma acset_code[code]:
  "acset S = cset_of_llist (lfilter (\<lambda> x. x \<in> S) cenum)"
  unfolding cset_of_llist_def map_fun_def o_apply id_apply using UNIV_cenum by auto


end