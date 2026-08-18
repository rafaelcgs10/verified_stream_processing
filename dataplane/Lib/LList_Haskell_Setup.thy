theory LList_Haskell_Setup

imports
  Coinductive.Coinductive_List
  CsetUtils
  "HOL-Library.Code_Target_Numeral"
begin


lemma one_minus[code]:
  "(1 :: 1) - x = 1"
  by auto
lemma one_plus[code]:
  "(1 :: 1) + x = 1"
  by auto



lemma cminus_code[code]:
  "(cset_of_llist xs) - (cset_of_llist ys) = cset_of_llist (lfilter (\<lambda> x. x \<notin> lset ys) xs)"
  by (auto simp add: cset_of_llist.rep_eq)



friend_of_corec lappend where
  "lappend xs lys = (case xs of LNil \<Rightarrow> (case lys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs)
    | LCons x xs \<Rightarrow> LCons x (lappend xs lys))"
  subgoal by (cases xs; cases lys; simp)
  subgoal by transfer_prover
  done

declare csome_elem_def[code del]
declare cthe_elem_def[code del]

definition "cnub (C :: (_ :: equal) cset) = C"
declare cnub_def[code del]

definition "ctake (n :: nat) (C :: (_ :: equal) cset) = C"
declare ctake_def[code del]

declare ccard_def[code del]

code_printing code_module "Cset" \<rightharpoonup> (Haskell)
\<open>
module Cset (chd, Cset (..), Nat (..), cnub, clast, ctake, safe_nth, ndrop, lmerge) where
import qualified Data.List;

newtype Cset a = Cset [a];
newtype Nat = Nat Integer;

chd (Cset xs) = Prelude.head xs;
clast (Cset xs) = Prelude.last xs;

cnub (Cset xs) = Cset (Data.List.nub xs);

safe_nth xs n = xs !! ((mod (Prelude.fromInteger n) (length  xs)));

ctake (Nat n) (Cset xs) = Cset (Prelude.take (Prelude.fromInteger n) xs);

ndrop (Nat n) xs = drop (Prelude.fromInteger n) xs;

lmerge = (concat . Data.List.transpose);
\<close> 

code_printing
  type_constructor cset \<rightharpoonup>
    (Haskell) "Cset.Cset _"
  | type_constructor nat \<rightharpoonup>
    (Haskell) "Cset.Nat"
  | constant Code_Target_Nat.Nat \<rightharpoonup>
    (Haskell) "Cset.Nat"
  | constant cset_of_llist \<rightharpoonup>
    (Haskell) "Cset.Cset"
  | constant cthe_elem \<rightharpoonup>
    (Haskell) "Cset.chd"
  | constant csome_elem \<rightharpoonup>
    (Haskell) "Cset.chd"
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
  | constant llist_all \<rightharpoonup>
    (Haskell) "all"
  | constant llist_of \<rightharpoonup>
    (Haskell) "id"
(*   | constant linterleave \<rightharpoonup>
    (Haskell) infixr 5 "++"
   | constant lmerge \<rightharpoonup>
    (Haskell) "Prelude.concat"  
 *)
fun wsteps_at where
  "wsteps_at (Write op p x) n = {|(VOut p x, op)|}"
| "wsteps_at (Read p f) n = {|(VInp p (Code.abort (STR ''wsteps_at should not read'') (\<lambda> _. undefined)), f undefined)|}"
| "wsteps_at (Silent op) (Suc n) = wsteps_at op n"
| "wsteps_at (Choice ops) (Suc n) = cUnion (cimage (\<lambda> op. wsteps_at op n) ops)"
| "wsteps_at op 0 = {||}"

definition "wsteps_exec op = cUnion (cimage (wsteps_at op) cUNIV)"

lemma wsteps_exec_Write[simp]: "wsteps_exec (Write op p x) = {|(VOut p x, op)|}"
  unfolding wsteps_exec_def by (auto simp: cset_eq_iff)

lemma wsteps_exec_Read[simp]: "wsteps_exec (Read p f) = {|(VInp p (Code.abort (STR ''wsteps_at should not read'') (\<lambda> _. undefined)), f undefined)|}"
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

lemma acset_code[code]:
  "acset S = cset_of_llist (lfilter (\<lambda> x. x \<in> S) cenum)"
  unfolding cset_of_llist_def map_fun_def o_apply id_apply using UNIV_cenum by auto

definition "flat_choices ops = cUnion (cimage choices ops)"

fun find_output_at where
  "find_output_at (Write op p x) (p', x') n = (if p' = p \<and> x' = x then Some op else None)"
| "find_output_at (Read p f) x n = Code.abort (STR ''steps_of should not read'') undefined"
| "find_output_at (Silent op) x (Suc n) = find_output_at op x n"
| "find_output_at (Choice ops) x (Suc n) = (
   let ops' = cfilter (\<lambda>r. r \<noteq> None) (cimage (\<lambda> op. find_output_at op x n) (ops)) in
   (if ops' = {||} then None else cthe_elem ops'))"
| "find_output_at op x _ = Code.abort (STR ''steps_of out of gas'') undefined"


fun check_prefix where
  "check_prefix n [] op = True"
| "check_prefix n (io # ios) op = 
  (case find_output_at op io n of
     None \<Rightarrow> False
   | Some op \<Rightarrow> check_prefix n ios op)"

subsection \<open>Executable Unit Tests\<close>

text \<open>A unit test asserts that a computed value equals an expected one. On
  success the computed value is returned, so that a @{command value} command
  using it still displays that value. On failure the generated code aborts,
  which turns a wrong result into a failing @{command value} command instead of
  a silently wrong output. The comparison is plain equality, so the expected
  value fixes exactly as much as the test intends: comparing traces as lazy
  lists fixes the order of the outputs, while comparing @{const lset} of a
  trace with a set of expected outputs leaves the order open, which is what
  programs with several possible schedules require.\<close>

definition "unit_test v r = (if v = r then v else Code.abort (STR ''Failed unit test'') (\<lambda> _. v))"

lemma choice2_simp[simp]:
  "choice2 op1 op2 = Choice {| op1, op2 |}"
  by simp

lemma choice3_simp[simp]:
  "choice3 op1 op2 op3 = Choice {| op1, op2, op3 |}"
  by simp

end