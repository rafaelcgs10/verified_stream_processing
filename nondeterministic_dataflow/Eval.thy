theory Eval
imports BNA_Operators
  CSet_LList_Impl
begin

no_notation Sublist.parallel (infixl "\<parallel>" 50)

fun show_VIO where
  "show_VIO showI showO show (VOut p x) = STR ''Out '' + showO p + STR '' '' + show x"
| "show_VIO showI showO show (VInp p x) = STR ''Inp '' + showI p + STR '' '' + show x"

definition show_1 where "show_1 (x :: 1) = STR ''1''"
definition show_11 where "show_11 = show_sum show_1 show_1"
definition show_2 where "show_2 (x :: 2) = (if x = 1 then STR ''1'' else STR ''2'')"

fun eval' :: "nat \<Rightarrow> ('i, 'o, 'd :: {countable, defaults}) op \<Rightarrow> (('i, 'o, 'd) VIO list \<times> ('i, 'o, 'd) op) cset"  where
  "eval' 0 op = {|([], op)|}"
| "eval' (Suc n) (Read p f) = cUnion (cimage (\<lambda>x. cimage (\<lambda>(t, op). (VInp p x # t, op)) (eval' n (f x))) (c\<UU> :: 'd cset))"
| "eval' (Suc n) (Write op p x) = cimage (\<lambda>(t, op). (VOut p x # t, op)) (eval' n op)"
| "eval' (Suc n) (Silent op) = cimage (\<lambda>(t, op). (t, op)) (eval' n op)"
| "eval' (Suc n) (Choice ops) = (if ops = {||} then {|([], \<oslash>)|} else cUnion (cimage (eval' n) ops))"

definition "eval n op = cimage fst (eval' n op)"

definition W42 :: "(2,1,nat) op" where "W42 = Write end_op 1 42"
definition CP :: "(1,1,bool) op" where "CP = Read 1 (\<lambda>x. Write end_op 1 x)"
corec cp_op :: "(1,1,bool) op" where "cp_op = Read 1 (\<lambda>x. Write cp_op 1 x)"

value [GHC] "eval 10 W42"
value [GHC] "eval 10 CP"
value [GHC] "eval 10 cp_op"
value [GHC] "eval 1000 (CP \<bullet> CP)"
value [GHC] "eval 10 (cp_op \<bullet> cp_op)"
value [GHC] "eval 10 (cp_op \<parallel> cp_op)"

end