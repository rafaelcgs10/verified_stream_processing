theory Eval
imports BNA_Operators
  CSet_LList_Impl
begin

fun eval :: "nat \<Rightarrow> ('i, 'o, 'd :: countable) op \<Rightarrow> (('i, 'o, 'd) IO list \<times> ('i, 'o, 'd) op) cset"  where
  "eval 0 op = {|([], op)|}"
| "eval (Suc n) (Read p f) = cUnion (cimage (\<lambda>x. cimage (\<lambda>(t, op). (Inp p x # t, op)) (eval n (f x))) (cUNIV :: 'd cset))"
| "eval (Suc n) (Write op p x) = cimage (\<lambda>(t, op). (Out p x # t, op)) (eval n op)"
| "eval (Suc n) (Silent op) = cimage (\<lambda>(t, op). (Tau # t, op)) (eval n op)"
| "eval (Suc n) (Choice ops) = (if ops = {||} then {|([], \<oslash>)|} else cUnion (cimage (eval n) ops))"

definition W42 :: "(2,1,nat) op" where "W42 = Write end_op 1 42"
definition CP :: "(1,1,bool) op" where "CP = Read 1 (\<lambda>x. Write end_op 1 x)"
corec cp_op :: "(1,1,bool) op" where "cp_op = Read 1 (\<lambda>x. Write cp_op 1 x)"

value "force_cset 10 (cimage fst (eval 10 W42))"
value "force_cset 10 (cimage fst (eval 10 CP))"
value "force_cset 100 (cimage fst (eval 10 cp_op))"
value "force_cset 100 (cimage fst (eval 1000 (CP \<bullet> CP)))"
value "force_cset 100 (cimage fst (eval 10 (cp_op \<bullet> cp_op)))"
value "force_cset 100 (cimage fst (eval 10 (cp_op \<parallel> cp_op)))"

end