theory Eval
imports BNA_Operators
  CSet_LList_Impl
begin

fun show_IO where
  "show_IO showI showO show (Out p x) = STR ''Out '' + showO p + STR '' '' + show x"
| "show_IO showI showO show (Inp p x) = STR ''Inp '' + showI p + STR '' '' + show x"
| "show_IO showI showO show Tau = STR ''Tau''"

definition show_1 where "show_1 (x :: 1) = STR ''1''"
definition show_11 where "show_11 = show_sum show_1 show_1"
definition show_2 where "show_2 (x :: 2) = (if x = 1 then STR ''1'' else STR ''2'')"

fun eval :: "nat \<Rightarrow> ('i, 'o, 'd :: countable) op \<Rightarrow> (('i, 'o, 'd) IO list \<times> ('i, 'o, 'd) op) cset"  where
  "eval 0 op = {|([], op)|}"
| "eval (Suc n) (Read p f) = cUnion (cimage (\<lambda>x. cimage (\<lambda>(t, op). (Inp p x # t, op)) (eval n (f x))) (c\<UU> :: 'd cset))"
| "eval (Suc n) (Write op p x) = cimage (\<lambda>(t, op). (Out p x # t, op)) (eval n op)"
| "eval (Suc n) (Silent op) = cimage (\<lambda>(t, op). (Tau # t, op)) (eval n op)"
| "eval (Suc n) (Choice ops) = (if ops = {||} then {|([], \<oslash>)|} else cUnion (cimage (eval n) ops))"

definition W42 :: "(2,1,nat) op" where "W42 = Write end_op 1 42"
definition CP :: "(1,1,bool) op" where "CP = Read 1 (\<lambda>x. Write end_op 1 x)"
corec cp_op :: "(1,1,bool) op" where "cp_op = Read 1 (\<lambda>x. Write cp_op 1 x)"

value [GHC] "force_cset (show_list (show_IO show_2 show_1 show_nat)) 10 (cimage fst (eval 10 W42))"
value [GHC] "force_cset (show_list (show_IO show_1 show_1 show_bool)) 10 (cimage fst (eval 10 CP))"
value [GHC] "force_cset (show_list (show_IO show_1 show_1 show_bool)) 100 (cimage fst (eval 10 cp_op))"
value [GHC] "force_cset (show_list (show_IO show_1 show_1 show_bool)) 100 (cimage fst (eval 1000 (CP \<bullet> CP)))"
value [GHC] "force_cset (show_list (show_IO show_1 show_1 show_bool)) 100 (cimage fst (eval 10 (cp_op \<bullet> cp_op)))"
value [GHC] "force_cset (show_list (show_IO show_11 show_11 show_bool)) 100 (cimage fst (eval 10 (cp_op \<parallel> cp_op)))"
definition bar where "bar = cis_empty (force_cset (show_list (show_IO show_1 show_1 show_bool)) 200 (cimage fst (eval 200 (cp_op \<bullet> cp_op))))"
export_code bar in Haskell module_name Bar

end