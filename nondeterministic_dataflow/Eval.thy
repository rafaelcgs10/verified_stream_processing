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

fun eval' :: "nat \<Rightarrow> ('i, 'o, 'd :: {countable}) op \<Rightarrow> (('i, 'o, 'd) VIO list \<times> ('i, 'o, 'd) op) cset"  where
  "eval' 0 op = {|([], op)|}"
| "eval' (Suc n) (Write op p x) = cimage (\<lambda>(t, op). (VOut p x # t, op)) (eval' n op)"
| "eval' (Suc n) (Read p f) = cUnion (cimage (\<lambda>x. cimage (\<lambda>(t, op). (VInp p x # t, op)) (eval' n (f x))) (cUNIV :: 'd cset))"
| "eval' (Suc n) (Silent op) = (cimage (\<lambda>(t, op). (t, op)) (eval' n op))"
| "eval' (Suc n) (Choice ops) = (if ops = {||} then {|([], \<oslash>)|} else cUnion (cimage (eval' n) ops))"

definition "eval n op = cimage fst (eval' n op)"
definition "approx_eq n op op' = 
  (cis_empty (cfilter (\<lambda>xs. cis_empty (cfilter (\<lambda>ys. prefix xs ys) (cimage fst (eval' (2 * n) op')))) (cimage fst (eval' n op)))  \<and>
   cis_empty (cfilter (\<lambda>xs. cis_empty (cfilter (\<lambda>ys. prefix xs ys) (cimage fst (eval' (2 * n) op)))) (cimage fst (eval' n op'))))"

definition "approx_in n pfx op = 
  (\<not> cis_empty (cfilter (\<lambda>xs. prefix pfx xs) (cimage fst (eval' n op))))"

fun traceprefix :: "nat \<Rightarrow> ('i, 'o, 'd) VIO list \<Rightarrow> ('i, 'o, 'd :: {countable}) op \<Rightarrow> bool" where
  "traceprefix n [] _ = True"
| "traceprefix n (VInp p x # lxs) (Read q f) = (p = q \<and> traceprefix n lxs (f x))"
| "traceprefix n (VOut p x # lxs) (Write op q y) = (p = q \<and> x = y \<and> traceprefix n lxs op)"
| "traceprefix (Suc n) lxs (Silent op) = traceprefix n lxs op"
| "traceprefix (Suc n) lxs (Choice ops) = (\<not> cis_empty (cfilter (traceprefix n lxs) ops))"
| "traceprefix _ _ _ = False"

end