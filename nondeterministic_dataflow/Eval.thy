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

definition W42 :: "(2,1,nat) op" where "W42 = Write end_op 1 42"
definition CP :: "(1,1,bool) op" where "CP = Read 1 (\<lambda>x. Write end_op 1 x)"
corec cp_op :: "(1,1,bool) op" where "cp_op = Read 1 (\<lambda>x. Write cp_op 1 x)"

value [GHC] "eval 10 (ex1_op :: (nat,nat,nat) op)"
value [GHC] "eval 10 (ex2_op :: (nat,nat,nat) op)"
value [GHC] "eval 10 (ex3_op :: (nat,nat,nat) op)"
value [GHC] "eval 10 W42"
value [GHC] "eval 10 CP"
value [GHC] "eval 10 cp_op"
value [GHC] "eval 1000 (CP \<bullet> CP)"
value [GHC] "eval 10 (cp_op \<bullet> cp_op)"
value [GHC] "eval 10 (cp_op \<parallel> cp_op)"

value [GHC] "traceprefix 1000000 [VInp (Inl 0) (Some 1), VInp (Inr 0) (Some 1), VOut (Inl 0) (Some 1), VOut (Inr 0) (Some 1)] (\<Q> \<bullet> \<C> :: (2 + 2, 2 + 2, nat option) op)"

value [GHC] "approx_in 12 [VInp (Inl 0) (Some 1), VInp (Inr 0) (Some 1), VOut (Inl 0) (Some 1), VOut (Inr 0) (Some 1)] (\<Q> \<bullet> \<C> :: (2 + 2, 2 + 2, nat option) op)"
value [GHC] "eval 4 ((\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q>\<turnstile> \<parallel> \<Q>\<turnstile>) :: (2 + 2, 2 + 2, bool option) op)"
value [GHC] "approx_eq 4 (\<Q> \<bullet> \<C> :: (2 + 2, 2 + 2, bool option) op)
                  ((\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q>\<turnstile> \<parallel> \<Q>\<turnstile>) :: (2 + 2, 2 + 2, bool option) op)"
value [GHC] "\<not> approx_eq 4 (\<Q> \<bullet> \<C> :: (2 + 2, 2 + 2, bool option) op) \<I>"
value [GHC] "\<not> approx_eq 4 (\<Q> \<bullet> \<C> :: (2 + 2, 2 + 2, bool option) op) \<X>"
value [GHC] "cfilter (\<lambda>x. \<not> x |\<in>| eval 4 (map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>))) (eval 4 ((\<Q> \<parallel> \<I>) \<bullet> \<Q> :: ((2 + 2) + 2, 2, bool option) op))"
value [GHC] "approx_eq 4 ((\<Q> \<parallel> \<I>) \<bullet> \<Q> :: ((2 + 2) + 2, 2, bool option) op) (map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>))"

end