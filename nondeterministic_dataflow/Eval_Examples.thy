theory Eval_Examples
  imports 
    BNA_Operators
    Eval
begin

no_notation Sublist.parallel (infixl "\<parallel>" 50)

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