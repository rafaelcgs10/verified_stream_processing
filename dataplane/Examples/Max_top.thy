theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
begin 

abbreviation "maxs ft buf \<equiv> [(n, c) \<leftarrow> buf. ft (time c) \<and> n = Max (set (map fst ((filter (\<lambda> (n' :: nat, c'). time c = time c') buf))))]"

corec max_top' where
  "max_top' buf = choice2
   (Read (trace (STR ''Reading frontier'') None) (\<lambda> st.
    if is_Inl st \<and> is_Inr (projl st)
    then let impf = projr (projl st) in
      let ft = frontier (impf (0 :: 1)) in
      if print_frontier ft  is_empty_antichain ft 
      then trace (STR ''Empty frontier'') \<oslash> 
      else let result = trace (STR ''Non empty frontier'') (maxs (less_than_frontier ft) buf) in
      push (drop_caps (map snd result) (max_top' [(n, c) \<leftarrow> buf. \<not> less_than_frontier ft (time c)])) (0 :: 1) result
    else
      \<oslash>))
   (pull (1 :: 1) (\<lambda> x. max_top' (buf @ [x])))"


lemma step_max'_top_elim:
  assumes "step io (max_top' buf) op"
  obtains
  x where  "io = Inp None (Inl (Inl x))" "op = \<oslash>"
| x where  "io = Inp None (Inr x)" "op = \<oslash>"
| st impf ft where "io = Inp None (Inl (Inr impf))" "ft = frontier (impf (0 :: 1))"
  "is_empty_antichain ft" "op = \<oslash>"
| st impf ft result where "io = Inp None (Inl (Inr impf))" "ft = frontier (impf (0 :: 1))"
  "\<not> is_empty_antichain ft" "result = maxs (less_than_frontier ft) buf"
  "op = push (drop_caps (map snd result) (max_top' [(n, c) \<leftarrow> buf. \<not> less_than_frontier ft (time c)])) 0 result"
| x t n where "io = Inp (Some 0) (Inr (n, t))"
 "op = Write (max_top' (buf @ [(n, Cap t 1)])) None (Inl (Inl \<lparr> cons = [(1, t, 1)], inte = [(1, t, 1)], prod = [] \<rparr>))"
| x where "io = Inp (Some 0) (Inl x)" "op = \<oslash>"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) max_top'.code)
  apply (cases io; simp split: option.splits sum.splits if_splits)
  subgoal for p x
    apply (cases p; cases x; simp)
    subgoal for p
      apply (cases p; simp)
      subgoal
        apply auto

      apply (elim stepChoiceE disjE; simp)
      apply (elim disjE; simp; hypsubst_thin)
      subgoal           
      apply (elim stepReadE disjE; simp; hypsubst_thin)
        

abbreviation "max_top \<equiv> max_top' []"

abbreviation "ex3 \<equiv> Comp [ (0 :: 2, 0) \<mapsto> (0, 0) ] ex1 (Logic max_top)"

(* value [GHC] "approx_in 32 [VOut (1, 0) (3, 0), VOut (1, 0) (9, 1)] (compile_dataflow ex3)"
 *)
abbreviation "ex4 \<equiv> Comp (\<lambda> _. None) (Logic (input_top (Cap 0 (1 :: 1)) (LCons [0] LNil))) (Logic (input_top (Cap 0 (1 :: 1)) (LCons [Suc 0] LNil)))"

abbreviation "ex5 \<equiv> Comp (\<lambda> _. None) (Logic (\<I> :: (1 option, 1 option, _) op)) (Logic (\<I> :: (1 option, 1 option, _) op))"

abbreviation "ex6 \<equiv> Comp [ (0 :: 4, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex5"

(* value [GHC] "approx_in 15 [VOut (3, 0) (0, 0), VOut (2, 0) (1, 0)] (compile_dataflow ex6)"
 *)
corec cp_op :: "(1 option, 1 option, 'a) op" where "cp_op = Read (Some 1) (\<lambda>x. Write cp_op (Some 1) x)"

abbreviation "ex7 \<equiv> Comp (\<lambda> _. None) (Logic cp_op) (Logic cp_op)"

abbreviation "ex8 \<equiv> Comp [ (0 :: 4, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex7"

(* value [GHC] "approx_in 15 [VOut (3, 0) (0, 0), VOut (2, 0) (1, 0)] (compile_dataflow ex8)"
 *)
abbreviation "ex9 \<equiv> Comp [ (0, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex7 ex7"

abbreviation "ex10 \<equiv> Comp [ (0 :: 6, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex9"

corec max_op :: "nat \<Rightarrow> _ buf llist \<Rightarrow> (1, 1, _ \<times> nat) op" where
  "max_op n inps = (case ldropWhile ((=) []) inps of
     LNil \<Rightarrow> \<oslash>
   | LCons xs lxs \<Rightarrow> Write (max_op (n + the_enat (llength (ltakeWhile ((=) []) inps))) (LCons xs lxs)) 1 (Max (set xs), n + the_enat (llength (ltakeWhile ((=) []) inps))))"

abbreviation "inp_top c inps \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, (p :: 1)))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, (p :: 1)))) (input_top c inps)"
abbreviation "m_top buf \<equiv>  map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, (p :: 1)))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, (p :: 1)))) (max_top' buf)"

abbreviation "inp_m_top i inps buf1 buf2 \<equiv> map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0 :: 2, 1 :: 1) \<mapsto> Inr (1, 1)] buf1 (inp_top (Cap i 1) inps) (m_top buf2))"

lemma
  \<open>xs @@- ys @@- lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps1 (iterates Suc i))) =
   lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps2 (iterates Suc j))) \<Longrightarrow>
   inrbufs1 = buf1 (Inr (1, 1)) \<Longrightarrow>
   \<forall> x \<in> set inrbufs1. is_Inr x \<Longrightarrow>
   xs = map projr inrbufs1 \<Longrightarrow>
   ys = map (\<lambda> (n, c). (n, time c)) buf2 \<Longrightarrow>
   edges sg = (\<lambda> l. if node l = 0 \<and> port l = Src 1 then [Loc 1 (Trg 0)] else []) \<Longrightarrow>
   dataflow_op sg (inp_m_top i inps1 buf1 buf2) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (max_op j inps2)\<close>
proof (coinduction arbitrary: inps1 inps2 buf1 buf2 inrbufs1 xs ys i j sg rule: wbisim_coinduct)
  case SIM1
  then show ?case
    apply -
    apply (elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp; hypsubst_thin)


end