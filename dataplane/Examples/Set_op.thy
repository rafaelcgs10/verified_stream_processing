theory Set_op

imports
  Nondeterministic_Dataflow.Operator
begin

corec set_op :: "('a \<times> 'b) cset \<Rightarrow> ('a \<times> 'b) cset \<Rightarrow> ('c, 'a, 'b) op \<Rightarrow> ('c, 'a, 'b) op" where
  "set_op S S' op = choice2
  (Choice (cimage (\<lambda> op. case op of
     Write op p x \<Rightarrow> Silent (set_op (cinsert (p, x) S) S' op) 
   | Silent op \<Rightarrow> Silent (set_op S S' op)
   | Read _ _ \<Rightarrow> Code.abort (STR ''Set_op can only output'') (\<lambda> _. \<oslash>)
   ) (choices op))
  
   )
  (Choice (cimage (\<lambda> (p, x). Write (set_op S (cinsert (p, x) S') op) p x) (S - S')))"
  

(* lemma
  "wtraces (set_op op) = (wtraces op)"
  unfolding wtraces_def
  apply auto
  subgoal for vios
    oops
 *)
end