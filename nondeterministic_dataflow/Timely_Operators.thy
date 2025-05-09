theory Timely_Operators

imports
  Operator
  BNA_Operators
begin

datatype ('c, 'd) subgraph = 
  "apply": Logic "'c \<Rightarrow> 'c \<times> (nat, nat, 'd) op"
  | Seq "nat \<Rightarrow> 'd buf" "('c, 'd) subgraph" "('c, 'd) subgraph"

inductive activate where
  "l c = (c', op) \<Longrightarrow> l' c' = (_, op') \<Longrightarrow> step io op op' \<Longrightarrow> activate io c (Logic l) c' (Logic l')"
| "activate (Out p x) c op1 c' op1' \<Longrightarrow>
   activate Tau c (Seq buf op1 op2) c' (Seq (BENQ p x buf) op1' op2)" 

fun compile_subgraph where
  "compile_subgraph c (Logic l) = l c"
| "compile_subgraph c (Seq buf sg1 sg2) = (
  let (c', op1) = (compile_subgraph c sg1) in 
  let (c'', op2) = (compile_subgraph c' sg2) in 
  (c'', map_op projl projr (comp_op Some buf op1 op2)))"

lemma
  "activate io c t_op c'' t_op' \<Longrightarrow>
   (c', op) = (compile_subgraph c t_op) \<Longrightarrow>
   (c'', op') =  (compile_subgraph c' t_op') \<Longrightarrow>
   step io op op'"
  apply (induct io c t_op c'' t_op' arbitrary: op op' pred: activate)
  subgoal for l c c' opa l' uu_ op'a io
    by simp
  subgoal for p x c op1 c' op1' buf op2
    apply (simp split: prod.splits)
      apply (rule step_map_op)
     apply simp_all
    apply (rule step_Tau_comp_op_L)
       apply simp_all
   

      find_theorems comp_op Tau Out










   
end