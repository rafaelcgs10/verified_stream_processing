theory Timely_Operators

imports
  Operator
  BNA_Operators
begin

datatype ('c, 'd) subgraph = 
  "apply": Logic "'c \<Rightarrow> (nat, nat, 'd) op"
  | Seq "nat \<Rightarrow> 'd buf" "('c, 'd) subgraph" "('c, 'd) subgraph"


inductive activate where
  "step io (l c) (l' c') \<Longrightarrow> activate io c (Logic l) c' (Logic l')"
| "activate (Out p x) c op1 c' op1' \<Longrightarrow>
   activate Tau c (Seq buf op1 op2) c' (Seq (BENQ p x buf) op1' op2)" 
 
(* friend_of_corec map_op where
  "map_op f g (op :: ('i, 'o, 'd) op) = 
  (case op of Silent op' \<Rightarrow> 
    Silent (map_op f g op') 
  | Write op' p x \<Rightarrow> Write (map_op f g op') (g p) x 
  | Read p f' \<Rightarrow> Read (f p) (map_op f g o f')
  | Choice ops \<Rightarrow> Choice (map_op f g |`| ops))"
 *)



fun compile_subgraph where
  "compile_subgraph c (Logic l) = l c"
| "compile_subgraph c (Seq buf sg1 sg2) = map_op projl projr (comp_op Some buf (compile_subgraph c sg1) (compile_subgraph c sg2))"

lemma
  "activate io c t_op c' t_op' \<Longrightarrow>
   step io (compile_subgraph c t_op) (compile_subgraph c' t_op')"
  apply (induct io c t_op c' t_op' pred: activate)
  subgoal for io op c op' c'
    by simp
  subgoal for p x c op1 c' op1' buf op2
    apply simp
      apply (rule step_map_op)
     apply simp_all
    apply (rule step_Tau_comp_op_L)
    apply simp_all

      find_theorems comp_op Tau Out










   
end