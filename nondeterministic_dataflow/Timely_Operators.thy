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
| "activate (Out p x) c sg1 c' sg1' \<Longrightarrow>
   activate Tau c (Seq buf sg1 sg2) c' (Seq (BENQ p x buf) sg1' sg2)" 

fun compile_subgraph where
  "compile_subgraph c (Logic l) = l c"
| "compile_subgraph c (Seq buf sg1 sg2) = map_op projl projr (comp_op Some buf (compile_subgraph c sg1) (compile_subgraph c sg2))"

lemma
  "activate io c sg c' sg' \<Longrightarrow>
   step io (compile_subgraph c sg) (compile_subgraph c' sg')"
  apply (induct io c sg c' sg'  pred: activate)
  subgoal for io l c l' c'
    by simp
  subgoal for p x c sg1 c' sg1' buf sg2
    apply simp
      apply (rule step_map_op)
     apply simp_all
    apply (rule step_Tau_comp_op_L)
       apply simp_all
    oops
   

      find_theorems comp_op Tau Out










   
end