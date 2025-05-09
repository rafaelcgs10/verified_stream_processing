theory Timely_Operators

imports
  Operator
  BNA_Operators
begin

datatype ('c, 'd) subgraph = 
  "apply": Logic "'c \<Rightarrow> (nat, nat, 'd) op"
  | Seq "nat \<Rightarrow> nat option" "nat \<Rightarrow> 'd buf" "('c, 'd) subgraph" "('c, 'd) subgraph"

(* inductive activate where
  "step io (l c) (l' c') \<Longrightarrow> activate io c (Logic l) c' (Logic l')"
| "activate (Out p x) c sg1 c' sg1' \<Longrightarrow>
   activate Tau c (Seq buf sg1 sg2) c' (Seq (BENQ p x buf) sg1' sg2)" 
 *)

fun embed_nat where
  "embed_nat (Inl n) =  2 * n"
| "embed_nat (Inr n) =  2 * n + 1"

fun compile_subgraph where
  "compile_subgraph c (Logic l) = l c"
| "compile_subgraph c (Seq wire buf sg1 sg2) = map_op embed_nat embed_nat (comp_op wire buf (compile_subgraph c sg1) (compile_subgraph c sg2))"

(* 
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
    oops *)

inductive wactivate where
  "step io (l c) (l' c') \<Longrightarrow> wactivate io c (Logic l) c' (Logic l')"
| "wactivate (Out p x) c sg1 c' sg1' \<Longrightarrow>
   wire p = Some q \<Longrightarrow>
   wactivate Tau c sg2 c' sg2 \<Longrightarrow>
   wactivate Tau c (Seq wire buf sg1 sg2) c' (Seq wire (BENQ q x buf) sg1' sg2)"
 | "wactivate (Inp p x) c sg2 c' sg2' \<Longrightarrow>
   BHD p buf = x \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow>
   wactivate Tau c sg1 c' sg1' \<Longrightarrow>
   wactivate Tau c (Seq wire buf sg1 sg2) c' (Seq wire (BTL p buf) sg1' sg2')" 
 | "wactivate (Inp p x) c sg1 c' sg1' \<Longrightarrow>
   wactivate Tau c sg2 c' sg2' \<Longrightarrow>
   wactivate (Inp (2 * p) x) c (Seq wire buf sg1 sg2) c' (Seq wire buf sg1' sg2')"  

lemma wstep_trans_taus:
  "wstep io op op' \<Longrightarrow> wstep Tau op' op'' \<Longrightarrow> wstep io op op''"
  apply simp
  apply (metis (no_types, opaque_lifting) relcomppI relcompp_assoc rtranclp_idemp rtranclp_tranclp_absorb tranclp_unfold_left wstep_def)
  done

lemma wstep_Inp_comp_op:
  "wstep (Inp p x) op1 op1' \<Longrightarrow>
   wstep Tau op2 op2' \<Longrightarrow>
   wstep (Inp (2 * p) x) (map_op embed_nat embed_nat (comp_op wire buf op1 op2)) (map_op embed_nat embed_nat (comp_op wire buf op1' op2'))"
  apply (rule wstep_map_op)
   apply (rule wstep_trans_taus)
    apply (rule wstep_comp_op_L_Inp)
      apply assumption
     apply simp_all
  apply blast
  done

lemma
  "wactivate io c sg c' sg' \<Longrightarrow>
   wstep io (compile_subgraph c sg) (compile_subgraph c' sg')"
  apply (induct io c sg c' sg'  pred: wactivate)
  subgoal for io l c l' c'
    apply (rule step_wstep)
    apply simp
    done
  subgoal for p x c sg1 c' sg1' sg2 buf
    apply simp
      apply (metis (mono_tags, lifting) rtranclp_trans step_comp_op_R_Taus step_star_map_op wstep_Tau_comp_op_L wstep_steps_Tau)
    done
  subgoal for p x c sg2 c' sg2' buf sg1 sg1'
    apply simp
    apply (metis (mono_tags, lifting) rtranclp_trans step_comp_op_L_Taus step_star_map_op wstep_Tau_comp_op_R wstep_steps_Tau)
  done
  subgoal for p x c sg1 c' sg1' sg2 sg2' buf
    by (simp add: wstep_Inp_comp_op)
  done



end