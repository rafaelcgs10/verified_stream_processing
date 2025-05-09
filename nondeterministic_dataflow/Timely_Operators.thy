theory Timely_Operators

imports
  Operator
  BNA_Operators
  Progress_Tracking.Propagate
begin

datatype ('c, 'd) subgraph = 
  "apply": Logic "'c \<Rightarrow> (nat, nat, 'd) op"
  | Comp "nat \<Rightarrow> nat option" "nat \<Rightarrow> 'd buf" "('c, 'd) subgraph" "('c, 'd) subgraph"

fun embed_nat where
  "embed_nat (Inl n) =  2 * n"
| "embed_nat (Inr n) =  2 * n + 1"

fun compile_subgraph where
  "compile_subgraph c (Logic l) = l c"
| "compile_subgraph c (Comp wire buf sg1 sg2) = map_op embed_nat embed_nat (comp_op wire buf (compile_subgraph c sg1) (compile_subgraph c sg2))"

inductive activate where
  "wstep io (l c) (l' c') \<Longrightarrow> activate io c (Logic l) c' (Logic l')"
| "activate (Out p x) c sg1 c' sg1' \<Longrightarrow>
   wire p = Some q \<Longrightarrow>
   activate Tau c sg2 c' sg2 \<Longrightarrow>
   activate Tau c (Comp wire buf sg1 sg2) c' (Comp wire (BENQ q x buf) sg1' sg2)"
 | "activate (Inp p x) c sg2 c' sg2' \<Longrightarrow>
   BHD p buf = x \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow>
   activate Tau c sg1 c' sg1' \<Longrightarrow>
   activate Tau c (Comp wire buf sg1 sg2) c' (Comp wire (BTL p buf) sg1' sg2')" 
 | "activate (Inp p x) c sg1 c' sg1' \<Longrightarrow>
   activate Tau c sg2 c' sg2' \<Longrightarrow>
   activate (Inp (2 * p) x) c (Comp wire buf sg1 sg2) c' (Comp wire buf sg1' sg2')"  

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

lemma activate_compiles:
  "activate io c sg c' sg' \<Longrightarrow>
   wstep io (compile_subgraph c sg) (compile_subgraph c' sg')"
  apply (induct io c sg c' sg'  pred: activate)
  subgoal for io l c l' c'
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

record ('loc, 't) progress =
  conf :: "('loc, 't) configuration"
  cap :: "'loc \<Rightarrow> 't zmultiset"

abbreviation "init_conf \<equiv> \<lparr>c_work = (\<lambda> _. {#}\<^sub>z), c_pts = (\<lambda> _. {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>"
abbreviation "init_prog \<equiv> \<lparr> conf = init_conf, cap = \<lambda> _. {# 1 #}\<^sub>z \<rparr>"

corec op1 :: "(2, nat) progress \<Rightarrow> (nat, nat, nat) op" where
  "op1 pg = (if zcount ((cap pg) 1) 1 > 0 then Write (op1 (pg\<lparr>cap := (cap pg)(1 := {#}\<^sub>z)\<rparr>)) 1 0  else Silent (op1 pg))"

corec op2 :: "(2, nat) progress \<Rightarrow> (nat, nat, nat) op" where
  "op2 pg = pull 1 (case_option (Silent (op2 pg)) (\<lambda> x. if \<exists> t. t \<in>\<^sub>A frontier ((c_imp (conf pg)) 2) \<and> 1 \<le> t then Write \<oslash> 1 x else Silent (op2 pg)))"

abbreviation "op1_sg \<equiv> Logic op1"
abbreviation "op2_sg \<equiv> Logic op2"
abbreviation "op1_op2_sg \<equiv> Comp Some (\<lambda> _. []) op1_sg op2_sg"

lemma activate_op1_sg:
  "activate (Out 1 0) init_prog op1_sg (init_prog\<lparr>cap := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) op1_sg"
  apply (rule activate.intros(1))
  apply (subst op1.code)
  apply auto
  done

lemma op2_update_cap:
  "op2 \<lparr>conf = C, cap = A\<rparr> = op2 \<lparr>conf = C, cap = B\<rparr>"
  apply (coinduction arbitrary: A B C rule: op.coinduct_upto)
  apply (intro conjI impI)
  apply (subst (1 2) op2.code, simp)
  apply (subst (asm) op2.code, simp)
           apply (subst (asm) op2.code, simp)
  apply (subst (1 2) op2.code, simp)
  apply (subst (asm) op2.code, simp)
  apply (subst (asm) op2.code, simp)
     apply (subst (asm) op2.code, simp)
    apply (subst (1 2) op2.code, simp)
  subgoal
    apply (subst (3 4) op2.code, simp)
    apply (intro rel_setI)
     apply simp_all
    subgoal
      apply (elim disjE)
      subgoal
        apply hypsubst_thin
        apply (smt (verit, ccfv_threshold) transp_op.cong_Silent transp_op.cong_base)        
        done
      subgoal
        apply hypsubst_thin
        apply (rule disjI2)
        apply (rule transp_op.cong_Read)
         apply simp
        apply (smt (verit, del_insts) comp_apply option.simps(5) rel_funI transp_op.cong_Silent transp_op.cong_base transp_op.cong_refl)
        done
      done
    subgoal
      apply (elim disjE)
      subgoal
        apply hypsubst_thin
        apply (smt (verit, ccfv_threshold) transp_op.cong_Silent transp_op.cong_base)        
        done
      subgoal
        apply hypsubst_thin
        apply (rule disjI2)
        apply (rule transp_op.cong_Read)
         apply simp
        apply (smt (verit, del_insts) comp_apply option.simps(5) rel_funI transp_op.cong_Silent transp_op.cong_base transp_op.cong_refl)
        done
      done
    done
  apply (subst (asm) op2.code, simp)
  done

lemma
  "activate Tau init_prog op1_op2_sg (init_prog\<lparr>cap := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)"
  apply (rule activate.intros(2)[where p=1])
    apply (rule activate_op1_sg)
   apply simp
  apply (rule activate.intros(1))
  apply simp
  apply (metis op2_update_cap rtranclp.rtrancl_refl)
  done


end