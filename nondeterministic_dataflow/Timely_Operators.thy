theory Timely_Operators

imports
  Operator
  BNA_Operators
  Progress_Tracking.Propagate
  Eval
   "HOL-Library.Debug"
  Executable
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
  internal :: "'loc \<Rightarrow> 't zmultiset"

abbreviation "init_conf \<equiv> \<lparr>c_work = (\<lambda> _. {#}\<^sub>z), c_pts = (\<lambda> _. {#}\<^sub>z), c_imp = (\<lambda> _. {# 0 #}\<^sub>z)\<rparr>"
abbreviation "init_prog \<equiv> \<lparr> conf = init_conf, internal = \<lambda> _. {# 0 #}\<^sub>z \<rparr>"

lift_definition is_empty_antichain :: "'a :: order antichain \<Rightarrow> bool" is "Set.is_empty".

lemma set_zmset_code[code]:
  "set_zmset (abs_zmultiset x) = (case x of (A, B) \<Rightarrow> set_mset (A - B) \<union> set_mset (B - A))"
  unfolding set_zmset_def
  by transfer (auto simp: set_mset_def)

lemma frontier_code[code]:
  "set_antichain (frontier x) = minimal_antichain {t \<in> set_zmset x. 0 < zcount x t}"
  by transfer' (auto intro!: arg_cong[of _ _ minimal_antichain] zcount_inI)

corec op1 :: "(2, nat) progress \<Rightarrow> (nat, nat, unit) op" where
  "op1 pg = (if zcount ((internal pg) 1) 1 > 0 then Write (op1 (pg\<lparr>internal := (internal pg)(1 := {#}\<^sub>z)\<rparr>)) 1 () else Silent (op1 pg))"

abbreviation "advancing \<equiv> Debug.tracing (String.implode ''advancing'')"

value "{# 1 :: nat #}\<^sub>z + {# 1 :: nat #}\<^sub>z"

value "update_zmultiset {# 1 :: nat #}\<^sub>z 1 1"

find_consts "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset"

definition advance_frontier_at :: "('loc, 't) progress \<Rightarrow> 'loc \<Rightarrow> 't \<Rightarrow> ('loc, 't) progress" where
  "advance_frontier_at pg loc t = advancing pg\<lparr>conf := (conf pg)\<lparr>c_imp := (c_imp (conf pg))(loc := {# t #}\<^sub>z)\<rparr>\<rparr>"

corec op2 :: "unit list \<Rightarrow> (2, nat) progress \<Rightarrow> (nat, nat, unit) op" where
  "op2 buf pg = pull 1 (case_option
   (if \<not> is_empty_antichain (filter_antichain (\<lambda> t. \<not> even t) (frontier ((c_imp (conf pg)) 2))) \<and> buf \<noteq> [] 
   then Write (op2 (tl buf) pg) 1 (hd buf) 
   else Silent (op2 buf (advance_frontier_at pg 2 1)))
   (\<lambda> x. 
   if is_empty_antichain (filter_antichain (\<lambda> t. \<not> even t) (frontier ((c_imp (conf pg)) 2))) 
   then Silent (op2 (buf @ [x]) (advance_frontier_at pg 2 1)) 
   else Write (op2 (tl (buf @ [x])) pg) 1 (bhd (buf @ [x]))))"

value "eval 8 (op2 [] init_prog)"


abbreviation "op1_sg \<equiv> Logic op1"
abbreviation "op2_sg \<equiv> Logic (op2 [])"
abbreviation "op1_op2_sg \<equiv> Comp Some (\<lambda> _. []) op1_sg op2_sg"

term "compile_subgraph init_prog op1_op2_sg"

global_interpretation sum: enum_dataflow_topology
  "summary :: (op_meta \<times> port) \<Rightarrow> (op_meta \<times> port) \<Rightarrow> sum antichain"
  "results_in :: sum \<Rightarrow> sum \<Rightarrow> sum"
  defines take_step' = "enum_dataflow_topology.take_step summary results_in :: _ \<Rightarrow> (op_meta \<times> port, sum) Step \<Rightarrow> _ \<Rightarrow> _" and
      after_summary = "dataflow_topology.after_summary results_in :: sum zmultiset \<Rightarrow> sum antichain \<Rightarrow> sum zmultiset"
  sorry

definition mymin_code :: "(sum \<times> (op_meta \<times> port)) set \<Rightarrow> (sum \<times> (op_meta \<times> port))" where [code del]: "mymin_code = mymin (<)"

lemma mymin_code[code]: "mymin_code (set (x # xs)) = fold (\<lambda>a b. if t_loc_linord (<) a b then a else b) xs x"
  unfolding mymin_code_def
  apply (rule linorderMin)
  apply unfold_locales
      apply auto
  done


term take_step'

definition take_step where
  "take_step = take_step' (<)"

declare sum.take_step.simps[of "((<) :: sum \<Rightarrow> _ \<Rightarrow> _)",  folded mymin_code_def take_step_def, code]

definition initial_state where
"initial_state = (\<lparr> c_work =  (\<lambda>x. zmultiset_of_antichain (frontier (default_capabilities x))),
                    c_pts = (default_capabilities),
                    c_imp = (\<lambda>x.{#}\<^sub>z) \<rparr>
                    :: ((op_meta \<times> port, sum) configuration))"

lift_definition zequal :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" is
  "\<lambda> (M, N) (P, Q). (M-N) = (P-Q) \<and> (N-M) = (Q-P)"
  apply (auto simp: equiv_zmset_def)
    apply (metis (full_types) Multiset.diff_right_commute add_diff_cancel_right')
    apply (metis Multiset.diff_right_commute add_diff_cancel_left')
  apply (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute)
  by (metis Multiset.diff_right_commute add_diff_cancel_left')

definition "reachable_locations \<equiv> { loc . \<exists> loc' .
     \<not> is_empty_antichain (summary loc loc') \<or> \<not> is_empty_antichain (summary loc' loc) }"

definition worklist_is_empty :: "(op_meta \<times> port, sum) configuration \<Rightarrow> bool" where
"worklist_is_empty c = Set.Ball reachable_locations (\<lambda> loc. zequal (c_work c loc) {#}\<^sub>z)"

definition "prop_metaagate_all c0 = while_op_metation worklist_is_empty
                                            (take_step PR) c0"



end


lemma activate_op1_sg:
  "activate (Out 1 0) init_prog op1_sg (init_prog\<lparr>internal := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) op1_sg"
  apply (rule activate.intros(1))
  apply (subst op1.code)
  apply auto
  done

end

lemma op2_update_internal:
  "op2 \<lparr>conf = C, internal = A\<rparr> = op2 \<lparr>conf = C, internal = B\<rparr>"
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
  "activate Tau init_prog op1_op2_sg (init_prog\<lparr>internal := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)"
  apply (rule activate.intros(2)[where p=1])
    apply (rule activate_op1_sg)
   apply simp
  apply (rule activate.intros(1))
  apply simp
  apply (metis op2_update_internal rtranclp.rtrancl_refl)
  done

lemma
  "activate Tau (init_prog\<lparr>internal := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)
   (init_prog\<lparr>internal := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)"


end