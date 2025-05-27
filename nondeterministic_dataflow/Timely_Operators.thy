theory Timely_Operators

imports
  Operator
  BNA_Operators
  Progress_Tracking.Propagate
  Eval
   "HOL-Library.While_Combinator"
  Executable
begin

corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"

lemma foo[friend_of_corec_simps]:
  "(if snd (snd x) = [] then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x)))) else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x))))))) =
         (if snd (snd x) = []
         then if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
              else if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> \<not> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                   else if \<not> isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                        else ctor_op
                              (Abs_op_pre_op
                                (Inr (Inr (if isl (Rep_op_pre_op (dtor_op (fst x))) then undefined
                                           else if isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then undefined else projr (projr (Rep_op_pre_op (dtor_op (fst x))))))))
         else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x)))))))"
  by (auto split: if_splits)

friend_of_corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"
   apply (rule writes.code)
  apply transfer_prover
  done

consts send_update_conf :: "('loc, 't) configuration \<Rightarrow> ('loc, 't) configuration"
consts read_update_conf :: "('loc, 't) configuration \<Rightarrow> ('loc, 't) configuration"

record ('loc, 't) progress =
  conf :: "('loc, 't) configuration"
  internal :: "'loc \<Rightarrow> 't zmultiset"

abbreviation "init_conf \<equiv> \<lparr>c_work = (\<lambda> _. {#}\<^sub>z), c_pts = (\<lambda> _. {#}\<^sub>z), c_imp = (\<lambda> _. {# 0 #}\<^sub>z)\<rparr>"
abbreviation "init_prog \<equiv> \<lparr> conf = init_conf, internal = \<lambda> _. {# 0 #}\<^sub>z \<rparr>"

definition tscomp_op ::
  "('ip option, 'op1 option, 'd + ('loc, 't) progress) op \<Rightarrow>
   ('op1 option, 'op option, 'd + ('loc, 't) progress) op \<Rightarrow>
   ('ip option, 'op option, 'd + ('loc, 't) progress) op" (infixl "\<cdot>" 65) where
  "tscomp_op op1 op2 = map_op (case_sum id (\<lambda> _. None)) (case_sum (\<lambda> _. None) id) (comp_op (case_option None (Some o Some)) (\<lambda>_. []) op1 op2)"

lift_definition is_empty_antichain :: "'a :: order antichain \<Rightarrow> bool" is "Set.is_empty".

lemma set_zmset_code[code]:
  "set_zmset (abs_zmultiset x) = (case x of (A, B) \<Rightarrow> set_mset (A - B) \<union> set_mset (B - A))"
  unfolding set_zmset_def
  by transfer (auto simp: set_mset_def)

lemma frontier_code[code]:
  "set_antichain (frontier x) = minimal_antichain {t \<in> set_zmset x. 0 < zcount x t}"
  by transfer' (auto intro!: arg_cong[of _ _ minimal_antichain] zcount_inI)

corec op1 :: "(1 option, 1 option, unit + (2, 256) progress) op" where
  "op1 = (Read None (\<lambda> pg. if zcount ((internal (projr pg)) 1) 0 > 0 then Write op1 (Some 1) (Inl ()) else Silent op1))"

corec dataflow_op where
  "dataflow_op pg op = Choice (cimage (\<lambda> op. case op of 
     Read None f \<Rightarrow> Silent (dataflow_op pg (f (Inr pg)))
   | Read (Some p) f \<Rightarrow> Read p (\<lambda> x. dataflow_op pg (f (Inl x)))
   | Write op' None (Inr pg') \<Rightarrow> Silent (dataflow_op pg' op')
   | Write op' (Some p) (Inl x) \<Rightarrow> Write (dataflow_op pg op') p x
   | Silent op' \<Rightarrow> Silent (dataflow_op pg op')) (choices op))"

value "eval 20 (dataflow_op init_prog op1)"

definition advance_frontier_at :: "('loc, 't) progress \<Rightarrow> 'loc \<Rightarrow> 't \<Rightarrow> ('loc, 't) progress" where
  "advance_frontier_at pg loc t = pg\<lparr>conf := (conf pg)\<lparr>c_imp := (c_imp (conf pg))(loc := {# t #}\<^sub>z)\<rparr>\<rparr>"

corec op2 :: "unit list \<Rightarrow> (1 option, 1 option, unit + (2, 256) progress) op" where
  "op2 buf = Read None (\<lambda> pg. pull (Some 1) (case_option
   (if \<not> is_empty_antichain (filter_antichain (\<lambda> t. 2 < t) (frontier ((c_imp (conf (projr pg))) 2))) \<and> buf \<noteq> [] 
   then Write (op2 (tl buf)) (Some 1) (Inl (hd buf)) 
   else Silent (op2 buf))
   (\<lambda> x. 
   if is_empty_antichain (filter_antichain (\<lambda> t. 2 < t) (frontier ((c_imp (conf (projr pg))) 2))) 
   then Silent (op2 (buf @ [projl x])) 
   else Write (op2 (tl (buf @ [projl x]))) (Some 1) (Inl (bhd (buf @ [projl x]))))))"

term "\<lambda> pg loc t. pg\<lparr>internal := (internal pg)(loc := image_zmset ((+)t) ((internal pg) loc))\<rparr>"

definition advance_cap_at :: "('loc, 't) progress \<Rightarrow> 'loc \<Rightarrow> 't :: plus \<Rightarrow> ('loc, 't) progress" where
  "advance_cap_at pg loc t = pg\<lparr>internal := (internal pg)(loc := image_zmset ((+)t) ((internal pg) loc))\<rparr>"

find_consts "_ zmultiset \<Rightarrow> _ set"

term "Min (set_zmset {# 0 :: nat #}\<^sub>z)"

definition get_cap_at :: "('loc, 't) progress \<Rightarrow> 'loc \<Rightarrow> 't" where
  "advance_cap_at pg loc = pg\<lparr>internal := internal pg loc \<rparr>"

corec input_op :: "'a list llist \<Rightarrow> (0 option, 1 option, 'a \<times> 256 + (2, 256) progress) op" where
  "input_op inps = (case inps of LNil \<Rightarrow> \<oslash> | LCons xs lxs \<Rightarrow> Read None (\<lambda> pg. writes (input_op lxs) (Some 1) (map Inl xs)))"

value "eval 30 (dataflow_op init_prog (op2 []))"


datatype ('c, 'd) subgraph = 
  "apply": Logic "'c \<Rightarrow> (nat, nat, 'd) op"
  | Comp "nat \<Rightarrow> nat option" "nat \<Rightarrow> 'd buf" "('c, 'd) subgraph" "('c, 'd) subgraph"

fun embed_nat where
  "embed_nat (Inl n) =  2 * n"
| "embed_nat (Inr n) =  2 * n + 1"

fun activate_children where
  "activate_children c (Logic l) = ((\<lambda> op. case op of Write op' p x \<Rightarrow> (send_update_conf c, Write op' p x)) |`| choices (l c))"
(* | "compile_subgraph c (Comp wire buf sg1 sg2) = (map_op embed_nat embed_nat (comp_op wire buf (compile_subgraph c sg1) (compile_subgraph c sg2)))"
 *)

corec compile_subgraph where
  "compile_subgraph c sg = ((\<lambda> (c', op). undefined) |`| activate_children c sg)"  

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



abbreviation "op1_sg \<equiv> Logic op1"
abbreviation "op2_sg \<equiv> Logic (op2 [])"
abbreviation "op1_op2_sg \<equiv> Comp Some (\<lambda> _. []) op1_sg op2_sg"

term "compile_subgraph init_prog op1_op2_sg"


definition summary :: "(op_meta \<times> port) \<Rightarrow> (op_meta \<times> port) \<Rightarrow> (sum antichain)" where
  "summary opp1 opp2 = (case (opp1, opp2) of ((o1, p1), (o2, p2)) \<Rightarrow>
  (if o1=(Op 0) \<and> p1=(trg 0) \<and> o2=(Op 1) \<and> p2=(src 0) then frontier (abs_zmultiset (mset [(0, 0)], {#}))
   else frontier {#}\<^sub>z))"

declare zmultiset_of_antichain_def[code]

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

(* definition initial_state where
"initial_state = (\<lparr> c_work =  (\<lambda>x. zmultiset_of_antichain (frontier (default_capabilities x))),
                    c_pts = (default_capabilities),
                    c_imp = (\<lambda>x.{#}\<^sub>z) \<rparr>
                    :: ((op_meta \<times> port, sum) configuration))" *)

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

definition "propagate_all c0 = while_option worklist_is_empty
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