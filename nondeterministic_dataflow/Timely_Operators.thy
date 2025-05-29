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

definition summary :: "3 \<Rightarrow> 3 \<Rightarrow> (nat antichain)" where
  "summary l1 l2 = 
  (if l1 = 1 \<and> l2 = 2 then frontier (abs_zmultiset (mset [0], {#}))
   else
   if l1 = 2 \<and> l2 = 3 then frontier (abs_zmultiset (mset [0], {#})) else
   frontier {#}\<^sub>z)"

declare zmultiset_of_antichain_def[code]

global_interpretation sum: enum_dataflow_topology
  "summary :: 3 \<Rightarrow> 3 \<Rightarrow> nat antichain"
  "(+)"
  defines take_step' = "enum_dataflow_topology.take_step summary (+) :: _ \<Rightarrow> (3, nat) Step \<Rightarrow> _ \<Rightarrow> _" and
      after_summary = "dataflow_topology.after_summary (+) :: nat zmultiset \<Rightarrow> nat antichain \<Rightarrow> nat zmultiset"
  sorry

definition mymin_code :: "(nat \<times> 3) set \<Rightarrow> (nat \<times> 3)" 
  where [code del]: "mymin_code = mymin (<)"

lemma mymin_code[code]: "mymin_code (set (x # xs)) = fold (\<lambda>a b. if t_loc_linord (<) a b then a else b) xs x"
  unfolding mymin_code_def
  apply (rule linorderMin)
  apply unfold_locales
      apply auto
  done

definition take_step where
  "take_step = take_step' (<)"

declare sum.take_step.simps[of "((<) :: nat \<Rightarrow> _ \<Rightarrow> _)",  folded mymin_code_def take_step_def, code]

lift_definition zequal :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" is
  "\<lambda> (M, N) (P, Q). (M-N) = (P-Q) \<and> (N-M) = (Q-P)"
  apply (auto simp: equiv_zmset_def)
    apply (metis (full_types) Multiset.diff_right_commute add_diff_cancel_right')
    apply (metis Multiset.diff_right_commute add_diff_cancel_left')
  apply (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute)
  by (metis Multiset.diff_right_commute add_diff_cancel_left')

definition "reachable_locations \<equiv> { loc . \<exists> loc' .
     \<not> is_empty_antichain (summary loc loc') \<or> \<not> is_empty_antichain (summary loc' loc) }"

definition worklist_is_empty :: "(3, nat) configuration \<Rightarrow> bool" where
"worklist_is_empty c = Set.Ball reachable_locations (\<lambda> loc. zequal (c_work c loc) {#}\<^sub>z)"

definition "propagate_all c0 = while_option worklist_is_empty
                                            (take_step PR) c0"

(* Inspired by timely/src/progress/change_batch.rs:20 *)
type_synonym ('loc, 't) change_batch = "('loc \<times> 't zmultiset) list"

(* Inspired by timely/src/progress/subgraph.rs:237 *)
record ('loc, 't) subgraph =
  pointstamp_tracker :: "('loc, 't) configuration"
(* We consider local_pointstamp and final_pointstamp as the same thing in this non-distributed version *)
  local_pointstamp :: "('loc, 't) change_batch"

abbreviation "init_conf \<equiv> \<lparr>c_work = (\<lambda> _. {#}\<^sub>z), c_pts = (\<lambda> _. {#}\<^sub>z), c_imp = (\<lambda> _. {# 0 #}\<^sub>z)\<rparr>"
abbreviation "init_subgraph \<equiv> \<lparr> pointstamp_tracker = init_conf, local_pointstamp = [] \<rparr>"

(* Inspired by timely/src/progress/subgraph.rs:453 *)
(* First migrate all change batches to the worklist, then call propagate_all *)
fun propagate_pointstamps :: "(3, nat) configuration \<Rightarrow> 'a buf \<Rightarrow> (3, nat) configuration option"  where
  "propagate_pointstamps conf [] = propagate_all conf"
| "propagate_pointstamps conf (cb # cbs) = undefined"

definition tscomp_op ::
  "('ip option, 'op1 option, 'd + ('loc, 't) subgraph) op \<Rightarrow>
   ('op1 option, 'op option, 'd + ('loc, 't) subgraph) op \<Rightarrow>
   ('ip option, 'op option, 'd + ('loc, 't) subgraph) op" (infixl "\<bullet>\<^sub>t" 65) where
  "tscomp_op op1 op2 = map_op (case_sum id (\<lambda> _. None)) (case_sum (\<lambda> _. None) id) (comp_op (case_option None (Some o Some)) (\<lambda>_. []) op1 op2)"

lift_definition is_empty_antichain :: "'a :: order antichain \<Rightarrow> bool" is "Set.is_empty".

lemma set_zmset_code[code]:
  "set_zmset (abs_zmultiset x) = (case x of (A, B) \<Rightarrow> set_mset (A - B) \<union> set_mset (B - A))"
  unfolding set_zmset_def
  by transfer (auto simp: set_mset_def)

lemma frontier_code[code]:
  "set_antichain (frontier x) = minimal_antichain {t \<in> set_zmset x. 0 < zcount x t}"
  by transfer' (auto intro!: arg_cong[of _ _ minimal_antichain] zcount_inI)

corec op1 :: "(1 option, 1 option, unit + (2, 256) subgraph) op" where
  "op1 = (Read None (\<lambda> pg. if zcount ((local_pointstamp (projr pg)) 1) 0 > 0 then Write op1 (Some 1) (Inl ()) else Silent op1))"


corec dataflow_op where
  "dataflow_op pg op = Choice (cimage (\<lambda> op. case op of 
     Read None f \<Rightarrow> Silent (dataflow_op pg (f (Inr pg)))
   | Read (Some p) f \<Rightarrow> Read p (\<lambda> x. dataflow_op pg (f (Inl x)))
   | Write op' None (Inr pg') \<Rightarrow> Silent (dataflow_op (propagate_all_mock pg') op')
   | Write op' (Some p) (Inl x) \<Rightarrow> Write (dataflow_op pg op') p x
   | Silent op' \<Rightarrow> Silent (dataflow_op pg op')) (choices op))"

value [GHC] "eval 20 (dataflow_op init_subgraph op1)"

definition advance_frontier_at :: "('loc, 't) subgraph \<Rightarrow> 'loc \<Rightarrow> 't \<Rightarrow> ('loc, 't) subgraph" where
  "advance_frontier_at pg loc t = pg\<lparr>pointstamp_tracker := (pointstamp_tracker pg)\<lparr>c_imp := (c_imp (pointstamp_tracker pg))(loc := {# t #}\<^sub>z)\<rparr>\<rparr>"

corec op2 :: "unit list \<Rightarrow> (1 option, 1 option, unit + (2, 256) subgraph) op" where
  "op2 buf = Read None (\<lambda> pg. pull (Some 1) (case_option
   (if \<not> is_empty_antichain (filter_antichain (\<lambda> t. 2 < t) (frontier ((c_imp (pointstamp_tracker (projr pg))) 2))) \<and> buf \<noteq> [] 
   then Write (op2 (tl buf)) (Some 1) (Inl (hd buf)) 
   else Silent (op2 buf))
   (\<lambda> x. 
   if is_empty_antichain (filter_antichain (\<lambda> t. 2 < t) (frontier ((c_imp (pointstamp_tracker (projr pg))) 2))) 
   then Silent (op2 (buf @ [projl x])) 
   else Write (op2 (tl (buf @ [projl x]))) (Some 1) (Inl (bhd (buf @ [projl x]))))))"

value [GHC] "eval 10 (dataflow_op init_subgraph (op2 []))"

definition advance_cap_at :: "('loc, 't) subgraph \<Rightarrow> 'loc \<Rightarrow> 't :: plus \<Rightarrow> ('loc, 't) subgraph" where
  "advance_cap_at pg loc t = Debug.tracing (String.implode (''advancing cap!''))  pg\<lparr>local_pointstamp := (local_pointstamp pg)(loc := image_zmset ((+)t) ((local_pointstamp pg) loc))\<rparr>"

definition get_cap_at where
  "get_cap_at pg loc = Min (set_zmset (local_pointstamp pg loc))"

corec input_op :: "'a list llist \<Rightarrow> (0 option, 1 option, 'a \<times> nat + (2, nat) subgraph) op" where
  "input_op inps = Read None (\<lambda> pg. (case inps of
    LNil \<Rightarrow> \<odot>
  | LCons xs lxs \<Rightarrow> let cap = get_cap_at (projr pg) 1 in
     writes (Write (input_op lxs) None (Inr (advance_cap_at (projr pg) 1 1))) (Some 1) (map (\<lambda> x. Inl (x, cap)) xs)))"

value [GHC] "eval 20 (dataflow_op init_subgraph (input_op (LCons [Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))))"

term "Debug.tracing (show_nat n)"

abbreviation "maxs ft buf \<equiv> [(n, t) \<leftarrow> buf. ft t \<and> n = Max (set (map fst ((filter (\<lambda> (n', t'). t = t') buf))))]"

abbreviation
   "less_than_frontier pg t \<equiv> (let ft = frontier ((c_imp (pointstamp_tracker pg)) 2) in \<not> is_empty_antichain (filter_antichain (\<lambda> f. t < f) ft))"


value "less_than_frontier (propagate_all_mock (advance_cap_at (init_subgraph :: (2, 256) subgraph) 1 1)) 0"


corec max_op :: "(nat \<times> nat) list \<Rightarrow> (1 option, 1 option, nat \<times> nat + (2, nat) subgraph) op" where
  "max_op buf = Read None (\<lambda> pg. pull (Some 1) (case_option
   (writes (max_op [(n, t) \<leftarrow> buf. \<not> less_than_frontier (projr pg) t]) (Some 1) (map Inl (maxs (less_than_frontier (projr pg)) buf)))
   (\<lambda> x.
   writes (max_op [(n, t) \<leftarrow> buf @ [projl x]. \<not> less_than_frontier (projr pg) t]) (Some 1) (map Inl (maxs (less_than_frontier (projr pg)) (buf @ [projl x]))))))"



value [GHC] "cfilter ((\<noteq>) []) (eval 20 (dataflow_op init_subgraph ((input_op (LCons [5, Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))) \<bullet>\<^sub>t (max_op []))))"

term cfilter

end

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

term "compile_subgraph init_subgraph op1_op2_sg"





end


lemma activate_op1_sg:
  "activate (Out 1 0) init_subgraph op1_sg (init_subgraph\<lparr>local_pointstamp := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) op1_sg"
  apply (rule activate.intros(1))
  apply (subst op1.code)
  apply auto
  done

end

lemma op2_update_internal:
  "op2 \<lparr>pointstamp_tracker = C, local_pointstamp = A\<rparr> = op2 \<lparr>pointstamp_tracker = C, local_pointstamp = B\<rparr>"
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
  "activate Tau init_subgraph op1_op2_sg (init_subgraph\<lparr>local_pointstamp := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)"
  apply (rule activate.intros(2)[where p=1])
    apply (rule activate_op1_sg)
   apply simp
  apply (rule activate.intros(1))
  apply simp
  apply (metis op2_update_internal rtranclp.rtrancl_refl)
  done

lemma
  "activate Tau (init_subgraph\<lparr>local_pointstamp := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)
   (init_subgraph\<lparr>local_pointstamp := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)"


end