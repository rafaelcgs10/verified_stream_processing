section \<open>The composition operator\<close>

theory Composition

imports
  Operator
begin

inductive comp_producing :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow> ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> nat \<Rightarrow> bool" for wire where
  "comp_producing wire buf End End 0"
| "comp_producing wire buf (Read p1 f1) End 0"
| "wire p1 = None \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) End 0"
| "wire p1 = Some p \<Longrightarrow> comp_producing wire buf op1' End n \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) End (Suc n)"
| "comp_producing wire buf End (Write op2' p2 x2) 0"
| "comp_producing wire buf (Read p1 f1) (Write op2' p2 x2) 0"
| "comp_producing wire buf (Write op1' p1 x1) (Write op2' p2 x2) 0"
| "p2 \<notin> ran wire \<Longrightarrow> comp_producing wire buf End (Read p2 f2) 0"
| "p2 \<in> ran wire \<Longrightarrow> comp_producing wire (BTL p2 (bend o buf)) End (f2 (BHD p2 (bend o buf))) n \<Longrightarrow> comp_producing wire buf End (Read p2 f2) (Suc n)"
| "comp_producing wire buf (Read p1 f1) (Read p2 f2) 0"
| "p2 \<notin> ran wire \<or> wire p1 = None \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) 0"
| "p2 \<in> ran wire \<Longrightarrow> wire p1 = Some p \<Longrightarrow>
    comp_producing wire (BTL p2 (BENQ p x1 buf)) op1' (f2 (BHD p2 (BENQ p x1 buf))) n \<Longrightarrow>
    comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) (Suc n)"

lemma comp_producing_inject: "comp_producing wire buf op1 op2 i \<Longrightarrow> comp_producing wire buf op1 op2 j \<Longrightarrow> i = j"
proof (induct buf op1 op2 i arbitrary: j rule: comp_producing.induct)
  case (4 p1 p buf op1' n x1)
  from 4(4,1-2) 4(3)[of "j - 1"] show ?case
    by (elim comp_producing.cases[of _ _ "Write op1' p1 x1"]) (auto simp del: fun_upd_apply)
next
  case (9 p2 buf f2 n)
  from 9(4,1-2) 9(3)[of "j - 1"] show ?case
    by (elim comp_producing.cases[of _ _ _ "Read p2 f2"]) (auto simp del: fun_upd_apply)
next
  case (12 p2 p1 p buf x1 op1' f2 n)
  from 12(5,1-3) 12(4)[of "j - 1"] show ?case
    by (elim comp_producing.cases[of _ _ _ "Read p2 f2"]) (auto simp del: fun_upd_apply)
qed (auto elim: comp_producing.cases)

lemma The_comp_producing: "comp_producing wire buf op1 op2 i \<Longrightarrow> The (comp_producing wire buf op1 op2) = i"
  using comp_producing_inject by fast

(*workaround about termination issue in corecursive*)
lemma case_prod_cong4[fundef_cong]:
  fixes prod prod' f g
  shows "prod = prod' \<Longrightarrow>
    (\<And>x1 x2 y1 y2. prod' = ((x1, x2), (y1, y2)) \<Longrightarrow> f x1 x2 y1 y2 = g x1 x2 y1 y2) \<Longrightarrow>
    ((\<lambda>((x1, x2), (y1, y2)). f x1 x2 y1 y2) prod) = ((\<lambda>((x1, x2), (y1, y2)). g x1 x2 y1 y2) prod')"
  by (auto split: prod.splits)

corecursive comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op" where
  "comp_op wire buf op1 op2 =
     (let comp_op' = (\<lambda>buf' op1' op2'. if \<exists>n. comp_producing wire buf op1 op2 n then comp_op wire buf' op1' op2' else End) in
     case (op1, op2) of
     (End, End) \<Rightarrow> End
   | (End, Write op2' p2 x2) \<Rightarrow> Write (comp_op wire (bend o buf) End op2') (Inr p2) x2
   | (End, Read p2 f2) \<Rightarrow> let buf' = bend o buf in if p2 \<in> ran wire
     then comp_op' (BTL p2 buf') End (f2 (BHD p2 buf'))
     else Read (Inr p2) (\<lambda>y2. comp_op wire buf' End (f2 y2))
   | (Read p1 f1, End) \<Rightarrow> Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) End)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) x2)
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then Read (Inl p1) (\<lambda>y1. comp_op wire (BTL p2 buf) (f1 y1) (f2 (BHD p2 buf)))
     else Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))
   | (Write op1' p1 x1, End) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (comp_op wire buf op1' End) (Inl p1) x1
     | Some p \<Rightarrow> comp_op' buf op1' End)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1
     | Some p \<Rightarrow> Write (comp_op wire (BENQ p x1 buf) op1' op2') (Inr p2) x2)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (BTL p2 buf) op1' (f2 (BHD p2 buf))) (Inl p1) x1
     | Some p \<Rightarrow> comp_op' (BTL p2 (BENQ p x1 buf)) op1' (f2 (BHD p2 (BENQ p x1 buf))))
     else (case wire p1 of
       None \<Rightarrow> Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (BENQ p x1 buf) op1' (f2 y2))))"
  by (relation "measure (\<lambda>((wire, buf), op1, op2). THE i. comp_producing wire buf op1 op2 i)")
    (auto 0 3 simp: The_comp_producing elim: comp_producing.cases)

lemma not_comp_producing_eq_End: "\<forall>n. \<not> comp_producing wire buf op1 op2 n \<Longrightarrow> comp_op wire buf op1 op2 = End"
  apply (coinduction arbitrary: buf op1 op2)
  apply auto
  subgoal for buf op1 op2
    apply (subst (asm) comp_op.code)
    apply (auto split: op.splits if_splits option.splits simp: Let_def intro: comp_producing.intros)
    done
  subgoal for buf op1 op2
    apply (subst (asm) comp_op.code)
    apply (auto split: op.splits if_splits option.splits simp: Let_def intro: comp_producing.intros)
    done
  done

lemma comp_op_code[code]:
  "comp_op wire buf op1 op2 = (case (op1, op2) of
     (End, End) \<Rightarrow> End
   | (End, Write op2' p2 x2) \<Rightarrow> Write (comp_op wire (bend o buf) End op2') (Inr p2) x2
   | (End, Read p2 f2) \<Rightarrow> let buf = bend o buf in if p2 \<in> ran wire
     then comp_op wire (BTL p2 buf) End (f2 (BHD p2 buf))
     else Read (Inr p2) (\<lambda>y2. comp_op wire buf End (f2 y2))
   | (Read p1 f1, End) \<Rightarrow> Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) End)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) x2)
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then Read (Inl p1) (\<lambda>y1. comp_op wire (BTL p2 buf) (f1 y1) (f2 (BHD p2 buf)))
     else Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))
   | (Write op1' p1 x1, End) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (comp_op wire buf op1' End) (Inl p1) x1
     | Some p \<Rightarrow> comp_op wire buf op1' End)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1
     | Some p \<Rightarrow> Write (comp_op wire (BENQ p x1 buf) op1' op2') (Inr p2) x2)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (BTL p2 buf) op1' (f2 (BHD p2 buf))) (Inl p1) x1
     | Some p \<Rightarrow> comp_op wire (BTL p2 (BENQ p x1 buf)) op1' (f2 (BHD p2 (BENQ p x1 buf))))
     else (case wire p1 of
       None \<Rightarrow> Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (BENQ p x1 buf) op1' (f2 y2))))"
  apply (subst comp_op.code)
  apply (simp split: op.splits option.splits add: Let_def)
  apply safe
  subgoal for p1 f1 op2' p2 x2
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1 p
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  done
simps_of_case comp_op_simps': comp_op_code[unfolded prod.case]

simps_of_case comp_op_simps[simp]: comp_op.code[unfolded prod.case Let_def]

section\<open>Inputs of comp_op\<close>

lemma inputs_comp_producing:
  "p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow> 
   \<exists> n. comp_producing wire buf op1 op2 n"
  using not_comp_producing_eq_End by fastforce

lemma not_comp_producing_no_inputs:
  "\<forall>x. \<not> comp_producing wire buf op1 op2 x \<Longrightarrow>
   inputs (comp_op wire buf op1 op2) = {}"
  by (simp add: not_comp_producing_eq_End)


lemma inputs_comp_op_1:
  "p \<in> inputs op1 \<Longrightarrow>
   Inl p \<in> inputs (comp_op wire buf op1 op2)"
  apply (induct p op1 arbitrary: buf op2 rule: op.set_induct(1))
  subgoal for z1 z2 buf op2
    apply (cases op2)
      apply auto
    done
  subgoal for z1 z2 xa xb buf op2
    apply (cases op2)
      apply auto
    done
  subgoal for z1a z2a z3 xd buf op2
    apply (cases op2)
      apply (auto split: option.splits)
     defer
    subgoal
      by (metis all_not_in_conv comp_producing.intros(4) not_comp_producing_eq_End op.simps(37))
    subgoal for x11 x12 x2
      by (meson comp_producing.intros(12) inputs_comp_producing)
    done
  done

lemma comp_op_Read_simps_case:
  "comp_op wire buf (Read p f) op2 =
   Read (Inl p) (\<lambda> x. case op2 of
     End \<Rightarrow> comp_op wire buf (f x) End
   | Write op' p' y \<Rightarrow> Write (comp_op wire buf (f x) op') (Inr p') y
   | Read p' f' \<Rightarrow> (if p' \<in> ran wire then comp_op wire (buf(p' := btl (buf p'))) (f x) (f' (BHD p' buf)) else (Read (Inr p') (\<lambda>y2. comp_op wire buf (f x) (f' y2)))))"
  apply (cases op2)
    apply auto
  done

lemma input_depth_Read_0[simp]:
  "input_depth p (Read p f) = 0"
  by (simp add: input_depth_Read)

lemma input_depth_Suc_diff[simp]:
  "input_depth p (comp_op wire buf op1 op2) = Suc n \<Longrightarrow>
   op1 = Read p' f \<Longrightarrow>
   Inl p' \<noteq> p"
  by (metis (no_types, lifting) Zero_neq_Suc comp_op_Read_simps_case input_depth_Read_0)

lemma input_depth_Read_Write[simp]:
  "p \<in> inputs (comp_op wire buf (Read p1 f1) (Write op' p' x)) \<Longrightarrow>
   p \<noteq> Inl p1 \<Longrightarrow>
   input_depth p (comp_op wire buf (Read p1 f1) (Write op' p' x)) = 
   Suc (Suc (input_depth p (comp_op wire buf (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>y1. Write (comp_op wire buf (f1 y1) op') (Inr p') x)) x. p \<in> inputs (comp_op wire buf (f1 x) op'))) op')))"
  apply simp
  apply (subst input_depth_Read_diff)
    apply fast
   apply force
  apply (subst input_depth_Write)
   apply force
  apply auto
  done


lemma comp_producing_inputs_comp_op:
  fixes op1 :: "('ip1, 'op1, 'd) op" and op2 :: "('ip2, 'op2, 'd) op"
  shows "comp_producing wire buf op1 op2 i \<Longrightarrow>
    p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow>
    input_depth p (comp_op wire buf op1 op2) = Suc n \<Longrightarrow>
    (\<And>buf (op1 :: ('ip1, 'op1, 'd) op) (op2 :: ('ip2, 'op2, 'd) op).
        input_depth p (comp_op wire buf op1 op2) \<le> n \<Longrightarrow>
        p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow>
        p \<in> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)) \<Longrightarrow>
    p \<in> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  apply (induct buf op1 op2 i rule: comp_producing.induct)
             apply (auto 7 7 intro: le_SucI split: if_splits option.splits)
          apply (fastforce intro!: le_SucI)+
  subgoal
    apply (rule ccontr)
    apply (subst (asm) input_depth_Read_diff)
      apply fastforce+
    done
  subgoal
    apply fastforce+
    done
  subgoal for buf p1 f1 p2 f2 x y
    apply (subst (asm) input_depth_Read_diff)
      apply auto
    apply (subst (asm) (1 2) input_depth_Read_diff)
        apply auto
      apply (smt (verit, del_insts) DiffI arg_min_natI image_iff insert_iff)
     apply (smt (verit, del_insts) DiffI arg_min_natI image_iff insert_iff)
    apply hypsubst_thin
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply (smt (verit, del_insts) Diff_iff arg_min_natI image_iff insertI1)
    apply auto
    done
  subgoal
    by (force intro!: le_SucI)
  subgoal
    by (force intro!: le_SucI)
  done

lemma inputs_comp_op: "p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow> p \<in> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  apply (induct "input_depth p (comp_op wire buf op1 op2)" arbitrary: buf op1 op2 rule: less_induct)
  subgoal for buf op1 op2
    apply (cases "input_depth p (comp_op wire buf op1 op2)")
    subgoal
      apply simp
      apply (simp add: input_depth_Read)
      apply auto
      apply (cases "\<exists>n. comp_producing wire buf op1 op2 n"; (simp add: not_comp_producing_eq_End)?)
      apply (erule exE)+
      subgoal premises prems for f n
        using prems(3,1-2)
        apply (induct buf op1 op2 n arbitrary: p f rule: comp_producing.induct)
                   apply (auto split: if_splits option.splits)
        done
      done
    subgoal premises prems for n
      unfolding less_Suc_eq_le apply -
      using prems(2-) apply -
      apply (cases op1)
        apply (auto split: if_splits option.splits simp: input_depth_Read_diff)
      subgoal for p1 f1 
        apply (cases op2)
        subgoal for p1' f1'
          apply (auto split: if_splits option.splits simp: input_depth_Read_diff)
          subgoal 
            apply (rule ccontr)
            apply (insert prems(1))
            apply force
            done
          subgoal for y z
            using prems(1) apply -
            apply hypsubst_thin
            apply (rule ccontr)
            apply simp
            apply (subst (asm) input_depth_Read_diff)
              apply fast
             apply auto
            apply (subst (asm) input_depth_Read_diff)
              apply blast
             apply (smt (verit, ccfv_threshold) Diff_iff arg_min_natI image_iff insertI1)
            apply auto
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply force+
            done
          done
        subgoal for op' p' x
          using prems(1)
          apply(force intro: le_SucI simp add: less_Suc_eq_le)
          done
        subgoal
          apply (drule sym)
          apply (insert prems(1))
          apply hypsubst
          apply simp
          apply (subst (asm) (2) input_depth_Read_diff)
            apply fast
           apply force
          apply simp
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (subst less_Suc_eq_le)
           apply (rule order_refl)
          apply (drule meta_mp)
           apply (auto simp add: image_iff)
          done
        done
      subgoal prem for op' p' x
        apply (insert prems(1))
        apply hypsubst_thin
        apply (cases op2)
        subgoal
          apply (drule sym)
          apply hypsubst
          apply (auto split: if_splits option.splits)
          subgoal
            by fastforce
          subgoal
            apply (subst (asm) if_P)
             apply fast
            apply simp
            apply (drule comp_producing_inject, assumption)
            apply hypsubst_thin
            apply (rotate_tac 5)
            apply (drule sym)
            apply (erule comp_producing.cases)
                       apply simp_all
            apply (drule comp_producing_inputs_comp_op)
               apply assumption+
             apply (meson UnCI le_imp_less_Suc)
            apply blast
            done
          subgoal
            apply (subst (asm) if_P)
             apply fast
            apply simp
            apply (drule comp_producing_inject, assumption)
            apply hypsubst_thin
            apply (rotate_tac 5)
            apply (drule sym)
            apply (erule comp_producing.cases)
                       apply simp_all
            apply (drule comp_producing_inputs_comp_op)
               apply assumption+
             apply (meson UnCI le_imp_less_Suc)
            apply blast
            done
          subgoal
            apply (subst (asm) (1) input_depth_Read_diff)
              apply blast+
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply simp
            apply blast
            done
          subgoal
            by force
          done
        subgoal
          by (smt (verit) UnE comp_producing_inputs_comp_op inputs_comp_producing le_imp_less_Suc op.simps(36))
        subgoal
          apply (auto split: option.splits)
           apply fastforce
          apply (smt (z3) UnE UnI1 UnI2 all_not_in_conv comp_producing_inputs_comp_op empty_Diff image_empty inputs_comp_producing le_imp_less_Suc op.simps(37))
          done
        done
      subgoal
        using prems(1) by (metis UnE comp_producing_inputs_comp_op equals0D image_empty inputs_comp_producing less_Suc_eq_le op.simps(37))
      done
    done
  done

lemma inputs_comp_op_le:
  "inputs (comp_op wire buf op1 op2) \<subseteq> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  using inputs_comp_op by blast

section\<open>Outputs of comp_op\<close>


lemma outputs_comp_op_arg_min_1[simp]:
  "p \<in> outputs (comp_op wire buf (f1 x) op) \<Longrightarrow>
   p \<in> outputs (comp_op wire buf (f1 (ARG_MIN (m :: _ \<Rightarrow> nat) x. p \<in> outputs (comp_op wire buf (f1 x) op))) op)"
  by (rule arg_min_natI)

lemma outputs_comp_op_arg_min_2[simp]:
  "p \<in> outputs (comp_op wire buf op (f2 y)) \<Longrightarrow>
   p \<in> outputs (comp_op wire buf op (f2 (ARG_MIN (m :: _ \<Rightarrow> nat) y. p \<in> outputs (comp_op wire buf op (f2 y)))))"
  by (rule arg_min_natI)

lemma outputs_comp_op_arg_min_3[simp]:
  "p \<in> outputs (comp_op wire buf (f1 x) (f2 y)) \<Longrightarrow>
   p \<in> outputs
         (comp_op wire buf
            (f1 (ARG_MIN (m1 :: _ \<Rightarrow> nat) x. (\<exists>xa. p \<in> outputs (comp_op wire buf (f1 x) (f2 xa)))))
            (f2 (ARG_MIN (m2 :: _ \<Rightarrow> nat) x. p \<in> outputs (comp_op wire buf
                            (f1 (ARG_MIN (m1 :: _ \<Rightarrow> nat) x. (\<exists>xa. p \<in> outputs (comp_op wire buf (f1 x) (f2 xa))))) (f2 x)))))"
  by (smt (verit, best) arg_min_natI)

lemma comp_producing_outputs_comp_op:
  fixes op1 :: "('ip1, 'op1, 'd) op" and op2 :: "('ip2, 'op2, 'd) op"
  shows "comp_producing wire buf op1 op2 i \<Longrightarrow>
    p \<in> outputs (comp_op wire buf op1 op2) \<Longrightarrow>
    output_depth p (comp_op wire buf op1 op2) = Suc n \<Longrightarrow>
    (\<And>buf (op1 :: ('ip1, 'op1, 'd) op) (op2 :: ('ip2, 'op2, 'd) op).
        output_depth p (comp_op wire buf op1 op2) \<le> n \<Longrightarrow>
        p \<in> outputs (comp_op wire buf op1 op2) \<Longrightarrow>
         p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2) \<Longrightarrow>
     p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  apply (induct buf op1 op2 i rule: comp_producing.induct)
             apply (auto 7 7 intro: le_SucI split: if_splits option.splits)
  subgoal
    apply (rule ccontr)
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
     apply blast
    apply simp
    apply hypsubst
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
     apply blast
    apply simp
    apply hypsubst
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    apply (rule ccontr) 
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    apply blast
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
     apply blast
    apply simp
    apply hypsubst
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    by blast
  subgoal
    by fastforce
  subgoal
    apply (rule ccontr) 
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    apply blast
    done
  subgoal
    apply (subst (asm) (1 2) output_depth_Read)
      apply (smt (verit) arg_min_natI)
     apply (smt (verit) arg_min_natI)
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
     apply blast+
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
     apply blast
    apply simp
    apply hypsubst
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
      apply blast
     apply blast
    apply simp
    apply (subst (asm)  output_depth_Read)
     apply (smt (verit) arg_min_natI)
    apply (drule sym[of _ n])
    apply simp
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply auto
    done
  subgoal
    by (smt (z3) UN_I arg_min_natI domI dom_const dual_order.refl imageE image_eqI insert_Diff1)
  done

lemma outputs_comp_op: 
  "p \<in> outputs (comp_op wire buf op1 op2) \<Longrightarrow>
   p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  apply (induct "output_depth p (comp_op wire buf op1 op2)" arbitrary: buf op1 op2 rule: less_induct)
  subgoal for buf op1 op2
    apply (cases "output_depth p (comp_op wire buf op1 op2)")
    subgoal
      apply (simp add: input_depth_Write_0)
      apply auto
      apply (cases "\<exists>n. comp_producing wire buf op1 op2 n"; (simp add: not_comp_producing_eq_End)?)
      apply (erule exE)+
      subgoal premises prems for x op' n
        using prems(3,1-2)
        apply (induct buf op1 op2 n arbitrary: p x op' rule: comp_producing.induct)
                   apply (auto split: if_splits option.splits)
        done
      done
    subgoal premises prems for n
      using prems(2-) apply -
      apply (cases op1)
        apply (auto split: if_splits option.splits simp: input_depth_Read_diff)
      subgoal for p1 f1 
        apply (cases op2)
        subgoal for p1' f1'
          apply (auto split: if_splits option.splits)
          subgoal 
            apply (rule ccontr)
            apply (insert prems(1))
            apply simp
            apply (subst (asm) output_depth_Read)
             apply fast
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply (meson arg_min_natI)
            apply blast
            done
          subgoal 
            apply (rule ccontr)
            apply (insert prems(1))
            apply simp
            apply (subst (asm) (2) output_depth_Read)
             apply simp
             apply blast
            apply (subst (asm) (2) output_depth_Read)
             apply simp
             apply (smt (verit, ccfv_SIG) arg_min_natI)
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply simp
            apply blast
            done
          done
        subgoal for op' p' x
          apply (auto split: if_splits option.splits)
          apply (insert prems(1))
          apply simp
          apply (rule ccontr)
          apply (subst (asm) output_depth_Read)
           apply simp
           apply blast
          apply (subst (asm) output_depth_Write_simp_diff)
            apply simp
           apply (smt (verit, ccfv_SIG) arg_min_natI)
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (subst less_Suc_eq_le)
           apply (rule le_SucI)
           apply (rule order_refl)
          apply (drule meta_mp)
           apply simp
          apply blast
          done
        subgoal
          apply (auto split: if_splits option.splits)
          apply (insert prems(1))
          apply simp
          apply (rule ccontr)
          apply (subst (asm) output_depth_Read)
           apply blast
          apply simp
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (subst less_Suc_eq_le)
           apply (rule order_refl)
          apply (drule meta_mp)
           apply (smt (verit) arg_min_natI)
          apply auto
          done
        done
      subgoal for op' p' x
        apply (drule sym)
        apply (cases op2)
        subgoal for p1' f1'
          apply (auto split: if_splits option.splits)
          subgoal
            apply (insert prems(1))
            apply simp
            apply (subst (asm) (2) output_depth_Write_simp_diff)
              apply simp
             apply force
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply (smt (verit) arg_min_natI)
            apply auto
            done
          subgoal
            apply (insert prems(1))
            apply (drule comp_producing_outputs_comp_op[where p=p and n=n])
               apply simp
               apply (subst (asm) if_P)
                apply fast    
               apply fast
              apply force
             apply (metis le_imp_less_Suc prems(3))
            apply auto
            done
          subgoal
            apply (insert prems(1))
            apply (drule comp_producing_outputs_comp_op[where p=p and n=n])
               apply simp
               apply (subst (asm) if_P)
                apply fast    
               apply fast
              apply force
             apply (metis le_imp_less_Suc prems(3))
            apply auto
            done
          subgoal
            apply (cases "p = Inl p'")
             apply simp
            apply (insert prems(1))
            apply simp
            apply (subst (asm) (1 2) output_depth_Write_simp_diff)
                apply force
               apply force
              apply force
             apply fast
            apply (subst (asm) (1 2) output_depth_Read)
              apply blast+
            apply simp
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply auto
            done
          subgoal
            by (smt (z3) UNIV_I Un_iff Union_iff arg_min_natI domI dual_order.refl imageE image_eqI insert_Diff1 le_imp_less_Suc prems(1) prems(3))
          done
        subgoal
          apply (cases op2)
            apply (auto split: if_splits option.splits)
          subgoal 
            apply (cases "p = Inl p'")
             apply simp
            apply (insert prems(1))
            apply (subst (asm) output_depth_Write_simp_diff)
              apply force
             apply blast
            apply (subst (asm) output_depth_Write_simp_diff)
              apply force
             apply blast
            apply simp
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply auto
            done
          subgoal for p''
            apply (insert prems(1))
            apply simp
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply auto
            done
          done
        subgoal
          apply (insert prems(1))
          apply (auto split: option.splits if_splits)
          subgoal
            apply (cases "p = Inl p'")
             apply simp
            apply (subst (asm) (1 2) output_depth_Write_simp_diff)
                apply force
               apply force
              apply fast+            
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply auto
            done   
          subgoal for op'' n'' n'
            apply (subst (asm) if_P)
             apply fast    
            apply simp
            apply (drule comp_producing_outputs_comp_op[where p=p and n=n])
               apply force
              apply force
             apply (metis less_Suc_eq_le prems(1) prems(3))
            apply auto
            done
          done
        done
      subgoal
        by (smt (z3) UnE comp_producing_outputs_comp_op empty_Diff empty_iff image_empty le_imp_less_Suc not_comp_producing_eq_End op.set(6) prems(1))
      done
    done
  done

lemma outputs_comp_op_le:
  "outputs (comp_op wire buf op1 op2) \<subseteq> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  using outputs_comp_op by blast


section\<open>Cleaned comp_op\<close>

lemma comp_producing_cleanedD: "comp_producing wire buf op1 op2 n \<Longrightarrow>
  cleaned op1 \<Longrightarrow>
  cleaned op2 \<Longrightarrow>
  comp_op wire buf op1 op2 = End \<or>
  (\<exists>op' q x. comp_op wire buf op1 op2 = Write op' q x \<and> 
    cleaned_cong (\<lambda>op. \<exists>buf op1 op2. op = comp_op wire buf op1 op2 \<and> cleaned op1 \<and> cleaned op2) op') \<or>
  (\<exists>f p. comp_op wire buf op1 op2 = Read p f \<and> p \<notin> inputs (f EOS) \<and>
   (\<forall>x. cleaned_cong (\<lambda>op. \<exists>buf op1 op2. op = comp_op wire buf op1 op2 \<and> cleaned op1 \<and> cleaned op2) (f x)))"
  by (induct buf op1 op2 n pred: comp_producing)
    (auto 6 0 split: option.splits intro: cc_base intro!: cc_write cc_read dest!: inputs_comp_op)+

lemma cleaned_comp_op: "cleaned op1 \<Longrightarrow> cleaned op2 \<Longrightarrow> cleaned (comp_op wire buf op1 op2)"
  apply (coinduction arbitrary: buf op1 op2 rule: cleaned_coinduct_upto)
  subgoal for buf op1 op2
    apply (cases op1; cases op2)
            apply (auto dest!: inputs_comp_op split: option.splits)
                        apply (rule cc_base, (rule exI conjI refl)+; simp)
                       apply (rule cc_read, blast dest!: inputs_comp_op, rule cc_base, (rule exI conjI refl)+; simp)
                      apply (rule cc_write, rule cc_base, (rule exI conjI refl)+; simp)
                     apply (rule cc_base, (rule exI conjI refl)+; simp)
                    apply (rule cc_base, (rule exI conjI refl)+; simp)
                   apply (rule cc_read, blast dest!: inputs_comp_op, rule cc_base, (rule exI conjI refl)+; simp)
    subgoal for op' q x f p n
      by (frule comp_producing_cleanedD) (auto intro: cleaned.intros(1,2) split: if_splits)
                 apply (rule cc_base, (rule exI conjI refl)+; simp)
                apply (rule cc_base, (rule exI conjI refl)+; simp)
    subgoal for op' q x p f p' n 
      by (frule comp_producing_cleanedD) (auto intro: cleaned.intros(1,2) split: if_splits)
              apply (rule cc_base, (rule exI conjI refl)+; simp)
             apply (rule cc_base, (rule exI conjI refl)+; simp)
            apply (rule cc_write, rule cc_base, (rule exI conjI refl)+; simp)
           apply (rule cc_base, (rule exI conjI refl)+; simp)
          apply (rule cc_base, (rule exI conjI refl)+; simp)
         apply (rule cc_base, (rule exI conjI refl)+; simp)
    subgoal for op' q x p' n 
      by (frule comp_producing_cleanedD) (auto intro: cleaned.intros(1,2) split: if_splits)
    subgoal for p f n 
      by (frule comp_producing_cleanedD) (auto intro: cleaned.intros(1,2) split: if_splits)
      apply (rule cc_base, (rule exI conjI refl)+; simp)
     apply (rule cc_base, (rule exI conjI refl)+; simp)
    apply (rule cc_base, (rule exI conjI refl)+; simp)
    done
  done

section\<open>Trace model correctness\<close>
definition "lfocus f A ios = lmap (map_prod f id) (lfilter (\<lambda>qx. fst qx \<in> A) ios)"

corec lalternate where
  "lalternate ios1 ios2 = (case (ios1, ios2) of
     (LCons io1 ios1', LCons io2 ios2') \<Rightarrow> LCons io1 (LCons io2 (lalternate ios1' ios2'))
   | (_, LNil) \<Rightarrow> ios1
   | (LNil, _) \<Rightarrow> ios2)"

simps_of_case lalternate_simps[simp]: lalternate.code[unfolded prod.case]

term case_IO

abbreviation visible_IO where "visible_IO wire io \<equiv> case_IO (\<lambda>p _. case_sum (\<lambda> _. True) (\<lambda> q. q \<notin> ran wire) p) (\<lambda> p _. case_sum (\<lambda> q. q \<notin> dom wire) (\<lambda> _. True) p) io" 

coinductive causal for wire where
  "causal wire (BTL p buf) ios1 ios2 \<Longrightarrow> y = BHD p buf \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal wire buf (LCons (Inp q x) ios1) (LCons (Inp p y) ios2)"
| "causal wire buf ios1 ios2 \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal wire buf (LCons (Inp q x) ios1) (LCons (Inp p y) ios2)"
| "causal wire buf ios1 ios2 \<Longrightarrow> causal wire buf (LCons (Inp q x) ios1) (LCons (Out p y) ios2)"
| "causal wire (BTL p (BENQ p' x buf)) ios1 ios2 \<Longrightarrow> y = BHD p (BENQ p' x buf) \<Longrightarrow> wire q = Some p' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
| "causal wire (BENQ p' x buf) ios1 ios2 \<Longrightarrow> wire q = Some p' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
| "causal wire buf ios1 ios2 \<Longrightarrow> wire q = None \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
| "causal wire (BTL p buf) ios1 ios2 \<Longrightarrow> wire q = None \<Longrightarrow> y = BHD p buf \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
| "causal wire buf ios1 ios2 \<Longrightarrow> wire q = None \<Longrightarrow> causal wire buf (LCons (Out q x) ios1) (LCons (Out p y) ios2)"
| "causal wire (BENQ p' x buf) ios1 ios2 \<Longrightarrow> wire q = Some p' \<Longrightarrow> causal wire buf (LCons (Out q x) ios1) (LCons (Out p y) ios2)"
| "causal wire buf ios1 LNil"
| "causal wire (BTL p (bend o buf)) LNil ios2 \<Longrightarrow> y = BHD p (bend o buf) \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal wire buf LNil (LCons (Inp p y) ios2)"
| "causal wire (bend o buf) LNil ios2 \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal wire buf LNil (LCons (Inp p y) ios2)"
| "causal wire (bend o buf) LNil ios2 \<Longrightarrow> causal wire buf LNil (LCons (Out p y) ios2)"

inductive_cases causal_InpInpE[elim!]: "causal wire buf (LCons (Inp q x) ios1) (LCons (Inp p y) ios2)"
inductive_cases causal_InpOutE[elim!]: "causal wire buf (LCons (Inp q x) ios1) (LCons (Out p y) ios2)"
inductive_cases causal_OutOutE[elim!]: "causal wire buf (LCons (Out q x) ios1) (LCons (Out p y) ios2)"
inductive_cases causal_OutInpE[elim!]: "causal wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
inductive_cases causal_LNilInpE[elim!]: "causal wire buf LNil (LCons (Inp p y) ios2)"
inductive_cases causal_LNilOutE[elim!]: "causal wire buf LNil (LCons (Out p y) ios2)"
inductive_cases causal_LNil[elim!]: "causal wire buf ios1 LNil"

lemma causal_buf_cong:
  "causal wire buf' ios1 ios2 \<Longrightarrow> (\<forall> p \<in> ran wire. buf' p = buf p) \<Longrightarrow> causal wire buf ios1 ios2"
  apply (coinduction arbitrary: buf buf' ios1 ios2)
  subgoal for buf buf' ios1 ios2
    apply (erule causal.cases)
                apply auto
    done
  done

lemma fun_upd_Inl[simp]:
  "(m \<circ> Inl)(p := n) = m(Inl p := n) \<circ> Inl"
  "m(Inr p' := n) \<circ> Inl = m \<circ> Inl"
  by auto

lemma not_EOB[simp]:
  "(x \<noteq> EOB) = (x = EOS \<or> (\<exists> ob. x = Observed ob))"
  apply (cases x)
    apply auto
  done 

lemma lalternate_LNil[simp]:
  "lalternate LNil ios = ios"
  "lalternate ios LNil = ios"
   apply (cases ios; auto)+
  done

lemma lalternate_LCons1:
  "lalternate (LCons io ios1) ios2 = LCons io (lalternate ios2 ios1)"
  apply (coinduction arbitrary: io ios1 ios2 rule: llist.coinduct_upto)
  subgoal for io ios1 ios2
    apply (intro impI context_conjI)
      apply (cases ios2)
       apply auto[2]
     apply (cases ios2)
      apply auto[2]
    apply (cases ios1; cases ios2)
       apply (auto intro: llist.cong_intros)
    apply (metis (mono_tags, lifting) llist.cong_LCons llist.cong_base)
    done
  done

lemma lset_lalternate1:
  "x \<in> lset (lalternate ios1 ios2) \<Longrightarrow>
   x \<in> lset ios1 \<union> lset ios2"
  apply (induct "lalternate ios1 ios2" arbitrary: ios1 ios2 rule: lset_induct)
  subgoal for xs ios1 ios2 
    apply (cases ios1; cases ios2)
       apply auto
    done
  subgoal for x' xs ios1 ios2
    apply (cases ios1; cases ios2)
       apply (simp split: llist.splits)
      apply auto
    apply hypsubst_thin
    using lalternate_LCons1 
    by (metis insert_iff llist.set(2))
  done

lemma lset_lalternate2:
  "x \<in> lset ios1 \<Longrightarrow>
   x \<in> lset (lalternate ios1 ios2)"
  apply (induct "ios1" arbitrary: ios2 rule: lset_induct)
   apply (auto simp add: lalternate_LCons1)
  subgoal for x' xs ios2
    apply (cases ios2)
     apply (auto simp add: lalternate_LCons1 split: llist.splits)
    done
  done

lemma lset_lalternate3:
  "x \<in> lset ios2 \<Longrightarrow>
   x \<in> lset (lalternate ios1 ios2)"
  apply (induct "ios2" arbitrary: ios1 rule: lset_induct)
  subgoal for xs ios1
    apply (cases ios1)
     apply auto
    done
  subgoal for x' xs ios1
    apply (cases ios1)
     apply (auto simp add: lalternate_LCons1 split: llist.splits)
    done
  done

lemma lset_lalternate:
  "lset (lalternate ios1 ios2) = lset ios1 \<union> lset ios2"
  by (auto dest: lset_lalternate1 lset_lalternate2 lset_lalternate3)

lemma lset_ios1_comp_op_End_not_visible:
  "x \<in> lset ios1 \<Longrightarrow>
   comp_op wire buf op1 op2 = End \<Longrightarrow>
   traced op1 ios1 \<Longrightarrow>
   traced op2 ios2 \<Longrightarrow>
   causal wire buf ios1 ios2 \<Longrightarrow>
   \<not> visible_IO wire (map_IO Inl Inl id x)"
  apply (induct ios1 arbitrary: ios2 buf op1 op2 rule: lset_induct)
  subgoal for xs ios2 buf op1 op2
    apply (cases op1; cases op2)
            apply (auto split: if_splits option.splits)+
    done
  subgoal for x' xs ios2 buf op1 op2
    apply (cases op1; cases op2)
            apply (auto split: if_splits option.splits)
    subgoal by blast
    subgoal by blast
    subgoal by blast
    subgoal by blast
    subgoal by blast
    subgoal by blast
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal using End causal.intros(10) by metis
    subgoal by (meson End causal.intros(10) comp_producing.intros(4) not_comp_producing_eq_End)
    done
  done

lemma lset_ios2_comp_op_End_not_visible:
  "x \<in> lset ios2 \<Longrightarrow>
   causal wire buf ios1 ios2 \<Longrightarrow>
   comp_op wire buf op1 op2 = End \<Longrightarrow>
   traced op1 ios1 \<Longrightarrow>
   traced op2 ios2 \<Longrightarrow>
   \<not> visible_IO wire ((map_IO Inr Inr id) x)"
  apply (induct ios2 arbitrary: ios1 buf op1 op2 rule: lset_induct)
  subgoal for xs ios1 buf op1 op2
    apply (cases op1; cases op2)
            apply (auto split: if_splits option.splits dest: not_comp_producing_eq_End)+
    done
  subgoal for x' xs ios1 buf op1 op2
    apply (cases op1; cases op2)
            apply (auto split: if_splits option.splits dest: not_comp_producing_eq_End intro: comp_producing.intros traced.intros)
    subgoal
      by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd)
    subgoal
      by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd)
    subgoal
      by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd)
    subgoal
      by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd)
    subgoal
      by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd)
    subgoal
      by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal
      using End by metis
      subgoal
      using End by metis
    subgoal
      using End by metis
    subgoal
      by (metis (mono_tags, opaque_lifting) End comp_eq_dest_lhs comp_producing.intros(9) not_comp_producing_eq_End)
    subgoal   
      by (metis (mono_tags, opaque_lifting) End comp_eq_dest_lhs comp_producing.intros(9) not_comp_producing_eq_End)
    subgoal
      by (metis bend.simps(1) bend_bend bhd.elims bhd.simps(2) comp_apply observation.distinct(1) observation.distinct(5)) 
    done
  done


lemma comp_producing_traced_cong_causalD:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   traced op1 ios1 \<Longrightarrow>
   traced op2 ios2 \<Longrightarrow>
   causal wire buf ios1 ios2 \<Longrightarrow>
   comp_op wire buf op1 op2 = End \<and> lfilter (visible_IO wire) (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) = LNil \<or>
   (\<exists>op' q x lxs. comp_op wire buf op1 op2 = Write op' q x \<and>
      lfilter (visible_IO wire) (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) = LCons (Out q x) lxs \<and>
      traced_cong (\<lambda>op lxs.
         \<exists>ios1 ios2 op1 op2 buf.
            op = comp_op wire buf op1 op2 \<and>
            traced op1 ios1 \<and>
            traced op2 ios2 \<and>
            lxs = lfilter (visible_IO wire) (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) \<and>
            causal wire buf ios1 ios2) op' lxs) \<or>
   (\<exists>f p x lxs n. comp_op wire buf op1 op2 = Read p f \<and>
      lfilter (visible_IO wire) (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) = LCons (Inp p x) lxs \<and>
            traced_cong (\<lambda>op lxs.
            \<exists>ios1 ios2 op1 op2 buf.
            op = comp_op wire buf op1 op2 \<and>
            traced op1 ios1 \<and>
            traced op2 ios2 \<and>
            lxs = lfilter (visible_IO wire) (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) \<and>
            causal wire buf ios1 ios2) (f x) lxs)"
  apply (induct buf op1 op2 n arbitrary: ios1 ios2 pred: comp_producing)
  subgoal by auto
  subgoal for buf p1 f1 ios1 ios2
    apply (erule causal.cases)
                apply auto
    subgoal for lxs
      by (auto 10 10 intro!: tc_base End causal.intros(10))
    subgoal for lxs
      by (auto 10 10 intro!: tc_base End causal.intros(10))
    subgoal for lxs
      by (auto 10 10 intro!: tc_base End causal.intros(10))
    done
  subgoal for buf p1 f1 ios1 ios2
    apply (erule causal.cases)
                apply (auto 10 10 intro!: tc_base End causal.intros(10))
    done
  subgoal
    apply (erule causal.cases)
                apply (auto simp add: lmap_eq_LNil split: if_splits intro: End causal.intros(10) comp_producing.intros(4))
    subgoal for lxs x
      by (smt (verit) End causal.intros(10) lalternate_LNil(2) lmap_eq_LNil)
    subgoal for lxs x
      by (smt (verit) End causal.intros(10) lalternate_LNil(2) lmap_eq_LNil)
    done
  subgoal
    by (auto 10 10 intro!: tc_base End)
  subgoal
    apply (erule causal.cases)
                apply auto
    subgoal for lxs lxsa
      by (force intro!: tc_base tc_write)
    subgoal for lxs  lxsa
      by (force intro!: tc_base tc_write)
    subgoal for lxs lxsa
      by (force intro!: tc_base tc_write)
    done
  subgoal
    apply (erule causal.cases)
                apply auto
    subgoal
      by (smt (z3) Compl_iff tc_base tc_write)
    subgoal
      by (smt (z3) Compl_iff tc_base tc_write)
    done
  subgoal
    apply (erule causal.cases)
                apply auto
    subgoal for lxs
      by (auto 10 10 intro!: End tc_base)
    subgoal for lxs
      by (auto 10 10 intro!: End tc_base)
    subgoal for lxs
      by (auto 10 10 intro!: End tc_base)
    done
  subgoal for p2 buf f2 ios1 ios2
    apply (erule causal.cases; hypsubst_thin)
                apply simp_all
                apply auto[10]
    subgoal for p ios2
      apply (erule traced_ReadE)
       apply simp_all
       apply (elim disjE)
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply blast
        apply auto
           apply (metis (mono_tags, opaque_lifting) comp_eq_dest_lhs comp_producing.intros(9))+
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply blast
        apply auto
           apply (metis (mono_tags, opaque_lifting) comp_eq_dest_lhs comp_producing.intros(9))+
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         defer
         apply (drule meta_mp)
          apply (rule causal.intros(10))
         apply auto
          apply (metis bend.simps(1) bend_bend bhd.elims bhd.simps(2) comp_apply observation.distinct(5) observation.simps(3))+
        done
      done
    subgoal for ios2 p y
      apply (erule traced_ReadE)
       apply simp_all
      done
    subgoal for ios2 p y
      apply (erule traced_ReadE)
       apply simp_all
      done
    done
  subgoal for buf p1 f1 p2 f2 ios1 ios2
    apply (erule causal.cases)
                apply auto
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      apply (rule tc_read)
       apply simp
      apply (auto 10 10 intro!: tc_base)
      done
    subgoal
      apply (rule tc_read)
       apply simp
      apply (auto 10 10 intro!: tc_base)
      done
    subgoal
      apply (rule tc_read)
       apply simp
      apply (auto 10 10 intro!: tc_base)
      done
    subgoal
      apply (rule tc_read)
       apply simp
      apply (auto 10 10 intro!: tc_base)
      done
    subgoal
      apply (rule tc_readEOB)
      apply (auto 10 10 intro!: tc_base)
      done
    subgoal
      apply (rule tc_readEOB)
      apply (auto 10 10 intro!: tc_base)
      done
    subgoal
      apply (rule tc_read)
       apply simp
      apply (auto 10 10 intro!: tc_base)
      done
    subgoal
      apply (rule tc_read)
       apply simp
      apply (auto 10 10 intro!: tc_base)
      done
    subgoal
      apply (rule tc_readEOB)
      apply (auto 10 10 intro!: tc_base)
      done
    done
  subgoal for buf p1 f1 p2 f2 ios1 ios2
    apply (erule causal.cases)
                apply auto
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal
      unfolding not_def
      apply (rotate_tac 7)
      apply (drule mp)
       apply (rule tc_read)
        apply simp
       apply (rule tc_base)
       apply (intro exI conjI)
            apply auto
      done
    subgoal for n
      unfolding not_def
      apply (rotate_tac 7)
      apply (drule mp)
       apply (rule tc_read)
        apply simp
       apply (rule tc_base)
       apply (intro exI conjI)
            apply auto
      done
    subgoal for n
      unfolding not_def
      apply (rotate_tac 7)
      apply (drule mp)
       apply (rule tc_read)
        apply simp
       apply (rule tc_base)
       apply (intro exI conjI)
            apply auto
      done
    subgoal for n
      unfolding not_def
      apply (rotate_tac 7)
      apply (drule mp)
       apply (rule tc_read)
        apply simp
       apply (rule tc_base)
       apply (intro exI conjI)
            apply auto
      done
    subgoal for n
      unfolding not_def
      apply (rotate_tac 7)
      apply (drule mp)
       apply (rule tc_readEOB)
       apply simp
       apply (rule tc_base)
       apply (intro exI conjI)
            apply auto
      done
    subgoal
      unfolding not_def
      apply (rotate_tac 7)
      apply (drule mp)
       apply (rule tc_readEOB)
       apply simp
       apply (rule tc_base)
       apply (intro exI conjI)
            apply auto
      done
    subgoal
      by (auto 10 10 intro!: tc_base)
    subgoal for n
      by (auto 10 10 intro!: tc_base)
    subgoal for n
      by (auto 10 10 intro!: tc_base)
    done
  subgoal for p2 p1 p x1 buf op1' f2 n ios1 ios2
    apply (erule causal.cases)
                apply simp_all
    subgoal for n
      by (auto 10 10 intro!: tc_base)
    subgoal for n
      by (auto 10 10 intro!: tc_base)
    subgoal for n
      by (auto 10 10 intro!: tc_base)
    subgoal for n
      apply hypsubst_thin
      apply (elim traced_ReadE traced_WriteE)
       apply (simp_all split: if_splits)
         apply (elim disjE)
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply auto
           apply (smt (verit) comp_producing.intros(12) fun_upd_apply fun_upd_upd)+
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply auto
           apply (smt (verit) comp_producing.intros(12) fun_upd_apply fun_upd_upd)+
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply auto
               apply (smt (verit) comp_producing.intros(12) fun_upd_apply fun_upd_upd)+
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply auto
           apply (smt (verit) comp_producing.intros(12) fun_upd_apply fun_upd_upd)+
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply auto
           apply (smt (verit) comp_producing.intros(12) fun_upd_apply fun_upd_upd)+
        done
      done
            apply auto
    done
  done

declare [[unify_search_bound = 100]]

corec retrace_comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow> ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> 'd observation llist \<Rightarrow> 'd observation llist \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) IO llist" where
  "retrace_comp_op wire buf op1 op2 inps1 inps2 = (
     case (op1, op2) of
     (End, End) \<Rightarrow> LNil
   | (End, Write op2' p2 x2) \<Rightarrow> LCons (Out (Inr p2) x2) (retrace_comp_op wire (bend o buf) End op2' inps1 inps2)
   | (End, Read p2 f2) \<Rightarrow> let buf' = bend o buf in if p2 \<in> ran wire
     then LCons (Inp (Inr p2) (BHD p2 buf')) (retrace_comp_op wire (BTL p2 buf') End (f2 (BHD p2 buf')) inps1 inps2)
     else LCons (Inp (Inr p2) (lhd inps2)) (retrace_comp_op wire buf' End (f2 (lhd inps2)) inps1 (ltl inps2))
   | (Read p1 f1, End) \<Rightarrow> LCons (Inp (Inl p1) (lhd inps1)) (retrace_comp_op wire buf (f1 (lhd inps1)) End (ltl inps1) inps2)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> LCons (Inp (Inl p1) (lhd inps1)) (LCons (Out (Inr p2) x2) (retrace_comp_op wire buf (f1 (lhd inps1)) op2' (ltl inps1) inps2))
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then LCons (Inp (Inl p1) (lhd inps1)) (LCons (Inp (Inr p2) (BHD p2 buf)) (retrace_comp_op wire (BTL p2 buf) (f1 (lhd inps1)) (f2 (BHD p2 buf)) (ltl inps1) inps2))
     else LCons (Inp (Inl p1) (lhd inps1)) (LCons (Inp (Inr p2) (lhd inps2)) (retrace_comp_op wire buf (f1 (lhd inps1)) (f2 (lhd inps2)) (ltl inps1) (ltl inps2)))
   | (Write op1' p1 x1, End) \<Rightarrow> LCons (Out (Inl p1) x1) (retrace_comp_op wire buf op1' End inps1 inps2)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> LCons (Out (Inl p1) x1) (LCons (Out (Inr p2) x2) (retrace_comp_op wire buf op1' op2' inps1 inps2))
     | Some p \<Rightarrow> LCons (Out (Inl p1) x1) (LCons (Out (Inr p2) x2) (retrace_comp_op wire (BENQ p x1 buf) op1' op2' inps1 inps2)))
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> LCons (Out (Inl p1) x1) (LCons (Inp (Inr p2) (BHD p2 buf)) (retrace_comp_op wire (BTL p2 buf) op1' (f2 (BHD p2 buf)) inps1 inps2))
     | Some p \<Rightarrow> LCons (Out (Inl p1) x1) (LCons (Inp (Inr p2) (BHD p2 (BENQ p x1 buf))) (retrace_comp_op wire (BTL p2 (BENQ p x1 buf)) op1' (f2 (BHD p2 (BENQ p x1 buf))) inps1 inps2)))
     else (case wire p1 of
       None \<Rightarrow> LCons (Out (Inl p1) x1) (LCons (Inp (Inr p2) (lhd inps2)) (retrace_comp_op wire buf op1' (f2 (lhd inps2)) inps1 (ltl inps2)))
     | Some p \<Rightarrow> LCons (Out (Inl p1) x1) (LCons (Inp (Inr p2) (lhd inps2)) (retrace_comp_op wire (BENQ p x1 buf) op1' (f2 (lhd inps2)) inps1 (ltl inps2)))))"

simps_of_case retrace_comp_op_simps[simp]: retrace_comp_op.code[unfolded prod.case]

term case_observation

abbreviation "Inp_Inl_llist (ios:: ('a + 'b, 'c + 'd, 'e) IO llist) \<equiv>
  lmap (case_IO (case_sum (\<lambda> _ ob. ob) undefined) undefined) (lfilter (case_IO (case_sum \<top> \<bottom>) \<bottom>) ios)"
abbreviation "Inp_Inr_llist ios \<equiv> lmap (case_IO (case_sum undefined (\<lambda> _ ob. ob)) undefined) (lfilter (case_IO (case_sum \<bottom> \<top>) \<bottom>) ios)"

abbreviation "retrace_comp_op_ios wire buf op1 op2 (ios::('a + 'b, 'c + 'd, 'e) IO llist) \<equiv> 
  retrace_comp_op wire buf op1 op2 (Inp_Inl_llist ios) (Inp_Inr_llist ios)"

abbreviation "Inl_llist ios \<equiv>
  lmap (case_IO (case_sum (\<lambda> p ob. Inp p ob) undefined) (case_sum (\<lambda> p ob. Out p ob) undefined)) (lfilter (case_IO (case_sum \<top> \<bottom>) (case_sum \<top> \<bottom>)) ios)"

abbreviation "Inr_llist ios \<equiv>
  lmap (case_IO (case_sum undefined (\<lambda> p ob. Inp p ob)) (case_sum undefined (\<lambda> p ob. Out p ob))) (lfilter (case_IO (case_sum \<bottom> \<top>) (case_sum \<bottom> \<top>)) ios)"

lemma in_retrace_comp_op_End_not_Inl:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = retrace_comp_op wire buf End op2 ios1 ios2 \<Longrightarrow>
   case_IO (case_sum \<bottom> \<top>) (case_sum \<bottom> \<top>) x"
  apply (induct lxs arbitrary: buf op2 ios1 ios2 rule: lset_induct)
  subgoal for xs buf op2 ios1
    apply (cases op2)
    apply (auto simp add: Let_def split: if_splits IO.splits sum.splits)
    done
  subgoal for x' xs buf op2 ios1 ios2
          apply (cases op2; hypsubst)
      apply (simp_all add: Let_def split: if_splits)
    done
  done

lemma traced_comp_op_traced_1:
  "traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
  \<exists>ios1. traced op1 ios1"
  apply (rule exI[of _ "Inl_llist (retrace_comp_op_ios wire buf op1 op2 ios)"])
  apply (coinduction arbitrary: op1 op2 buf ios)
  subgoal for op1 op2 buf ios
    apply (cases op1; cases op2)
    subgoal
      by (force split: sum.splits if_splits if_splits observation.splits)
    subgoal for p f op p' x
      by (force split: sum.splits if_splits if_splits observation.splits)
    subgoal for p f
      by (auto 10 10 split: sum.splits if_splits if_splits observation.splits)
    subgoal for op p x p' f
      apply hypsubst_thin
      apply (simp split: if_splits option.splits)
      subgoal
        by force
      subgoal
        by force
      subgoal
        by force
      subgoal
        apply (intro impI allI conjI disjI1 exI; hypsubst_thin)
             apply simp
           apply (metis comp_producing.intros(12) fun_upd_same fun_upd_upd not_comp_producing_eq_End)
          apply simp
        apply (smt (verit, ccfv_threshold) comp_producing.intros(12) fun_upd_other not_comp_producing_eq_End)
        done
      subgoal
        apply auto
        subgoal
          apply (intro conjI exI disjI1)
            apply auto
          done
        subgoal
          apply (intro conjI exI disjI1)
            apply auto
          done
        subgoal
          apply (intro conjI exI disjI1)
            apply auto
          done
        done
      subgoal
        apply auto
        subgoal
          apply (intro conjI exI disjI1)
            apply auto
          done
        subgoal
          apply (intro conjI exI disjI1)
            apply auto
          done
        subgoal
          apply (intro conjI exI disjI1)
            apply auto
          done
        done
      done
    subgoal
      by (auto 10 10 split: option.splits sum.splits if_splits if_splits observation.splits)
    subgoal
      apply hypsubst_thin
      apply (simp split: option.splits if_splits)
      subgoal
        by force
      subgoal
        by force
      subgoal
       apply (intro impI allI conjI disjI1 exI)
             apply simp
        apply (metis comp_producing.intros(4) not_comp_producing_eq_End)
        done
      done
    subgoal for p f
      apply hypsubst_thin
      apply (intro disjI2)
      apply (auto simp add: lmap_eq_LNil lfilter_eq_LNil split: if_splits IO.splits sum.splits dest: in_retrace_comp_op_End_not_Inl)
      done
    subgoal 
      apply hypsubst_thin
      apply (intro disjI2)
      apply (auto simp add: lmap_eq_LNil lfilter_eq_LNil split: if_splits IO.splits sum.splits dest: in_retrace_comp_op_End_not_Inl)
      done
    subgoal
      apply simp
      done
    done
  done

lemma traced_comp_op_traced_1:
  "traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
  \<exists>ios2. traced op2 ios2"
  apply (rule exI[of _ "Inr_llist (retrace_comp_op_ios wire buf op1 op2 ios)"])
  apply simp
  apply (coinduction arbitrary: op1 op2 buf ios)
  subgoal for op1 op2 buf ios
    apply (cases op1; cases op2)
    subgoal for p f p' f'
      apply hypsubst_thin
      apply (clarsimp split: sum.splits if_splits if_splits observation.splits elim!: chd.elims)
      subgoal
        apply (cases "BHD p' buf")
          apply simp_all
              oops


lemma traced_comp_op:
  "traced (comp_op wire buf op1 op2) ios =
  (\<exists>ios1 ios2. traced op1 ios1 \<and> traced op2 ios2 \<and> (\<forall> p \<in> (- ran wire). m' p = (m o Inr) p) \<and>
    ios = lfilter (visible_IO wire) (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) \<and>
    causal wire buf ios1 ios2)"
  apply (rule iffI)
  subgoal sorry
  subgoal
    apply (elim exE conjE)
    subgoal for ios1 ios2
      apply (coinduction arbitrary: ios ios1 ios2 op1 op2 buf rule: traced_coinduct_upto)
      subgoal for ios ios1 ios2 op1 op2 buf
        apply (cases op1; cases op2)
                apply simp_all
                apply (intro conjI impI)
        subgoal for p f p' f'
          apply (elim traced_ReadE)
          subgoal for x lxs x' lxsa
            apply (simp_all split: if_splits observation.splits)
            apply (elim disjE conjE exE)
               apply (simp_all split: if_splits observation.splits)
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            done
          subgoal for x lxs x' 
            apply (simp_all split: if_splits observation.splits)
            apply (elim disjE conjE exE)
             apply (simp_all split: if_splits observation.splits)
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            done
          subgoal for x lxs x'
            apply (simp_all split: if_splits observation.splits)
            apply (elim disjE conjE exE)
             apply (simp_all split: if_splits observation.splits)
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            done
          subgoal 
            apply (simp_all split: if_splits observation.splits)
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            done
          done
        subgoal for p f p' f'
          apply (elim traced_ReadE)
             apply (simp_all split: if_splits)
             apply (elim disjE conjE exE)
                apply (simp_all split: if_splits)
          subgoal
            apply (rule tc_read)
             apply simp_all
            apply (rule tc_read tc_base exI conjI; (rule refl | assumption)?)+
             apply auto
            done
          subgoal
            apply (rule tc_read)
             apply simp_all
            apply (rule tc_read tc_base exI conjI; (rule refl | assumption)?)+
             apply auto
            done
          subgoal
            apply (rule tc_read)
             apply simp_all
            apply (rule tc_read tc_base exI conjI; (rule refl | assumption)?)+
             apply auto
            done
          subgoal
            apply (rule tc_read)
             apply simp_all
            apply (rule tc_read tc_base exI conjI; (rule refl | assumption)?)+
             apply auto
            done
          subgoal
            apply hypsubst_thin
            apply (elim disjE conjE exE)
             apply simp_all
            subgoal
              apply (rule tc_readEOB)
              apply simp_all
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            subgoal
              apply (rule tc_readEOB)
              apply simp_all
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            done
          subgoal
            apply hypsubst_thin
            apply (elim disjE conjE exE)
             apply simp_all
            subgoal
              apply (rule tc_read)
               apply simp_all
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            subgoal
              apply (rule tc_read)
               apply simp_all
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            done
          subgoal
            apply hypsubst_thin
            subgoal
              apply (rule tc_readEOB)
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply auto
              done
            done
          done
        subgoal for p f p' f'
          apply (elim traced_ReadE traced_WriteE)
           apply (simp_all split: if_splits)
           apply (elim disjE conjE exE)
            apply (simp_all split: if_splits)
          subgoal
            apply (rule tc_write)
            apply simp_all
            apply (rule tc_base exI conjI; (rule refl | assumption)?)+
             apply auto
            done
          subgoal
            apply (rule tc_write)
            apply simp_all
            apply (rule tc_base exI conjI; (rule refl | assumption)?)+
             apply auto
            done
          subgoal
            apply (rule tc_write)
            apply (rule tc_base exI conjI; (rule refl | assumption)?)+
             apply auto
            done
          done
        subgoal
          apply (elim traced_EndE traced_ReadE)
           apply (simp_all split: if_splits)
           apply (elim disjE conjE exE)
            apply (simp_all split: if_splits)
          subgoal
            apply (intro exI conjI tc_base refl)
                 apply (rule refl)
                apply blast+
               apply (rule End)
              defer
              defer
            using causal.intros(10)
             apply (auto split: llist.splits)
            done
          subgoal
            apply (intro exI conjI tc_base refl)
                 apply (rule refl)
                apply blast+
               apply (rule End)
              defer
              defer
            using causal.intros(10)
             apply (auto split: llist.splits)
            done
          subgoal
            apply (intro exI conjI tc_base refl)
                 apply (rule refl)
                apply blast+
               apply (rule End)
              defer
              defer
            using causal.intros(10)
             apply (auto split: llist.splits)
            done
          done
        subgoal for op' p x p' f
          apply (elim traced_WriteE traced_ReadE)
           apply (simp_all split: if_splits)
                 apply (elim disjE conjE exE)
                  apply (simp_all split: if_splits option.splits)
          subgoal
            apply hypsubst_thin
            apply (elim causal_OutInpE)
               apply (simp_all split: if_splits)
             apply blast
            apply (rule tc_read)
             apply simp
            apply (rule tc_base exI conjI; (rule refl | assumption)?)+
            done
          subgoal
            apply hypsubst_thin
            apply (elim causal_OutInpE)
               apply (simp_all split: if_splits)
             apply blast
            apply (rule tc_read)
             apply simp
            apply (rule tc_base exI conjI; (rule refl | assumption)?)+
            done
          subgoal
            apply hypsubst_thin
            apply (elim causal_OutInpE)
               apply (simp_all split: if_splits)
              apply blast+
            apply (rule tc_base exI conjI; (rule refl | assumption)?)+
            done
          subgoal
            apply hypsubst_thin
            apply (elim causal_OutInpE)
               apply (simp_all split: if_splits)
             apply (elim exE disjE)
              apply simp_all
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
              done
            subgoal
              by force
            done
          subgoal for ios1 xa ios2
            apply (elim causal_OutInpE disjE exE)
                   apply (simp_all split: if_splits)
            subgoal for p''
              apply (cases "Ex (comp_producing wire buf (Write op' p x) (Read p' f))")
              subgoal
                apply simp
                apply (elim exE)
                apply (drule comp_producing_traced_cong_causalD)
                    apply (rule Write)
                    apply assumption
                   apply (rule Read)
                    apply simp
                    apply blast
                   apply simp
                  apply (metis causal.intros(4) fun_upd_same fun_upd_upd)
                 apply simp
                apply (elim exE disjE conjE)
                  apply (simp_all add: lfilter_eq_LNil split: if_splits)
                subgoal
                  apply auto
                  by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
                subgoal
                  by blast
                subgoal
                  apply auto
                  using not_EOB apply blast+
                  done
                done
              subgoal 
                apply (auto simp add: lfilter_eq_LNil lset_lalternate)
                subgoal
                  apply hypsubst_thin
                  apply (drule lset_ios1_comp_op_End_not_visible)
                      apply (rule not_comp_producing_eq_End)
                      prefer 4
                      apply assumption
                     defer
                     apply assumption+
                   apply blast
                  defer
                  apply (metis comp_producing.intros(12) fun_upd_same fun_upd_upd)
                  done
                subgoal
                  apply hypsubst_thin
                  apply (drule lset_ios2_comp_op_End_not_visible)
                      apply assumption
                     apply (rule not_comp_producing_eq_End)
                     prefer 4
                     apply blast
                    defer
                    apply assumption+
                  apply (metis comp_producing.intros(12) fun_upd_same fun_upd_upd)
                  done
                done
              done
            subgoal for p''
              apply (intro allI impI)
              subgoal for p'''
                apply (cases "p' = p'''")
                 apply simp_all
                apply (cases "p'' = p'''")
                 apply simp_all
                apply (cases "Ex (comp_producing wire buf (Write op' p x) (Read p' f))")
                subgoal
                  apply simp
                  apply (elim exE)
                  apply (drule comp_producing_traced_cong_causalD)
                      apply (rule Write)
                      apply assumption
                     apply (rule Read)
                      apply simp
                      apply blast
                     apply simp
                    apply (smt (verit, best) causal.intros(4) fun_upd_other)
                   apply simp
                  apply (elim exE disjE conjE)
                    apply (simp_all add: lfilter_eq_LNil split: if_splits)
                  subgoal
                    apply auto
                    by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
                  subgoal
                    by blast
                  subgoal
                    apply auto
                    using not_EOB apply blast+
                    done
                  done
                subgoal 
                  apply (auto simp add: lfilter_eq_LNil lset_lalternate)
                  subgoal
                    apply hypsubst_thin
                    apply (drule lset_ios1_comp_op_End_not_visible)
                        apply (rule not_comp_producing_eq_End)
                        prefer 4
                        apply assumption
                       defer
                       apply assumption+
                     apply blast
                    apply (smt (verit, best) comp_producing.intros(12) fun_upd_other)
                    done
                  subgoal
                    apply hypsubst_thin
                    apply (drule lset_ios2_comp_op_End_not_visible)
                        apply assumption
                       apply (rule not_comp_producing_eq_End)
                       prefer 4
                       apply blast
                      defer
                      apply assumption+
                    apply (smt (verit, best) comp_producing.intros(12) fun_upd_other)
                    done
                  done
                done
              done
            subgoal for p''
              apply (cases "Ex (comp_producing wire buf (Write op' p x) (Read p' f))")
              subgoal
                apply simp
                apply (elim exE)
                apply (drule comp_producing_traced_cong_causalD)
                    apply (rule Write)
                    apply assumption
                   apply (rule Read)
                    defer
                    apply simp
                   apply (metis causal.intros(4) fun_upd_same fun_upd_upd)
                 defer
                 apply force
                apply (elim exE disjE conjE)
                  apply (simp_all add: lfilter_eq_LNil split: if_splits)
                subgoal
                  apply auto
                  by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
                subgoal
                  by blast
                subgoal
                  apply auto
                  using not_EOB apply blast+
                  done
                done
              subgoal 
                apply (auto simp add: lfilter_eq_LNil lset_lalternate)
                subgoal
                  apply hypsubst_thin
                  apply (drule lset_ios1_comp_op_End_not_visible)
                      apply (rule not_comp_producing_eq_End)
                      prefer 4
                      apply assumption
                     defer
                     apply assumption+
                   apply blast
                  apply (metis comp_producing.intros(12) fun_upd_same fun_upd_upd)
                  done
                subgoal
                  apply hypsubst_thin
                  apply (drule lset_ios2_comp_op_End_not_visible)
                      apply assumption
                     apply (rule not_comp_producing_eq_End)
                     prefer 4
                     apply blast
                    defer
                    apply assumption+
                  apply (metis comp_producing.intros(12) fun_upd_same fun_upd_upd)
                  done
                done
              done
            subgoal for p''
              apply (intro allI impI)
              subgoal for p'''
                apply (cases "p' = p'''")
                 apply simp_all
                apply (cases "p'' = p'''")
                 apply simp_all
                apply (cases "Ex (comp_producing wire buf (Write op' p x) (Read p' f))")
                subgoal
                  apply simp
                  apply (elim exE)
                  apply (drule comp_producing_traced_cong_causalD)
                      apply (rule Write)
                      apply assumption
                     apply (rule Read)
                      defer
                      apply simp
                     apply (smt (verit, best) causal.intros(4) fun_upd_other)
                    apply simp
                   defer
                   apply force
                  apply (elim exE disjE conjE)
                    apply (simp_all add: lfilter_eq_LNil split: if_splits)
                  subgoal
                    apply auto
                    by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
                  subgoal
                    by blast
                  subgoal
                    apply auto
                    using not_EOB apply blast+
                    done
                  done
                subgoal 
                  apply (auto simp add: lfilter_eq_LNil lset_lalternate)
                  subgoal
                    apply hypsubst_thin
                    apply (drule lset_ios1_comp_op_End_not_visible)
                        apply (rule not_comp_producing_eq_End)
                        prefer 4
                        apply assumption
                       defer
                       apply assumption+
                     apply blast
                    apply (smt (verit, best) comp_producing.intros(12) fun_upd_other)
                    done
                  subgoal
                    apply hypsubst_thin
                    apply (drule lset_ios2_comp_op_End_not_visible)
                        apply assumption
                       apply (rule not_comp_producing_eq_End)
                       prefer 4
                       apply blast
                      defer
                      apply assumption+
                    apply (smt (verit, best) comp_producing.intros(12) fun_upd_other)
                    done
                  done
                done
              done
             apply auto
            done
          subgoal for lxs lxs'
            apply hypsubst_thin
            apply (elim causal_OutInpE)
               apply (simp_all split: if_splits)
             apply auto[1]
            apply (rule tc_readEOB)
            apply (rule tc_base exI conjI; (rule refl | assumption)?)+
            done
          subgoal for lxs lxs'
            apply hypsubst_thin
            apply (elim causal_OutInpE)
               apply (simp_all split: if_splits)
              apply (auto 10 10 intro!: tc_base)
            done
          subgoal for lxs lxs'
            apply hypsubst_thin
            apply (elim causal_OutInpE)
               apply (simp_all split: if_splits)
             apply (auto 10 10 intro!: tc_base)
            done
          subgoal for lxs lxs'
            apply hypsubst_thin
            apply (elim causal_OutInpE)
               apply (simp_all split: if_splits)
            subgoal for p''
              apply (cases "Ex (comp_producing wire buf (Write op' p x) (Read p' f))")
              subgoal
                apply simp
                apply (elim exE)
                apply (drule comp_producing_traced_cong_causalD)
                    apply (rule Write)
                    apply assumption
                  apply (rule ReadEOB)
                  apply assumption
                apply (smt (verit, best) causal.intros(4) fun_upd_apply fun_upd_upd)
                apply (elim exE disjE conjE)
                  apply (simp_all add: lfilter_eq_LNil split: if_splits)
                subgoal
                  apply auto
                  by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
                subgoal
                  by blast
                subgoal
                  apply auto
                  using not_EOB apply blast+
                  done
                done
              subgoal 
                apply (auto simp add: lfilter_eq_LNil lset_lalternate)
                subgoal
                  apply hypsubst_thin
                  apply (drule lset_ios1_comp_op_End_not_visible)
                      apply (rule not_comp_producing_eq_End)
                      prefer 4
                      apply assumption
                     defer
                     apply assumption+
                   apply blast
                  defer
                  apply (metis comp_producing.intros(12) fun_upd_same fun_upd_upd)
                  done
                subgoal
                  apply hypsubst_thin
                  apply (drule lset_ios2_comp_op_End_not_visible)
                      apply assumption
                     apply (rule not_comp_producing_eq_End)
                     prefer 4
                     apply blast
                    defer
                    apply assumption+
                  apply (metis comp_producing.intros(12) fun_upd_same fun_upd_upd)
                  done
                done
              done
            subgoal for p''
              apply (intro allI impI)
              subgoal for p'''
                apply (cases "p' = p'''")
                 apply simp_all
                apply (cases "p'' = p'''")
                 apply simp_all
                apply (cases "Ex (comp_producing wire buf (Write op' p x) (Read p' f))")
                subgoal
                  apply simp
                  apply (elim exE)
                  apply (drule comp_producing_traced_cong_causalD)
                      apply (rule Write)
                      apply assumption
                    apply (rule ReadEOB)
                    apply assumption
                apply (smt (verit, best) causal.intros(4) fun_upd_apply fun_upd_upd)
                  apply (elim exE disjE conjE)
                    apply (simp_all add: lfilter_eq_LNil split: if_splits)
                  subgoal
                    apply auto
                    by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
                  subgoal
                    by blast
                  subgoal
                    apply auto
                    using not_EOB apply blast+
                    done
                  done
                subgoal 
                  apply (auto simp add: lfilter_eq_LNil lset_lalternate)
                  subgoal
                    apply hypsubst_thin
                    apply (drule lset_ios1_comp_op_End_not_visible)
                        apply (rule not_comp_producing_eq_End)
                        prefer 4
                        apply assumption
                       defer
                       apply assumption+
                     apply blast
                    apply (smt (verit, best) comp_producing.intros(12) fun_upd_other)
                    done
                  subgoal
                    apply hypsubst_thin
                    apply (drule lset_ios2_comp_op_End_not_visible)
                        apply assumption
                       apply (rule not_comp_producing_eq_End)
                       prefer 4
                       apply blast
                      defer
                      apply assumption+
                    apply (smt (verit, best) comp_producing.intros(12) fun_upd_other)
                    done
                  done
                done
              done
            apply auto
            done
          done
        subgoal for op p x op' p' x'
          apply (elim traced_WriteE)
          subgoal for lxs lxs'
            apply (auto split: option.splits if_splits observation.splits)
            subgoal
              apply (rule tc_write)
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
              done
            done
          done
        subgoal for op p x
          apply (elim traced_WriteE traced_EndE)
          subgoal for lxs
            apply (auto split: option.splits if_splits observation.splits)
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (drule comp_producing_traced_cong_causalD)
                  apply (rule Write)
                  apply assumption+
                 apply (rule End)
                apply (meson causal.intros(10))
              apply (auto split: if_splits)
              using not_EOB apply blast
              apply (meson comp_producing.intros(4) not_comp_producing_eq_End)
              done
            subgoal
              apply (drule comp_producing_traced_cong_causalD)
                  apply (rule Write)
                  apply assumption+
                 apply (rule End)
                apply (meson causal.intros(10))
              apply (auto split: if_splits)
              using not_EOB apply blast
              done
            subgoal for y
              apply hypsubst_thin
              apply (auto simp add: lfilter_eq_LNil lset_lalternate)
              apply (frule not_comp_producing_eq_End)
              apply (frule lset_ios1_comp_op_End_not_visible[rotated 1]) 
                  apply (rule Write)
                  apply assumption
                 apply (rule End)
              using causal.intros(10) apply blast
               apply (auto split: if_splits)
              apply (metis End causal.intros(10) comp_producing.intros(4) lset_ios1_comp_op_End_not_visible not_comp_producing_eq_End)
              done
            done
          done
        subgoal for p f
          apply (elim traced_ReadE traced_EndE)
          subgoal for x lxs
            apply (auto 2 0 split: option.splits if_splits observation.splits)
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (frule comp_producing_traced_cong_causalD)
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 apply (simp add: causal.intros(11))
                apply (auto split: if_splits)
              using not_EOB apply blast
              done
            subgoal
              apply (frule comp_producing_traced_cong_causalD)
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 apply (simp add: causal.intros(11))
                apply (auto split: if_splits)
              using not_EOB apply blast
              done
            subgoal
              apply (auto simp add: lfilter_eq_LNil lset_lalternate)
              apply (frule not_comp_producing_eq_End)
              apply (frule lset_ios2_comp_op_End_not_visible[rotated 2]) 
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 defer
                 apply (metis causal.intros(11) comp_apply)
                apply auto
              done
            subgoal
              apply (frule comp_producing_traced_cong_causalD)
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 apply (simp add: causal.intros(11))
                apply (auto split: if_splits)
              using not_EOB apply blast
              done
            subgoal
              apply (frule comp_producing_traced_cong_causalD)
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 apply (simp add: causal.intros(11))
                apply (auto split: if_splits)
              using not_EOB apply blast
              done
            subgoal
              apply (auto simp add: lfilter_eq_LNil lset_lalternate)
              apply (frule not_comp_producing_eq_End)
              apply (frule lset_ios2_comp_op_End_not_visible[rotated 2]) 
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 defer
                 apply (metis causal.intros(11) comp_apply)
                apply auto
              done
            done
          subgoal for lxs
            apply (auto 2 0 split: option.splits if_splits observation.splits)
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (rule tc_base exI conjI; (rule refl | assumption)?)+
               apply (auto intro!: End causal.intros(10))
              done
            subgoal
              apply (frule comp_producing_traced_cong_causalD)
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 apply (simp add: causal.intros(11))
                apply (auto split: if_splits)
              using not_EOB apply blast
              apply (metis bend.simps(1) bend_bend bhd.elims bhd.simps(2) comp_apply observation.distinct(5) observation.simps(3))
              done              
            subgoal
              apply (frule comp_producing_traced_cong_causalD)
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 apply (simp add: causal.intros(11))
                apply (auto split: if_splits)
              using not_EOB apply blast
              apply (metis bend.simps(1) bend_bend bhd.elims bhd.simps(2) comp_apply observation.distinct(5) observation.simps(3))
              done   

            subgoal
              apply (auto simp add: lfilter_eq_LNil lset_lalternate)
              apply (frule not_comp_producing_eq_End)
              apply (frule lset_ios2_comp_op_End_not_visible[rotated 2]) 
                  apply (rule End)
                 apply (rule Read)
                  defer
                  apply assumption+
                 defer
                 apply (metis causal.intros(11) comp_apply)
                apply (auto split: if_splits)
              apply (metis bend.simps(1) bend_bend bhd.elims bhd.simps(2) comp_apply observation.distinct(5) observation.simps(3))
              done
            done
          done
        subgoal
          apply (elim traced_ReadE traced_EndE)
          apply (auto 10 10 simp add: lfilter_eq_LNil lset_lalternate split: option.splits if_splits observation.splits intro!: causal.intros(10) End tc_base)
          done
        subgoal
          by auto
        done
      done
    done
  done

(* lemma
  "traced m (comp_op wire buf op1 op2) ios \<Longrightarrow>
   \<exists> ios1 ios2. lfocus id (range Inp \<union> Out ` (- dom wire)) ios1 = lfocus (map_IO projl projl) (range (Inp o Inl) \<union> (Out o Inl) ` (- dom wire)) ios \<and>
   lfocus id (Inp ` (- ran wire) \<union> range Out) ios2 = lfocus (map_IO projr projr) ((Inp o Inr) ` (- ran wire) \<union> range (Out o Inr)) ios"
  apply (subst (asm) traced_comp_op)
  apply (elim exE conjE)
  subgoal for ios1 ios2 m'
    apply (rule exI[of _ ios1])
    apply (rule exI[of _ ios2])
    apply (intro conjI)
    apply (clarsimp simp add:  split: sum.splits)
 *)


section\<open>Parallel composition\<close>

definition "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. BEnded)"

lemma inputs_pcomp_op[simp]:
  "inputs (pcomp_op op1 op2) \<subseteq> Inl ` inputs op1 \<union> Inr ` inputs op2"
  unfolding pcomp_op_def by (auto dest: inputs_comp_op)

lemma outputs_pcomp_op[simp]:
  "outputs (pcomp_op op1 op2) \<subseteq> Inl ` outputs op1 \<union> Inr ` outputs op2"
  unfolding pcomp_op_def by (auto dest: outputs_comp_op)

section\<open>Sequential composition\<close>

definition "scomp_op op1 op2 = map_op projl projr (comp_op Some (\<lambda>_. BEmpty) op1 op2)"

lemma inputs_scomp_op[simp]:
  "inputs (scomp_op op1 op2) \<subseteq> inputs op1"
  unfolding scomp_op_def by (auto simp: op.set_map ran_def dest: inputs_comp_op)

lemma outputs_scomp_op[simp]:
  "outputs (scomp_op op1 op2) \<subseteq> outputs op2"
  unfolding scomp_op_def by (auto simp: op.set_map ran_def dest: outputs_comp_op)

end