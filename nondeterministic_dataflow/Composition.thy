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

coinductive alt where
    "\<forall>(io, x) \<in> lset ios. pred_IO isl isl io \<Longrightarrow> alt ios"
  | "\<forall>(io, x) \<in> lset ios. pred_IO (Not o isl) (Not o isl) io \<Longrightarrow> alt ios"
  | "alt ios \<Longrightarrow> pred_IO isl isl io1 \<Longrightarrow> pred_IO (Not o isl) (Not o isl) io2 \<Longrightarrow> alt (LCons (io1, x) (LCons (io2, y) ios))"

lemma "traced m (comp_op wire buf op1 op2) ios =
  (\<exists>ios1 ios2 m'. traced (m o Inl) op1 ios1 \<and> traced m' op2 ios2 \<and> (\<forall> p \<in> (- ran wire). m' p = (m o Inr) p) \<and> alt ios \<and>
    lfocus id (range Inp \<union> Out ` (- dom wire)) ios1 = lfocus (map_IO projl projl) (range (Inp o Inl) \<union> (Out o Inl) ` (- dom wire)) ios \<and>
    lfocus id (Inp ` (- ran wire) \<union> range Out) ios2 = lfocus (map_IO projr projr) ((Inp o Inr) ` (- ran wire) \<union> range (Out o Inr)) ios \<and>
    (\<forall>p \<in> ran wire. bapp (buf p) (lproject (=) (lfocus (the o wire o projo) (Out ` dom wire) ios1) p) = lproject (=) (lfocus proji (Inp ` ran wire) ios2) p))"
  apply (rule iffI)
  subgoal sorry
  subgoal
    apply (elim exE conjE)
    subgoal for ios1 ios2 m'
      apply (coinduction arbitrary: ios ios1 ios2 m m' op1 op2 buf)
      subgoal for ios ios1 ios2 m m' op1 op2 buf
        apply (cases op1; cases op2)
        apply simp_all
        apply (intro impI conjI)



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