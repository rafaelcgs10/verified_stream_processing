\<comment> \<open>The basic operators from the BNA book "Network Algebra for Synchronous and Asynchronous Dataflow" (https://staff.fnwi.uva.nl/c.a.middelburg/papers/P9508.pdf) \<close>
theory BNA_Operators

imports
  Operator
begin

term Inl

section \<open>comp_op: Compositions\<close>
datatype (discs_sels) ('ip1, 'ip2, 'op1, 'op2, 'd) comp_op_aux =
  Read_aux "'ip1 + 'ip2" "'d \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op"
  | Write_aux "('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op" "'op1 + 'op2" 'd
  | Silent_aux "('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op"

abbreviation eval_comp_op_aux where
  "eval_comp_op_aux c aux \<equiv> (case aux of
    Read_aux p f \<Rightarrow> Read p (\<lambda>y. let (buf, op1, op2) = f y in c buf op1 op2)
  | Write_aux (buf, op1, op2) q x \<Rightarrow> Write (c buf op1 op2) q x
  | Silent_aux (buf, op1, op2) \<Rightarrow> Silent (c buf op1 op2))"


corec comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op" where
  "comp_op wire buf op1 op2 =
     Choice (cimage (eval_comp_op_aux (comp_op wire)) (cUn
       (cimage (\<lambda>op. case op of
           Read p f \<Rightarrow> Read_aux (Inl p) (\<lambda>x. (buf, f x, op2))
         | Write op p x \<Rightarrow> (case wire p of
             None \<Rightarrow> Write_aux (buf, op, op2) (Inl p) x
           | Some q \<Rightarrow> Silent_aux (BENQ q x buf, op, op2))
         | Silent op \<Rightarrow> Silent_aux (buf, op, op2)) (choices op1))
       (cimage (\<lambda>op. case op of
           Read p f \<Rightarrow> if p \<in> ran wire then Silent_aux (BTL p buf, op1, f (BHD p buf))
             else Read_aux (Inr p) (\<lambda>x. (buf, op1, f x))
         | Write op p x \<Rightarrow> Write_aux (buf, op1, op) (Inr p) x
         | Silent op \<Rightarrow> Silent_aux (buf, op1, op)) (sound_reads wire buf (choices op2)))))"

subsection \<open>Basic simplification properties\<close>
lemma comp_op_code[code]: "comp_op wire buf op1 op2 =
  Choice (cUn
    (cimage (\<lambda>op. case op of
        Read p f \<Rightarrow> Read (Inl p) (\<lambda>x. comp_op wire buf (f x) op2)
      | Write op p x \<Rightarrow> (case wire p of
          None \<Rightarrow> Write (comp_op wire buf op op2) (Inl p) x
        | Some q \<Rightarrow> Silent (comp_op wire (BENQ q x buf) op op2))
      | Silent op \<Rightarrow> Silent (comp_op wire buf op op2)) (choices op1))
    (cimage (\<lambda>op. case op of
        Read p f \<Rightarrow> if p \<in> ran wire then Silent (comp_op wire (BTL p buf) op1 (f (BHD p buf)))
          else Read (Inr p) (\<lambda>x. comp_op wire buf op1 (f x))
      | Write op p x \<Rightarrow> Write (comp_op wire buf op1 op) (Inr p) x
      | Silent op \<Rightarrow> Silent (comp_op wire buf op1 op)) (sound_reads wire buf (choices op2))))"
  apply (subst comp_op.code)
  apply (unfold cimage_cUn op.inject)
  apply (rule arg_cong2[where f = cUn])
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: comp_op_aux.splits op.splits option.splits)
  done

lemma comp_op_simps[simp]:
  "comp_op wire buf (Read p1 f1) (Read p2 f2) =
    Choice (cinsert (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Read p2 f2)))
     (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (Silent (comp_op wire (BTL p2 buf) (Read p1 f1) (f2 (BHD p2 buf)))))
      else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Read p1 f1) (f2 y)))))"
  "comp_op wire buf (Read p1 f1) (Write op2 q2 x2) =
    choice2 (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Write op2 q2 x2))) (Write (comp_op wire buf (Read p1 f1) op2) (Inr q2) x2)"
  "comp_op wire buf (Read p1 f1) (Choice op2s) = 
    Choice (cinsert (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Choice op2s))) (cimage
       (case_op (\<lambda>p f. if p \<in> ran wire then Silent (comp_op wire (BTL p buf) (Read p1 f1) (f (BHD p buf))) else Read (Inr p) (\<lambda>x. comp_op wire buf (Read p1 f1) (f x)))
         (\<lambda>op p. Write (comp_op wire buf (Read p1 f1) op) (Inr p)) (\<lambda> op. undefined) (\<lambda>op. Silent (comp_op wire buf (Read p1 f1) op)))
       (sound_reads wire buf (cUnion (cimage choices op2s)))))"
  "comp_op wire buf (Write op1 q1 x1) (Read p2 f2) =
    Choice (cinsert (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Read p2 f2)) (Inl q1) x1
      | Some q \<Rightarrow> Silent (comp_op wire (BENQ q x1 buf) op1 (Read p2 f2)))
      (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (Silent (comp_op wire (BTL p2 buf) (Write op1 q1 x1) (f2 (BHD p2 buf)))))
        else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Write op1 q1 x1) (f2 y)))))"
  "comp_op wire buf (Write op1 q1 x1) (Write op2 q2 x2) =
    choice2 (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Write op2 q2 x2)) (Inl q1) x1
      | Some q \<Rightarrow> Silent (comp_op wire (BENQ q x1 buf) op1 (Write op2 q2 x2)))
      (Write (comp_op wire buf (Write op1 q1 x1) op2) (Inr q2) x2)"
  "comp_op wire buf (Write op1 q1 x1) (Choice op2s) =
     Choice (cinsert (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Choice op2s)) (Inl q1) x1
      | Some q \<Rightarrow> Silent (comp_op wire (BENQ q x1 buf) op1 (Choice op2s)))
      (cimage
       (case_op (\<lambda>p f. if p \<in> ran wire then Silent (comp_op wire (BTL p buf) (Write op1 q1 x1) (f (BHD p buf))) else Read (Inr p) (\<lambda>x. comp_op wire buf (Write op1 q1 x1) (f x)))
         (\<lambda>op p. Write (comp_op wire buf (Write op1 q1 x1) op) (Inr p)) (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf (Write op1 q1 x1) op)))
       (sound_reads wire buf (cUnion (cimage choices op2s)))))"
  "comp_op wire buf (Choice op1s) (Read p2 f2) =
    Choice (cUn (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (Silent (comp_op wire (BTL p2 buf) (Choice op1s) (f2 (BHD p2 buf)))))
        else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Choice op1s) (f2 y)))) (cimage
       (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Read p2 f2)))
         (\<lambda>op p x. case wire p of None \<Rightarrow> Write (comp_op wire buf op (Read p2 f2)) (Inl p) x | Some q \<Rightarrow> Silent (comp_op wire (BENQ q x buf) op (Read p2 f2))) (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf op (Read p2 f2))))
       (cUnion (cimage choices op1s))))"
  "comp_op wire buf (Choice op1s) (Write op2 q2 x2) =
    Choice (cinsert (Write (comp_op wire buf (Choice op1s) op2) (Inr q2) x2) (cimage
       (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Write op2 q2 x2)))
         (\<lambda>op p x. case wire p of None \<Rightarrow> Write (comp_op wire buf op (Write op2 q2 x2)) (Inl p) x | Some q \<Rightarrow> Silent (comp_op wire (BENQ q x buf) op (Write op2 q2 x2))) (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf op (Write op2 q2 x2))))
       (cUnion (cimage choices op1s))))"
  "comp_op wire buf (Choice op1s) (Choice op2s) =
    Choice (cUn (cimage
             (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Choice op2s)))
               (\<lambda>op p x.
                   case wire p of None \<Rightarrow> Write (comp_op wire buf op (Choice op2s)) (Inl p) x
                   | Some q \<Rightarrow> Silent (comp_op wire (BENQ q x buf) op (Choice op2s)))
               (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf op (Choice op2s))))
             (cUnion (cimage choices op1s)))
        (cimage
          (case_op
            (\<lambda>p f. if p \<in> ran wire then Silent (comp_op wire (BTL p buf) (Choice op1s) (f (BHD p buf)))
                   else Read (Inr p) (\<lambda>x. comp_op wire buf (Choice op1s) (f x)))
            (\<lambda>op p. Write (comp_op wire buf (Choice op1s) op) (Inr p)) (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf (Choice op1s) op)))
          (sound_reads wire buf (cUnion (cimage choices op2s)))))" 
  by (subst comp_op_code, auto simp add: image_iff  split: option.splits)+

lemma comp_op_not_Read[simp]:
  "\<not> is_Read (comp_op wire buf op1 op2)"
  by (subst comp_op_code, simp)
lemma comp_op_not_Write[simp]:
  "\<not> is_Write (comp_op wire buf op1 op2)"
  by (subst comp_op_code, simp)
lemma comp_op_is_choice[simp]:
  "is_Choice (comp_op wire buf op1 op2)"
  by (subst comp_op_code, simp)

subsection \<open>Inputs of comp_op\<close>

lemma inputs_comp_op: "sub_op (Read p g) (comp_op wire buf op1 op2) d \<Longrightarrow> p \<in> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
proof (induct p \<open>comp_op wire buf op1 op2\<close> arbitrary: buf op1 op2 rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (auto simp add: comp_op_code)
next
  case (Read2 p p' f x d g)
  then show ?case by (auto simp add: comp_op_code)
next
  case (Write p p' op' x d g)
  then show ?case by (auto simp add: comp_op_code)
next
  case (Silent p p' op' x d g)
  then show ?case by (auto simp add: comp_op_code)
next
  case (Choice p p' ops f buf op1)
  then show ?case 
    apply -
    apply (auto del: disjCI)
    apply (subst (asm) (2) comp_op_code)
    apply (auto del: disjCI)
    subgoal for op
      apply (cases op)
         apply (auto del: disjCI split: option.splits; hypsubst_thin?)
      subgoal for p f
        by (meson choices_sub_op cin.rep_eq image_iff sub_op_Read_inputs)
      subgoal for p' f' x' n
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply hypsubst_thin
        apply (rule disjI1)
        using inputs_after_choices 
        apply (metis cin.rep_eq imageI inputs_sub_op_Read sub_op.intros(2) sub_op_Read_inputs)
        done
      subgoal for op1' p' x'
        apply hypsubst_thin
        apply (auto del: disjCI split: option.splits; hypsubst_thin?)
        subgoal for n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          apply (simp add: inputs_after_choices)
          done
        subgoal for p' n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          apply (simp add: inputs_after_choices)
          done
        done
      subgoal 
        by (auto del: disjCI split: option.splits)
      subgoal for ops
        apply (auto del: disjCI split: option.splits; hypsubst_thin?)
        subgoal for n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          apply (simp add: inputs_after_choices)
          done
        done
      done
    subgoal for op
      apply (cases op)
         apply (auto simp add: Read_choices_inputs del: disjCI split: option.splits if_splits; hypsubst_thin?)
      subgoal for p' x n
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply hypsubst_thin
        apply (meson DiffI cin.rep_eq image_eqI inputs_after_choices inputs_sub_op_Read sub_op_Read sub_op_Read_inputs)
        done
      subgoal for p f x n
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply hypsubst_thin
        apply (meson DiffI cin.rep_eq imageI inputs_after_choices inputs_sub_op_Read sub_op_Read sub_op_Read_inputs)
        done
      subgoal
        apply hypsubst_thin
        apply simp
        apply (auto del: disjCI)
        subgoal for n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          apply (simp add: inputs_after_choices)
          done
        done
      subgoal
        by (auto del: disjCI)
      subgoal
        apply hypsubst_thin
        apply simp
        apply (auto del: disjCI)
        subgoal for n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          apply (simp add: inputs_after_choices)
          done
        done
      done
    done
qed

lemma inputs_comp_op_le:
  "inputs (comp_op wire buf op1 op2) \<subseteq> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  using inputs_comp_op by (metis inputs_sub_op_Read subsetI)
lemma inputs_comp_op_le_alt[dest!]:
  "c \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow> c \<in> Inl ` inputs op1 \<or> c \<in> Inr ` (inputs op2 - ran wire)"
  using set_mp[OF inputs_comp_op_le, simplified] by force

subsection \<open>Outputs of comp_op\<close>

lemma outputs_comp_op:
  "sub_op (Write op' p y) (comp_op wire buf op1 op2) d \<Longrightarrow> p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
proof (induct p \<open>comp_op wire buf op1 op2\<close> arbitrary: buf op1 op2 rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (auto simp add: comp_op_code)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (auto simp add: comp_op_code)
next
  case (Silent p op' op2 y d)
  then show ?case by (auto simp add: comp_op_code)
next
  case (Choice p op2 y d ops)
  then show ?case 
    apply -
    apply -
    apply (auto del: disjCI)
    apply (subst (asm) (2) comp_op_code)
    apply (auto del: disjCI)
    subgoal for op
      apply (cases op)
         apply (auto del: disjCI split: option.splits; hypsubst_thin?)
      subgoal for p f x n
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply hypsubst_thin
        using domIff outputs_after_choices apply fastforce
        done
      subgoal for op p x
        apply hypsubst_thin
        apply (auto del: disjCI split: option.splits; hypsubst_thin?)
        subgoal
          by (simp add: domIff outputs_after_choices)
        subgoal for n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          using domIff outputs_after_choices apply fastforce
          done
        subgoal for _ n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          using domIff outputs_after_choices apply fastforce
          done
        done
      subgoal for op
        by auto
      subgoal for p
        apply hypsubst_thin
        apply auto
        subgoal for n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          using domIff outputs_after_choices apply fastforce
          done
        done
      done
    subgoal for op
      apply hypsubst_thin
      apply (cases op)
         apply (auto del: disjCI split: if_splits option.splits; hypsubst_thin?)
      subgoal for _ _ n
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply hypsubst_thin
        using domIff outputs_after_choices apply fastforce
        done
      subgoal for _ _ _ n
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply hypsubst_thin
        using domIff outputs_after_choices apply fastforce
        done
      subgoal 
        apply auto
        subgoal
          by (simp add: outputs_after_choices)
        subgoal for n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          using domIff outputs_after_choices apply fastforce
          done
        done
      subgoal 
        by auto
      subgoal
        apply auto
        subgoal for n
          apply (drule meta_spec[of _ n])
          apply (drule meta_spec)+
          apply simp
          apply (drule meta_mp)
           apply assumption
          apply (auto del: disjCI)
          apply hypsubst_thin
          using domIff outputs_after_choices apply fastforce
          done
        done
      done
    done
next
  case (Write2 p op' x)
  then show ?case by (auto simp add: comp_op_code)
qed

lemma outputs_comp_op_le:
  "outputs (comp_op wire buf op1 op2) \<subseteq> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  using outputs_comp_op by (metis outputs_sub_op_Write subsetI)
lemma outputs_comp_op_le_alt[dest!]:
  "c \<in> outputs (comp_op wire buf op1 op2) \<Longrightarrow> c \<in> Inl ` (outputs op1 - dom wire) \<or> c \<in> Inr ` outputs op2"
  using set_mp[OF outputs_comp_op_le, simplified] by force

subsection \<open>Properties of the (general) composition\<close>

lemma step_comp_op_L[intro]:
  "step io op1 op1' \<Longrightarrow>
   (case io of Inp p x \<Rightarrow> True | Out p x \<Rightarrow> p \<notin> dom wire | Tau \<Rightarrow> True) \<Longrightarrow>
   step (map_IO Inl Inl id io) (comp_op wire buf op1 op2) (comp_op wire buf op1' op2)"
  apply (induct io op1 op1' arbitrary: op2 buf rule: step.induct)
  subgoal
    apply (subst (1) comp_op_code)
    apply (auto split: IO.splits intro: step.intros)
    done
  subgoal
    apply (subst (1) comp_op_code)
    apply (auto split: IO.splits option.splits intro: step.intros)
    done
  subgoal
    apply (subst (1) comp_op_code)
    apply (auto split: IO.splits option.splits intro: step.intros)
    done
  subgoal
    apply (erule step_choicesE)
      apply simp
    subgoal
      apply (subst (1) comp_op_code)
      apply (rule SC)
       apply (rule cUnI1)
       apply (rule cimage_eqI)
        apply (rule refl)
       apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) [2]
      done
    subgoal
      apply (subst (1) comp_op_code)
      apply (rule SC)
       apply (rule cUnI1)
       apply (rule cimage_eqI)
        apply (rule refl)
       apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) 
      done
    subgoal
      apply (subst (1) comp_op_code)
      apply (rule SC)
       apply (rule cUnI1)
       apply (rule cimage_eqI)
        apply (rule refl)
       apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) 
      done
    done
  done

lemma step_Tau_comp_op_L[intro]:
  "step (Out p x) op1 op1' \<Longrightarrow>
   wire p = Some q \<Longrightarrow>
   buf' = BENQ q x buf \<Longrightarrow>
   op2 = op2' \<Longrightarrow>
   step Tau (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  apply hypsubst_thin
  apply (erule step_choicesE)
    apply simp_all
  apply (subst (1) comp_op_code)
  apply simp
  apply (rule SC)
   apply simp
   apply (rule disjI1)
   apply (rule image_eqI)
    apply (rule refl)
   apply assumption
  apply auto
  done

lemma step_Tau_comp_op_L_alt[intro!]:
  "step (Out p x) op1 op1' \<Longrightarrow> wire p = Some q \<Longrightarrow> step Tau (comp_op wire buf op1 op2') (comp_op wire (BENQ q x buf) op1' op2')"
  by auto

lemma step_comp_op_R[intro]:
  "step io op2 op2' \<Longrightarrow>
   (case io of Out p x \<Rightarrow> True | Inp p x \<Rightarrow> p \<notin> ran wire | Tau \<Rightarrow> True) \<Longrightarrow>
   step (map_IO Inr Inr id io) (comp_op wire buf op1 op2) (comp_op wire buf op1 op2')"
  apply (induct io op2 op2' arbitrary: op1 buf rule: step.induct)
  subgoal for p x f op1 buf
    apply (subst (1) comp_op_code)
    unfolding cfilter_def Set.filter_def
    apply (clarsimp split: IO.splits option.splits intro: step.intros)
    subgoal
      apply (rule SC)
       apply (rule cUnI2)
       apply simp
       apply (rule image_eqI[of "Read (Inr p) (\<lambda>x. (comp_op wire buf op1 (f x)))" _ "Read p f"])
        apply simp_all
      subgoal 
        apply (subst cset.acset_inverse)
         apply (auto simp add: countableI' inj_on_def)
        done
      subgoal
        by (meson step.intros(1))
      done
    done
  subgoal for q x op op1 buf
    apply (subst (1) comp_op_code)
    unfolding cfilter_def Set.filter_def
    apply (clarsimp split: IO.splits option.splits intro: step.intros)
    apply (rule SC)
     apply (rule cUnI2)
     apply simp
     apply (rule image_eqI[of _ _ "Write op q x"])
      apply simp_all
    subgoal 
      apply (subst cset.acset_inverse)
       apply (auto simp add: countableI' inj_on_def)
      done
    subgoal
      by (meson step.intros(2))
    done
  subgoal for op op1 buf
    apply auto
    apply (subst (1) comp_op_code)
    apply auto
    apply (rule SC[rotated])
     apply (rule ST)
    apply auto
    apply force
    done
  subgoal for op ops l op' op1 buf
    apply (erule step_choicesE)
    subgoal for p f x
      apply simp
      apply hypsubst_thin
      apply (subst (1) comp_op_code)
      apply (rule SC)
       apply (rule cUnI2)
       apply simp
       apply (rule image_eqI[of "Read (Inr p) (\<lambda>x. comp_op wire buf op1 (f x))" _ "Read p f"])
        apply simp
      unfolding cfilter_def Set.filter_def
       apply auto
      done
    subgoal for p x
      apply simp
      apply hypsubst_thin
      apply (subst (1) comp_op_code)
      apply (rule SC)
       apply (rule cUnI2)
       apply simp
       apply (rule image_eqI[of _ _ "Write op' p x"])
        apply simp
      unfolding cfilter_def Set.filter_def
       apply auto
      done
    subgoal
      apply auto
      apply (subst (1) comp_op_code)
      apply (rule SC[rotated])
       apply (rule ST)
      apply (smt (verit, ccfv_threshold) cUN_I cUnI2 choices_Choice cin.rep_eq cin_cimage_cfilter op.simps(20))
      done
    done
  done

lemma step_Tau_comp_op_R[intro]:
  "step (Inp p x) op2 op2' \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow>
   buf p \<noteq> [] \<Longrightarrow>
   BHD p buf = x \<Longrightarrow>
   buf' = BTL p buf \<Longrightarrow>
   op1' = op1 \<Longrightarrow>
   step Tau (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  apply hypsubst_thin
  apply (erule step_choicesE)
    apply simp_all
  apply (subst (1) comp_op_code)
  apply simp
  apply (rule SC)
   apply simp
   apply (rule disjI2)
   apply (rule image_eqI)
    apply (rule refl)
   apply auto
  done

lemma step_Tau_comp_op_R_alt[intro!]:
  "step (Inp p (BHD p buf)) op2 op2' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> step Tau (comp_op wire buf op1 op2) (comp_op wire (BTL p buf) op1 op2')"
  by auto

lemma step_comp_op_R_Out[intro!]:
  "step (Out p x) op2 op2' \<Longrightarrow> buf = buf' \<Longrightarrow> op1 = op1' \<Longrightarrow> step (Out (Inr p) x) (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  using step_comp_op_R by force

lemma step_comp_op_R_Inp[intro!]:
  "step (Inp p x) op2 op2' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> buf = buf' \<Longrightarrow> op1 = op1' \<Longrightarrow> step (Inp (Inr p) x) (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  using step_comp_op_R by force

lemma step_comp_op_R_Tau[intro]:
  "step Tau op2 op2' \<Longrightarrow> buf = buf' \<Longrightarrow> op1 = op1' \<Longrightarrow> step Tau (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  using step_comp_op_R by force

lemma step_comp_op_L_Inp[intro!]:
  "step (Inp p x) op1 op1' \<Longrightarrow> buf = buf' \<Longrightarrow> op2 = op2' \<Longrightarrow>  step (Inp (Inl p) x) (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  using step_comp_op_L by force

lemma step_comp_op_L_Out[intro!]:
  "step (Out p x) op1 op1' \<Longrightarrow> p \<notin> dom wire \<Longrightarrow> buf = buf' \<Longrightarrow> op2 = op2' \<Longrightarrow> step (Out (Inl p) x) (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  using step_comp_op_L
  by (metis IO.map_id IO.simps(10) IO.simps(16))

lemma step_comp_op_L_Tau[intro]:
  "step Tau op1 op1' \<Longrightarrow> buf = buf' \<Longrightarrow> op2 = op2' \<Longrightarrow> step Tau (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  using step_comp_op_L by force

lemma step_comp_op_cases:
  "step io (comp_op wire buf op1 op2) op \<Longrightarrow>
   (\<exists> p x op1'. io = Inp (Inl p) x \<and> op = comp_op wire buf op1' op2 \<and> step (Inp p x) op1 op1') \<or>
   (\<exists> p x op2'. io = Out (Inr p) x \<and> op = comp_op wire buf op1 op2' \<and> step (Out p x) op2 op2') \<or>
   (\<exists> p x op1'. io = Out (Inl p) x \<and> op = comp_op wire buf op1' op2 \<and> wire p = None \<and> step (Out p x) op1 op1') \<or>
   (\<exists> p x op2'. io = Inp (Inr p) x \<and> op = comp_op wire buf op1 op2' \<and> p \<notin> ran wire \<and> step (Inp p x) op2 op2') \<or> 
   (\<exists> p x op1' q. io = Tau \<and> op = comp_op wire (BENQ q x buf) op1' op2 \<and> wire p = Some q \<and> step (Out p x) op1 op1') \<or> 
   (\<exists> p x op2'. io = Tau \<and> op = comp_op wire (BTL p buf) op1 op2' \<and> p \<in> ran wire \<and> step (Inp p x) op2 op2' \<and> buf p \<noteq> [] \<and> BHD p buf = x) \<or>
   (\<exists> p x op1'. io = Tau \<and> op = comp_op wire buf op1' op2 \<and> step Tau op1 op1') \<or>
   (\<exists> p x op2'. io = Tau \<and> op = comp_op wire buf op1 op2' \<and> step Tau op2 op2')"
  apply (erule step_choicesE)
  subgoal for p f x
    apply simp
    apply (cases p)
    subgoal for lp
      apply simp
      apply hypsubst_thin
      apply (subst (asm) comp_op_code)
      apply (auto split: if_splits)
      subgoal for op'
        apply (cases op')
           apply auto
        subgoal for f'
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule refl)
          apply (simp add: Read_in_choices_step)
          done
        subgoal
          by (auto split: option.splits)
        done
      subgoal for op'
        apply (cases op')
           apply auto
        subgoal for f' p'
          by (auto split: if_splits)
        done
      done
    subgoal for rp
      apply simp
      apply hypsubst_thin
      apply (subst (asm) comp_op_code)
      apply (auto split: if_splits option.splits)
      subgoal for op'
        apply (cases op')
           apply (auto split: if_splits option.splits)
        done
      subgoal for op'
        apply (cases op')
           apply (auto split: if_splits option.splits)
        apply hypsubst_thin
        apply (intro exI conjI)
         apply (rule refl)
        apply (simp add: Read_in_choices_step)
        done
      done
    done
  subgoal for p x
    apply simp
    apply (cases p)
    subgoal for lp
      apply simp
      apply hypsubst_thin
      apply (subst (asm) comp_op_code)
      apply (auto split: if_splits option.splits)
      subgoal for op'
        apply (cases op')
           apply (auto split: if_splits option.splits)
        subgoal for f'
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule refl)
          apply (simp add: Write_in_choices_step)
          done
        done
      subgoal for op'
        apply (cases op')
           apply auto
        subgoal for f' p'
          by (auto split: if_splits)
        done
      done
    subgoal for rp
      apply simp
      apply hypsubst_thin
      apply (subst (asm) comp_op_code)
      apply (auto split: if_splits option.splits)
      subgoal for op'
        apply (cases op')
           apply (auto split: if_splits option.splits)
        done
      subgoal for op'
        apply (cases op')
           apply (auto split: if_splits option.splits)
        apply hypsubst_thin
        apply (intro exI conjI)
         apply (rule refl)
        apply (simp add: Write_in_choices_step)
        done
      done
    done
  subgoal
    apply simp
    apply hypsubst_thin
    apply (subst (asm) comp_op_code)
    apply (auto del: disjCI split: if_splits option.splits)
    subgoal for op'
      apply (cases op')
         apply (auto  del: disjCI split: if_splits option.splits)
      subgoal for op'' p x' q
        by (metis Write_in_choices_step cin.rep_eq)
      subgoal
        using Silent_in_choices_step by auto
      done
    subgoal for op'
      apply (cases op')
         apply (auto  del: disjCI split: if_splits option.splits)
      subgoal
        by (metis Read_in_choices_step cin.rep_eq)
      subgoal
        using Silent_in_choices_step by fastforce
      done
    done
  done

lemma step_comp_op_elim:
  assumes "step io (comp_op wire buf op1 op2) op"
  obtains p x op1' where "io = Inp (Inl p) x" "op = comp_op wire buf op1' op2" "step (Inp p x) op1 op1'" |
    p x op2' where "io = Out (Inr p) x" "op = comp_op wire buf op1 op2'" "step (Out p x) op2 op2'" |
    p x op1' where "io = Out (Inl p) x" "op = comp_op wire buf op1' op2" "wire p = None" "step (Out p x) op1 op1'" |
    p x op2' where "io = Inp (Inr p) x" "op = comp_op wire buf op1 op2'" "p \<notin> ran wire" "step (Inp p x) op2 op2'" |
    p x op1' q where "io = Tau" "op = comp_op wire (BENQ q x buf) op1' op2" "wire p = Some q" "step (Out p x) op1 op1'" |
    p x op2' where "io = Tau" "op = comp_op wire (BTL p buf) op1 op2'" "p \<in> ran wire" "step (Inp p x) op2 op2'" "buf p \<noteq> []" "BHD p buf = x" |
    p x op1' where "io = Tau" "op = comp_op wire buf op1' op2" "step Tau op1 op1'" |
    p x op2' where "io = Tau" "op = comp_op wire buf op1 op2'" "step Tau op2 op2'"
  using assms apply -
  apply (drule step_comp_op_cases[where io=io and wire=wire and buf=buf, of op1 op2 op])
  apply auto
  done

subsection \<open>Parallel composition operator\<close>
no_notation Sublist.parallel (infixl "\<parallel>" 50)

definition pcomp_op (infixl "\<parallel>" 64) where
  "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. [])"

fun reassoc where
  "reassoc (Inl (Inl x)) = Inl x"
| "reassoc (Inl (Inr x)) = Inr (Inl x)"
| "reassoc (Inr x) = Inr (Inr x)"

lemma reassoc_extra_simps[simp]:
  "reassoc (Inl p) = (case p of Inl p \<Rightarrow> Inl p | Inr p \<Rightarrow> Inr (Inl p))"
  by (cases p; auto)

fun assoc where
  "assoc (Inl x) = Inl (Inl x)"
| "assoc (Inr (Inl x)) = Inl (Inr x)"
| "assoc (Inr (Inr x)) = Inr x"

lemma assoc_extra_simps[simp]:
  "assoc (Inr p) = (case p of Inl p \<Rightarrow> Inl (Inr p) | Inr p \<Rightarrow> Inr p)"
  by (cases p; auto)

lemma reassoc_assoc[simp]:
  "reassoc o assoc = id"
  unfolding comp_def
  apply (rule ext)
  subgoal for x
    apply (induct x rule: assoc.induct)
      apply auto
    done
  done

lemma assoc_reassoc[simp]:
  "assoc o reassoc = id"
  unfolding comp_def
  apply (rule ext)
  subgoal for x
    apply (induct x rule: reassoc.induct)
      apply auto
    done
  done

lemma reassoc_ing[simp]:
  "inj reassoc"
  by (metis BNA_Operators.assoc_reassoc comp_apply id_apply injI)
lemma assoc_inj[simp]:
  "inj assoc"
  by (metis BNA_Operators.reassoc_assoc comp_def id_apply inj_on_inverseI)
lemma map_op_assoc_inj:
  "inj (map_op assoc assoc)"
  by (simp add: op.inj_map)
lemma map_op_reassoc_inj:
  "inj (map_op reassoc reassoc)"
  by (simp add: op.inj_map)

lemma map_IO_assoc_eq_Out_Inl[intro!]:
  "IO = Out (Inl p) x \<Longrightarrow>
   map_IO id assoc id IO = Out (Inl (Inl p)) x"
  by auto

lemma map_IO_assoc_eq_Inp_Inl[intro!]:
  "IO = Out (Inl p) x \<Longrightarrow>
   map_IO f assoc id IO = Out (Inl (Inl p)) x"
  by auto

lemma map_IO_assoc_eq_Inp_Inr_Inl[intro!]:
  "IO = Out (Inr (Inl p)) x \<Longrightarrow>
   map_IO f assoc id IO = Out (Inl (Inr p)) x"
  by auto

lemma map_IO_assoc_eq_Out_Inr[intro!]:
  "IO = Out (Inr (Inr p)) x \<Longrightarrow>
   map_IO id assoc id IO = Out (Inr p) x"
  by auto

lemma map_IO_assoc_Inp_Inl[simp]:
  "map_IO id assoc id (Inp (Inl p) x) = Inp (Inl p) x"
  by simp

subsection \<open>Sequential composition operator\<close>
definition scomp_op (infixl "\<bullet>" 65) where
  "scomp_op op1 op2 = map_op projl projr (comp_op Some (\<lambda>_. []) op1 op2)"

subsubsection \<open>Congruence for strong bisim\<close>
lemma bisim_choices_Read:
  "op1 ~ op1' \<Longrightarrow>
   Read p f |\<in>| (choices op1) \<Longrightarrow>
   \<exists> f'. Read p f' |\<in>| (choices op1') \<and> f x ~ f' x"
  apply (erule bisim.cases)
  apply auto
  unfolding sim_def
  apply (drule Read_in_choices_step[where x=x, simplified])
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply safe
  apply (erule step_choicesE[where op=op1'])
    apply auto
  done

lemma bisim_choices_Write:
  "op1 ~ op1' \<Longrightarrow>
   Write op1'' p x |\<in>| choices op1 \<Longrightarrow>
   \<exists> op. Write op p x |\<in>| choices op1' \<and> op1'' ~ op"
  apply (erule bisim.cases)
  apply auto
  unfolding sim_def
  apply (drule Write_in_choices_step[where x=x, simplified])
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply safe
  apply (erule step_choicesE[where op=op1'])
    apply auto
  done

lemma bisim_choices_Silent:
  "op1 ~ op1' \<Longrightarrow>
   Silent op1'' |\<in>| choices op1 \<Longrightarrow>
   \<exists> op. Silent op |\<in>| choices op1' \<and> op1'' ~ op"
  apply (erule bisim.cases)
  apply auto
  unfolding sim_def
  apply (drule Silent_in_choices_step[simplified])
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply safe
  apply (erule step_choicesE[where op=op1'])
    apply auto
  done

lemma bisim_comp_op_cong:
  "op1 ~ op1' \<Longrightarrow>
   op2 ~ op2' \<Longrightarrow>
   comp_op wire buf op1 op2 ~ comp_op wire buf op1' op2'"
  apply (coinduction arbitrary: op1 op2 op1' op2' buf rule: bisim_coinduct_upto)
  subgoal for op1 op2 op1' op2' buf
    unfolding sim_def
    apply (intro conjI impI allI)
    subgoal for io op
      apply (rotate_tac 2)
      apply (induct io "comp_op wire buf op1 op2" op arbitrary: buf op1 op2 op1' op2' pred: step)
         apply (subst (asm) comp_op_code, simp)
        apply (subst (asm) comp_op_code, simp)
       apply (subst (asm) comp_op_code, simp)
      subgoal for op ops l op' buf op1 op2 op1'
        apply auto
        apply (subst (asm) (5) comp_op_code)
        apply (simp add: Set.filter_def ranI image_iff bex_Un split: option.splits)
        apply (elim exE bexE disjE)
        subgoal for op'
          apply (cases op')
          subgoal for p f
            apply simp
            apply auto
            subgoal for x
              apply (drule bisim_choices_Read[where x=x])
               apply simp
              apply safe
              subgoal for f'
                apply (intro exI conjI)
                 apply (subst comp_op_code)
                 apply simp
                 apply (rule SC)
                  apply (simp add: Set.filter_def ranI image_iff bex_Un)
                  apply hypsubst_thin
                  apply (rule disjI1)
                  apply (rule bexI[of _ "Read p f'"])
                   apply simp
                  apply assumption
                 apply hypsubst_thin
                using step.intros(1) apply force
                apply (rule bc_base)
                apply (intro conjI exI)
                   apply (rule refl)+
                 apply assumption+
                done
              done
            done
          subgoal for op1'' p x
            apply (simp add: Set.filter_def ranI image_iff bex_Un split: option.splits)
            subgoal
              apply hypsubst_thin
              apply (drule bisim_choices_Write)
               apply simp
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule SC)
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI1)
                apply (erule bexI[rotated])
                apply simp
               apply (rule step.intros(2))
              apply (metis (mono_tags, lifting) bc_base)
              done
            subgoal
              apply auto
              apply hypsubst_thin
              apply (drule bisim_choices_Write)
               apply simp
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule SC)
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI1)
                apply (erule bexI[rotated])
                apply simp
               apply (rule ST)
              apply (metis (mono_tags, lifting) bc_base)
              done
            done
          subgoal 
            by auto
          subgoal for op'''
            apply auto
            apply hypsubst_thin
            apply (drule bisim_choices_Silent)
             apply simp
            apply safe
            apply (intro conjI exI)
             apply (subst comp_op_code)
             apply simp
             apply (rule SC)
              apply (simp add: Set.filter_def ranI image_iff bex_Un)
              apply (rule disjI1)
              apply (erule bexI[rotated])
              apply simp
             apply (rule ST)
            apply (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op''
          apply hypsubst_thin
          apply (cases op'')
          subgoal for p f
            apply auto
             apply (erule thin_rl)
             apply rotate_tac
            subgoal for x
              apply (drule bisim_choices_Read[where x=x])
               apply simp
              apply safe
              subgoal for f'
                apply (intro exI conjI)
                 apply (subst comp_op_code)
                 apply simp
                 apply (rule SC)
                  apply (simp add: Set.filter_def ranI image_iff bex_Un)
                  apply hypsubst_thin
                  apply (rule disjI2)
                  apply force
                 apply (rule SR)
                apply (rule bc_base)
                apply (intro conjI exI)
                   apply (rule refl)+
                 apply assumption+
                done
              done
            subgoal
              apply (auto split: if_splits)
              subgoal
                apply (erule thin_rl)
                apply rotate_tac
                apply hypsubst_thin
                apply (drule bisim_choices_Read[where x="BHD p buf"])
                 apply force
                apply safe
                apply (intro exI conjI)
                 apply (subst comp_op_code)
                 apply simp
                 apply (rule SC)
                  apply (simp add: Set.filter_def ranI image_iff bex_Un)
                  apply (rule disjI2)
                  apply (intro exI conjI)
                    apply blast
                   apply force+
                apply (rule bc_base)
                apply (intro conjI exI)
                   apply (rule refl)+
                 apply assumption+
                done
              subgoal for x
                apply (erule thin_rl)
                apply rotate_tac
                apply hypsubst_thin
                apply (drule bisim_choices_Read[where x=x])
                 apply force
                apply safe
                apply (intro exI conjI)
                 apply (subst comp_op_code)
                 apply simp
                 apply (rule SC)
                  apply (simp add: Set.filter_def ranI image_iff bex_Un)
                  apply (rule disjI2)
                  apply (intro exI conjI)
                    apply blast
                   apply force+
                apply (rule bc_base)
                apply (intro conjI exI)
                   apply (rule refl)+
                 apply assumption+
                done
              done
            done
          subgoal for op1'' p x
            apply auto
            subgoal
              apply hypsubst_thin
              apply (erule thin_rl)
              apply rotate_tac
              apply (drule bisim_choices_Write)
               apply simp
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule SC)
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI2)
                apply (intro exI conjI)
                  apply simp_all
                apply force+
              apply (metis (mono_tags, lifting) bc_base)
              done
            done
          subgoal
            by auto
          subgoal
            apply auto
            apply hypsubst_thin
            apply (erule thin_rl)
            apply rotate_tac
            apply (drule bisim_choices_Silent)
             apply simp
            apply safe
            apply (intro conjI exI)
             apply (subst comp_op_code)
             apply simp
             apply (rule SC)
              apply (simp add: Set.filter_def ranI image_iff bex_Un)
              apply (rule disjI2)
              apply (intro exI conjI)
                apply simp_all
              apply force+
            apply (metis (mono_tags, lifting) bc_base)
            done
          done
        done
      done
    subgoal for io op
      apply (rotate_tac 2)
      apply (induct io "comp_op wire buf op1' op2'" op arbitrary: buf op1 op2 op1' op2' pred: step)
         apply (subst (asm) comp_op_code, simp)
        apply (subst (asm) comp_op_code, simp)
       apply (subst (asm) comp_op_code, simp)
      subgoal for op ops l op' buf op1' op2' op1 op2
        apply auto
        apply (subst (asm) (5) comp_op_code)
        apply (simp add: Set.filter_def ranI image_iff bex_Un split: option.splits)
        apply (elim exE bexE disjE)
        subgoal for op'
          apply (cases op')
          subgoal for p f
            apply simp
            apply auto
            subgoal for x
              apply (subst (asm) (5) bisim_sym)
              apply (drule bisim_choices_Read[where x=x])
               apply simp
              apply safe
              subgoal for f'
                apply (intro exI conjI)
                 apply (subst comp_op_code)
                 apply simp
                 apply (rule SC)
                  apply (simp add: Set.filter_def ranI image_iff bex_Un)
                  apply hypsubst_thin
                  apply (rule disjI1)
                  apply (rule bexI[of _ "Read p f'"])
                   apply simp
                  apply assumption
                 apply hypsubst_thin
                using step.intros(1) apply force
                apply (smt (verit, ccfv_threshold) bc_base bisim_sym)
                done
              done
            done
          subgoal for op1'' p x
            apply (simp add: Set.filter_def ranI image_iff bex_Un split: option.splits)
            subgoal
              apply hypsubst_thin
              apply (subst (asm) (5) bisim_sym)
              apply (drule bisim_choices_Write)
               apply simp
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule SC)
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI1)
                apply (erule bexI[rotated])
                apply simp
               apply (rule step.intros(2))
              apply (smt (verit, ccfv_threshold) bc_base bisim_sym)
              done
            subgoal 
              apply auto
              apply hypsubst_thin
              apply (erule thin_rl)
              apply (subst (asm) (1) bisim_sym)
              apply (drule bisim_choices_Write)
               apply simp
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule SC)
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI1)
                apply (erule bexI[rotated])
                apply simp_all
               apply (rule ST)
              apply (rule bc_sym)
              apply (rule bc_base)
              apply (intro exI conjI)
                 apply (rule refl)
              using bisim_sym apply blast+
              done
            done
          subgoal
            by auto
          subgoal for op'
            apply auto
            apply hypsubst_thin
            apply (erule thin_rl)
            apply (subst (asm) (1) bisim_sym)
            apply (drule bisim_choices_Silent)
             apply simp
            apply safe
            apply (intro conjI exI)
             apply (subst comp_op_code)
             apply simp
             apply (rule SC)
              apply (simp add: Set.filter_def ranI image_iff bex_Un)
              apply (rule disjI1)
              apply (erule bexI[rotated])
              apply simp_all
             apply (rule ST)
            apply (rule bc_sym)
            apply (rule bc_base)
            apply (intro exI conjI)
               apply (rule refl)
            using bisim_sym apply blast+
            done
          done
        subgoal for op'
          apply (cases op')
             apply auto
          subgoal for op'' p f
            apply hypsubst_thin
            apply (erule thin_rl)
            apply rotate_tac
            apply (subst (asm) (1) bisim_sym)
            apply (drule bisim_choices_Read)
             apply simp
            apply safe
            apply (intro conjI exI)
             apply (subst comp_op_code)
             apply simp
             apply (rule SC)
              apply (simp add: Set.filter_def ranI image_iff bex_Un)
              apply (rule disjI2)
              apply force
             apply simp_all
             apply auto
            apply (rule bc_sym)
            apply (rule bc_base)
            apply (intro exI conjI)
               apply (rule refl)
            using bisim_sym apply blast+
            done
          subgoal
            apply hypsubst_thin
            apply (auto split: if_splits)
            subgoal
              apply (erule thin_rl)
              apply rotate_tac
              apply (subst (asm) (1) bisim_sym)
              apply (drule bisim_choices_Read)
               apply simp
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule SC)
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI2)
                apply force
               apply simp_all
               apply auto
              apply (rule bc_base)
              apply (intro exI conjI)
                 apply (rule refl)
                defer
              using bisim_sym apply blast+
              done
            subgoal
              apply (erule thin_rl)
              apply rotate_tac
              apply (subst (asm) (1) bisim_sym)
              apply (drule bisim_choices_Read)
               apply simp
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule SC)
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI2)
                apply force
               apply simp_all
               apply auto
              apply (rule bc_base)
              apply (intro exI conjI)
                 apply (rule refl)
                defer
              using bisim_sym apply blast+
              done
            done
          subgoal for op1'' p x
            apply hypsubst_thin
            apply (erule thin_rl)
            apply rotate_tac
            apply (subst (asm) bisim_sym)
            apply (drule bisim_choices_Write)
             apply auto
            apply (intro conjI exI)
             apply (rule step_comp_op_R_Out)
               apply (rule Write_in_choices_step)
               apply simp_all
            apply (metis (mono_tags, lifting) bc_base bisim_sym)
            done
          subgoal
            apply hypsubst_thin
            apply (erule thin_rl)
            apply rotate_tac
            apply (subst (asm) bisim_sym)
            apply (drule bisim_choices_Silent)
             apply auto
            apply (intro conjI exI)
             apply (rule step_comp_op_R_Tau)
               apply (rule Silent_in_choices_step)
               apply simp_all
            apply (metis (mono_tags, lifting) bc_base bisim_sym)
            done
          done
        done
      done
    done
  done

lemma bisim_scomp_op_cong:
  "op1 ~ op1' \<Longrightarrow>
   op2 ~ op2' \<Longrightarrow>
   op1 \<bullet> op2 ~ op1' \<bullet> op2'"
  unfolding scomp_op_def using bisim_comp_op_cong bisim_map_op by blast

subsubsection \<open>Congruence for weak bisim (wbisim)\<close>

lemma wbisim_choices_Read:
  "op \<approx> op' \<Longrightarrow>
   Read p f |\<in>| (choices op) \<Longrightarrow>
   \<exists> f' op'' op'''. (step Tau)\<^sup>*\<^sup>* op' op'' \<and> Read p f' |\<in>| (choices op'') \<and> (step Tau)\<^sup>*\<^sup>* (f' x) op''' \<and> f x \<approx> op'''"
  apply (drule Read_in_choices_step[where x=x])
  apply (drule step_wstep)
  apply (erule wbisim_wstep[OF wbisimulation_wbisim])
   apply assumption
  unfolding wstep_def
  apply auto
  apply (erule step_choicesE)
    apply auto
  apply (erule step_choicesE)
    apply auto
  done

lemma wbisim_choices_Write:
  "op1 \<approx> op' \<Longrightarrow>
   Write op1' p x |\<in>| (choices op1) \<Longrightarrow>
   \<exists> op'''' op'' op'''. (step Tau)\<^sup>*\<^sup>* op' op'' \<and> Write op''' p x |\<in>| (choices op'') \<and> (step Tau)\<^sup>*\<^sup>* op''' op'''' \<and> op'''' \<approx> op1'"
  apply (drule Write_in_choices_step)
  apply (drule step_wstep)
  apply (erule wbisim_wstep[OF wbisimulation_wbisim])
   apply assumption
  unfolding wstep_def
  apply auto
  apply (erule step_choicesE)
    apply auto
  apply (erule step_choicesE)
    apply auto
  using wbisim_sym apply blast
  done

lemma wbisim_choices_Silent:
  "op1 \<approx> op' \<Longrightarrow>
   Silent op1' |\<in>| (choices op1) \<Longrightarrow>
   (\<exists> op'''' op'' op'''. (step Tau)\<^sup>*\<^sup>* op' op'' \<and> Silent op''' |\<in>| (choices op'') \<and> (step Tau)\<^sup>*\<^sup>* op''' op'''' \<and> op'''' \<approx> op1') \<or> op1' \<approx> op'"
  apply (drule Silent_in_choices_step)
  apply (drule step_wstep)
  apply (erule wbisim_wstep[OF wbisimulation_wbisim])
   apply assumption
  unfolding wstep_def
  apply auto
  subgoal
    apply (erule step_choicesE)
      apply auto
    apply (erule step_choicesE)
      apply auto
    using wbisim_sym apply blast
    done
  subgoal
    by (metis IO.simps(6) IO.simps(8) cin.rep_eq converse_rtranclpE rtranclp.rtrancl_refl step_choicesE wbisim_sym)
  subgoal
    by (metis IO.simps(6) IO.simps(8) cin.rep_eq converse_rtranclpE rtranclp.rtrancl_refl step_choicesE wbisim_sym)
  subgoal
    by (metis IO.simps(6) IO.simps(8) cin.rep_eq converse_rtranclpE rtranclp.rtrancl_refl step_choicesE wbisim_sym)
  done

lemma step_comp_op_L_Tau_start[intro]:
  "(step Tau)\<^sup>*\<^sup>* op1 op1' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (comp_op wire buf op1 op2) (comp_op wire buf op1' op2)"
  apply (induct op1 op1' rule: rtranclp.induct)
   apply simp
  apply (meson rtranclp.simps step_comp_op_L_Tau)
  done

lemma step_comp_op_R_Tau_start[intro]:
  "(step Tau)\<^sup>*\<^sup>* op2 op2' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (comp_op wire buf op1 op2) (comp_op wire buf op1 op2')"
  apply (induct op2 op2' rule: rtranclp.induct)
   apply simp
  apply (meson rtranclp.simps step_comp_op_R_Tau)
  done

lemma wbisim_comp_op_cong:
  "op1 \<approx> op1' \<Longrightarrow>
   op2 \<approx> op2' \<Longrightarrow>
   comp_op wire buf op1 op2 \<approx> comp_op wire buf op1' op2'"
  apply (coinduction arbitrary: op1 op2 op1' op2' buf rule: wbisim_coinduct_upto)
  subgoal for op1 op2 op1' op2' buf
    unfolding wsim_def
    apply (intro conjI impI allI)
    subgoal for io op
      apply (rotate_tac 2)
      apply (induct io "comp_op wire buf op1 op2" op arbitrary: buf op1 op2 op1' op2' pred: step)
         apply (subst (asm) comp_op_code, simp)
        apply (subst (asm) comp_op_code, simp)
       apply (subst (asm) comp_op_code, simp)
      subgoal for op ops io op' buf op1 op2 op1' op2'
        apply auto
        apply (subst (asm) (5) comp_op_code)
        apply (simp add: Set.filter_def ranI image_iff bex_Un split: option.splits)
        apply (elim exE bexE disjE)
        subgoal for op'
          apply (cases op')
          subgoal for p f
            apply simp
            apply auto
            subgoal for x
              apply (erule thin_rl)
              apply hypsubst_thin
              apply (drule wbisim_choices_Read[where x=x])
               apply simp
              apply auto
              subgoal for f' op'' op'''
                apply (rule exI[of _ "comp_op wire buf op''' op2'"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base)
                unfolding wstep_def
                apply auto
                apply (rule relcomppI)
                 apply (rule step_comp_op_L_Tau_start)
                 apply assumption
                apply (rule relcomppI)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule Read_in_choices_step)
                   apply simp_all
                apply blast
                done
              done
            done
          subgoal for op1'' p x
            apply (auto split: option.splits)
            subgoal 
              apply (erule thin_rl)
              apply hypsubst_thin
              apply (drule wbisim_choices_Write)
               apply simp
              apply auto
              subgoal for op'''' op'' op'''
                apply (rule exI[of _ "comp_op wire buf op'''' op2'"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
                unfolding wstep_def
                apply auto
                apply (rule relcomppI)
                 apply (rule step_comp_op_L_Tau_start)
                 apply assumption
                apply (rule relcomppI)
                 apply (rule step_comp_op_L_Out)
                    apply (rule Write_in_choices_step)
                    apply simp
                   apply blast+
                done
              done
            subgoal for q
              apply (erule thin_rl)
              apply hypsubst_thin
              apply (drule wbisim_choices_Write)
               apply simp
              apply auto
              subgoal for op'''' op'' op'''
                apply (rule exI[of _ "comp_op wire (BENQ q x buf) op'''' op2'"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
                apply (rule rtranclp_trans)
                 apply (rule step_comp_op_L_Tau_start)
                 apply assumption
                apply (rule converse_rtranclp_into_rtranclp)
                 apply (rule step_Tau_comp_op_L)
                    apply simp_all
                 apply (rule Write_in_choices_step)
                 apply simp
                apply blast
                done
              done
            done
          subgoal
            by auto
          subgoal for op
            apply auto
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (drule wbisim_choices_Silent)
             apply simp
            apply auto
            subgoal for op'''' op'' op'''
              apply (rule exI[of _ "comp_op wire buf op'''' op2'"])
              apply (intro conjI[rotated])
               apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
              apply (meson Silent_in_choices_step cin.rep_eq rtranclp.rtrancl_into_rtrancl rtranclp_trans step_comp_op_L_Tau_start)
              done
            subgoal
              by (metis (mono_tags, lifting) rtranclp.rtrancl_refl wbc_base)
            done
          done
        subgoal for op
          apply (cases op)
             apply auto
          subgoal for p f x
            apply (erule thin_rl)
            apply hypsubst_thin
            apply rotate_tac
            apply (drule wbisim_choices_Read[where x=x])
             apply simp
            apply auto
            subgoal for f' op'' op'''
              apply (rule exI[of _ "comp_op wire buf op1' op'''"])
              apply (intro conjI[rotated])
               apply (metis (mono_tags, lifting) wbc_base)
              unfolding wstep_def
              apply auto
              apply (rule relcomppI)
               apply (rule step_comp_op_R_Tau_start)
               apply assumption
              apply (rule relcomppI)
               apply (rule step_comp_op_R_Inp)
                  apply (rule Read_in_choices_step)
                  apply simp
                 apply blast+
              done
            done
          subgoal for p f
            apply (auto split: if_splits)
            subgoal
              apply (erule thin_rl)
              apply hypsubst_thin
              apply rotate_tac
              apply (drule wbisim_choices_Read[where x="BHD p buf"])
               apply simp
              apply auto
              subgoal for f' op'' op'''
                apply (rule exI[of _ "comp_op wire (BTL p buf) op1' op'''"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base)
                unfolding wstep_def
                apply (smt (verit, ccfv_SIG) Read_in_choices_step cin.rep_eq rtranclp.rtrancl_into_rtrancl rtranclp_trans step_Tau_comp_op_R step_comp_op_R_Tau_start)
                done
              done
            subgoal for x
              apply (erule thin_rl)
              apply hypsubst_thin
              apply rotate_tac
              apply (drule wbisim_choices_Read[where x=x])
               apply simp
              apply auto
              subgoal for f' op'' op'''
                apply (rule exI[of _ "comp_op wire buf op1' op'''"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base)
                unfolding wstep_def
                apply auto
                apply (rule relcomppI)
                 apply (rule step_comp_op_R_Tau_start)
                 apply assumption
                apply (rule relcomppI)
                 apply (rule step_comp_op_R_Inp)
                    apply (rule Read_in_choices_step)
                    apply simp
                   apply blast+
                done
              done
            done
          subgoal for op2 p x
            apply (erule thin_rl)
            apply hypsubst_thin
            apply rotate_tac
            apply (drule wbisim_choices_Write)
             apply auto
            subgoal for op'''' op'' op'''
              apply (rule exI[of _ "comp_op wire buf op1' op''''"])
              apply (intro conjI[rotated])
               apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
              unfolding wstep_def
              apply auto
              apply (smt (verit, ccfv_SIG) Write_in_choices_step cin.rep_eq relcompp_apply step_comp_op_R_Out step_comp_op_R_Tau_start)
              done
            done
          subgoal for op
            apply (erule thin_rl)
            apply hypsubst_thin
            apply rotate_tac
            apply (drule wbisim_choices_Silent)
             apply auto
            subgoal for op'''' op'' op'''
              apply (rule exI[of _ "comp_op wire buf op1' op''''"])
              apply (intro conjI[rotated])
               apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
              apply (metis Silent_in_choices_step cin.rep_eq rtranclp.simps rtranclp_trans step_comp_op_R_Tau_start)
              done
            subgoal
              by (metis (mono_tags, lifting) rtranclp.rtrancl_refl wbc_base)
            done
          done
        done
      done
    subgoal for io op12
      apply (rotate_tac 2)
      apply (induct io "comp_op wire buf op1' op2'" op12 arbitrary: buf op1 op2 op1' op2' pred: step)
         apply (subst (asm) comp_op_code, simp)
        apply (subst (asm) comp_op_code, simp)
       apply (subst (asm) comp_op_code, simp)
      subgoal for op ops io op' buf op1' op2' op1 op2
        apply auto
        apply (subst (asm) (5) comp_op_code)
        apply (simp add: Set.filter_def ranI image_iff bex_Un split: option.splits)
        apply (elim exE bexE disjE)
        subgoal for op'
          apply simp
          apply (cases op')
          subgoal for p f
            apply simp
            apply auto
            subgoal for x
              apply (erule thin_rl)
              apply hypsubst_thin
              apply (drule wbisim_sym)
              apply rotate_tac
              apply (drule wbisim_choices_Read[where x=x])
               apply auto
              subgoal for f' op'' op'''
                apply (rule exI[of _ "comp_op wire buf op''' op2"])
                apply (intro conjI[rotated])
                 apply (smt (verit, ccfv_threshold) wbc_base wbisim_sym wbisim_trans)
                unfolding wstep_def
                apply auto
                apply (rule relcomppI)
                 apply (rule step_comp_op_L_Tau_start)
                 apply assumption
                apply (rule relcomppI)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule Read_in_choices_step)
                   apply simp_all
                apply blast
                done
              done
            done
          subgoal for op1'' p x
            apply (auto split: option.splits)
            subgoal
              apply hypsubst_thin
              apply (erule thin_rl)
              apply (drule wbisim_sym)
              apply rotate_tac
              apply (drule wbisim_choices_Write)
               apply auto
              subgoal for op'''' op'' op'''
                apply (rule exI[of _ "comp_op wire buf op'''' op2"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base wbisim_refl wbisim_sym)
                unfolding wstep_def
                apply auto
                apply (rule relcomppI)
                 apply (rule step_comp_op_L_Tau_start)
                 apply assumption
                apply (rule relcomppI)
                 apply (rule step_comp_op_L_Out)
                    apply (rule Write_in_choices_step)
                    apply simp
                   apply blast+
                done
              done
            subgoal for q
              apply hypsubst_thin
              apply (erule thin_rl)
              apply (drule wbisim_sym)
              apply rotate_tac
              apply (drule wbisim_choices_Write)
               apply auto
              subgoal for op'''' op'' op'''
                apply (rule exI[of _ "comp_op wire (BENQ q x buf) op'''' op2"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base wbisim_refl wbisim_sym)
                unfolding wstep_def
                apply (rule rtranclp_trans)
                 apply (rule step_comp_op_L_Tau_start)
                 apply assumption
                apply (rule converse_rtranclp_into_rtranclp)
                 apply (rule step_Tau_comp_op_L)
                    apply simp_all
                 apply (rule Write_in_choices_step)
                 apply simp
                apply blast
                done
              done
            done
          subgoal
            by auto
          subgoal for op1''
            apply auto
            apply hypsubst_thin
            apply (erule thin_rl)
            apply (drule wbisim_sym)
            apply rotate_tac
            apply (drule wbisim_choices_Silent)
             apply auto
            subgoal for op'''' op'' op'''
              apply (rule exI[of _ "comp_op wire buf op'''' op2"])
              apply (intro conjI[rotated])
               apply (metis (mono_tags, lifting) wbc_base wbisim_refl wbisim_sym)
              unfolding wstep_def
              apply (meson Silent_in_choices_step cin.rep_eq rtranclp.rtrancl_into_rtrancl rtranclp_trans step_comp_op_L_Tau_start)
              done
            subgoal
              by (metis (mono_tags, lifting) rtranclp.rtrancl_refl wbc_base wbisim_sym)
            done
          done
        subgoal for op
          apply (cases op)
             apply auto
          subgoal for f p x
            apply hypsubst_thin
            apply (erule thin_rl)
            apply rotate_tac
            apply (drule wbisim_sym)
            apply (drule wbisim_choices_Read[where x=x, of op2'])
             apply auto
            subgoal for f' op'' op'''
              apply (rule exI[of _ "comp_op wire buf op1 op'''"])
              apply (intro conjI[rotated])
               apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
              unfolding wstep_def
              apply auto
              apply (smt (verit, ccfv_SIG) Read_in_choices_step cin.rep_eq relcompp_apply step_comp_op_R_Inp step_comp_op_R_Tau_start)
              done
            done
          subgoal for p x
            apply (auto split: if_splits)
            subgoal
              apply hypsubst_thin
              apply (erule thin_rl)
              apply rotate_tac
              apply (drule wbisim_sym)
              apply (drule wbisim_choices_Read[where x="BHD p buf", of op2'])
               apply auto
              subgoal for f' op'' op'''
                apply (rule exI[of _ "comp_op wire (BTL p buf) op1 op'''"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
                apply (smt (verit, best) Read_in_choices_step cin.rep_eq rtranclp.rtrancl_into_rtrancl rtranclp_trans step_Tau_comp_op_R step_comp_op_R_Tau_start)
                done
              done
            subgoal for x
              apply hypsubst_thin
              apply (erule thin_rl)
              apply rotate_tac
              apply (drule wbisim_sym)
              apply (drule wbisim_choices_Read[where x=x, of op2'])
               apply auto
              subgoal for f' op'' op'''
                apply (rule exI[of _ "comp_op wire buf op1 op'''"])
                apply (intro conjI[rotated])
                 apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
                unfolding wstep_def
                apply auto
                apply (smt (verit, ccfv_SIG) Read_in_choices_step cin.rep_eq relcompp_apply step_comp_op_R_Inp step_comp_op_R_Tau_start)
                done
              done
            done
          subgoal for op2'' p x
            apply hypsubst_thin
            apply (erule thin_rl)
            apply rotate_tac
            apply (drule wbisim_sym)
            apply (drule wbisim_choices_Write[of op2'])
             apply auto
            subgoal for op'''' op'' op'''
              apply (rule exI[of _ "comp_op wire buf op1 op''''"])
              apply (intro conjI[rotated])
               apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
              unfolding wstep_def
              apply auto
              apply (smt (verit, ccfv_threshold) Write_in_choices_step cin.rep_eq relcompp_apply step_comp_op_R_Out step_comp_op_R_Tau_start)
              done
            done
          subgoal
            apply hypsubst_thin
            apply (erule thin_rl)
            apply rotate_tac
            apply (drule wbisim_sym)
            apply (drule wbisim_choices_Silent[of op2'])
             apply auto
            subgoal for op'''' op'' op'''
              apply (rule exI[of _ "comp_op wire buf op1 op''''"])
              apply (intro conjI[rotated])
               apply (metis (mono_tags, lifting) wbc_base wbisim_sym)
              apply (meson Silent_in_choices_step cin.rep_eq rtranclp.rtrancl_into_rtrancl rtranclp_trans step_comp_op_R_Tau_start)
              done
            subgoal
              by (metis (mono_tags, lifting) rtranclp.rtrancl_refl wbc_base wbisim_sym)
            done
          done
        done
      done
    done
  done

lemma wbisim_scomp_op_cong:
  "op1 \<approx> op1' \<Longrightarrow>
   op2 \<approx> op2' \<Longrightarrow>
   op1 \<bullet> op2 \<approx> op1' \<bullet> op2'"
  unfolding scomp_op_def using wbisim_comp_op_cong wbisim_map_op by blast


section \<open>loop_op: Loop/Feedback\<close>
corec loop_op :: "('op \<rightharpoonup> 'ip) \<Rightarrow> ('ip \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip, 'op, 'd) op \<Rightarrow> ('ip, 'op, 'd) op" where
  "loop_op wire buf op = Choice (cimage (\<lambda> op. case op of
     Read p f \<Rightarrow> (if p \<in> ran wire then Silent (loop_op wire (BTL p buf) (f (BHD p buf))) else Read p (\<lambda> x. loop_op wire buf (f x)))
   | Write op' p x \<Rightarrow> (case wire p of None \<Rightarrow> Write (loop_op wire buf op') p x | Some q \<Rightarrow> Silent (loop_op wire (BENQ q x buf) op'))
   | Silent op' \<Rightarrow> Silent (loop_op wire buf op')
   ) (sound_reads wire buf (choices op)))"


subsection \<open>Simp rules\<close>
lemma loop_op_simps[simp]:
  "loop_op wire buf (Read p1 f1) = (if p1 \<in> ran wire then (if buf p1 = [] then Choice {||} else Choice {| Silent (loop_op wire (BTL p1 buf) (f1 (BHD p1 buf))) |} )
   else Choice {|Read p1 (\<lambda> x. loop_op wire buf (f1 x)) |})"
  "loop_op wire buf (Write op' p2 x) = (case wire p2 of None \<Rightarrow> Choice {|Write (loop_op wire buf op') p2 x  |} |
   Some q \<Rightarrow> Choice {|Silent (loop_op wire (BENQ q x buf) op')|})"
  "loop_op wire buf (Silent op') = Choice {|Silent (loop_op wire buf op') |}"
  "loop_op wire buf (Choice ops) = Choice (cimage (\<lambda> op. case op of
     Read p f \<Rightarrow> (if p \<in> ran wire then Silent (loop_op wire (BTL p buf) (f (BHD p buf))) else Read p (\<lambda> x. loop_op wire buf (f x)))
   | Write op' p x \<Rightarrow> (case wire p of None \<Rightarrow> Write (loop_op wire buf op') p x | Some q \<Rightarrow> Silent (loop_op wire (BENQ q x buf) op'))
   | Silent op' \<Rightarrow> Silent (loop_op wire buf op')
   ) (sound_reads wire buf (choices (Choice ops))))"
  by (subst loop_op.code, (auto simp add: image_iff Set.filter_def split: option.splits if_splits))+

lemma loop_op_not_Read[simp]:
  "\<not> is_Read (loop_op wire buf op)"
  by (subst loop_op.code, simp)
lemma loop_op_not_Write[simp]:
  "\<not> is_Write (loop_op wire buf op)"
  by (subst loop_op.code, simp)
lemma loop_op_not_Silent[simp]:
  "\<not> is_Silent (loop_op wire buf op)"
  by (subst loop_op.code, simp)
lemma loop_op_Choice[simp]:
  "is_Choice (loop_op wire buf op)"
  by (subst loop_op.code, simp)

definition feedback_op ( "_ \<up>" [66] 65) where
  "feedback_op op = map_op projl projl (loop_op (case_sum (\<lambda> _. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (\<lambda> _. [])) op)"

lemma in_feedback_wire[simp]:
  "p \<in> ran (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) \<longleftrightarrow> (\<exists> p'. p = Inr p' \<and> p' \<notin> defaults)"
  apply (cases p; simp add:  ran_def split: sum.splits if_splits)
  apply (metis Inl_Inr_False Inr_inject sumE)
  done

subsection \<open>Step properties\<close>

lemma step_loop_op_gen:
  "step io (loop_op wire buf op) op' \<Longrightarrow>
   (\<exists>p x. p \<notin> ran wire \<and> io = Inp p x \<and> (\<exists> op''. op' = loop_op wire buf op'' \<and> step io op op'')) \<or>
   (\<exists>p x. wire p = None \<and> io = Out p x \<and> (\<exists> op''. op' = loop_op wire buf op'' \<and> step io op op'')) \<or>
   (io = Tau \<and> (\<exists> op''. op' = loop_op wire buf op'' \<and> step io op op'')) \<or>
   (io = Tau \<and> (\<exists> op'' p x. p \<in> ran wire \<and> op' = loop_op wire (BTL p buf) op'' \<and> step (Inp p x) op op'' \<and> buf p \<noteq> [] \<and> BHD p buf = x)) \<or>
   (io = Tau \<and> (\<exists> op'' p q x. wire p = Some q \<and> op' = loop_op wire (BENQ q x buf) op'' \<and> step (Out p x) op op''))"
  apply (erule step_choicesE)
  subgoal
    apply (subst (asm) (1) loop_op.code)
    apply (auto 10 10 simp add: ran_def split: option.splits if_splits sum.splits op.splits)
    done
  subgoal
    apply (subst (asm) (1) loop_op.code)
    apply (auto 10 10 simp add: ran_def split: option.splits if_splits sum.splits op.splits)
    done
  subgoal 
    apply (subst (asm) (1) loop_op.code)
    apply (fastforce simp add: ran_def split: option.splits if_splits sum.splits op.splits)
    done
  done

lemma step_loop_op_elim:
  assumes "step io (loop_op wire buf op) op'"
  obtains
    p x op'' where "p \<notin> ran wire" "io = Inp p x" "op' = loop_op wire buf op''" "step io op op''" |
    p x op'' where "wire p = None" "io = Out p x" "op' = loop_op wire buf op''" "step io op op''" |
    op'' where "io = Tau" "op' = loop_op wire buf op''" "step io op op''" |
    op'' p x where "io = Tau" "p \<in> ran wire" "op' = loop_op wire (BTL p buf) op''" "step (Inp p x) op op''" "buf p \<noteq> []" "BHD p buf = x" |
    op'' p q x where "io = Tau" "wire p = Some q" "op' = loop_op wire (BENQ q x buf) op''" "step (Out p x) op op''"
  using assms apply -
  apply (drule step_loop_op_gen)
  apply auto
  done

lemma step_loop_op:
  "step io (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) buf op) op' \<Longrightarrow>
   (\<exists>p x. io = Inp (Inl p) x \<and> (\<exists> op''. op' = loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) buf op'' \<and> step io op op'')) \<or>
   (\<exists>p x. io = Out (Inl p) x \<and> (\<exists> op''. op' = loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) buf op'' \<and> step io op op'')) \<or>
   (io = Tau \<and> (\<exists> op''. op' = loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) buf op'' \<and> step io op op'')) \<or>
   (io = Tau \<and> (\<exists> op'' p x. p \<notin> defaults \<and> op' = loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (BTL (Inr p) buf) op'' \<and> step (Inp (Inr p) x) op op'' \<and> buf (Inr p) \<noteq> [] \<and> BHD (Inr p) buf = x)) \<or>
   (io = Tau \<and> (\<exists> op'' p x. p \<notin> defaults \<and> op' = loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (BENQ (Inr p) x buf) op'' \<and> step (Out (Inr p) x) op op'')) \<or>
   (\<exists>p x. p \<in> defaults \<and> io = Inp (Inr p) x \<and> (\<exists> op''. op' = loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) buf op'' \<and> step io op op'')) \<or>
   (\<exists>p x. p \<in> defaults \<and> io = Out (Inr p) x \<and> (\<exists> op''. op' = loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) buf op'' \<and> step io op op''))"
  apply (erule step_choicesE)
  subgoal for p f x
    apply (cases p)
    subgoal for lp
      apply (subst (asm) (1) loop_op.code)
      apply auto
      subgoal for op
        apply (cases op)
           apply (auto 10 10 simp add: ran_def split: if_splits sum.splits)
        done
      done
    subgoal for rp
      apply (subst (asm) (1) loop_op.code)
      apply auto
      subgoal for op
        apply (cases op)
           apply (auto 10 10 simp add: ran_def split: if_splits sum.splits)
        done
      subgoal for op
        apply (cases op)
           apply (auto 10 10 simp add: ran_def split: if_splits sum.splits)
        done
      done
    done
  subgoal for p x
    apply (subst (asm) (1) loop_op.code)
    apply auto
    subgoal for op
      apply (cases op)
         apply (auto 10 10 simp add: ran_def split: if_splits sum.splits)
      done
    subgoal for op
      apply (cases op)
         apply (auto 10 10 simp add: ran_def split: if_splits sum.splits)
      done
    done
  subgoal 
    apply (subst (asm) (1) loop_op.code)
    apply auto
    subgoal for op
      apply (cases op)
         apply (auto 10 10 simp add: ran_def split: if_splits sum.splits)
      done
    done
  done

(* lemma step_Inp_Inl_loop_op[intro]:
  "step (Inp (Inl p) x) op op' \<Longrightarrow>
   step (Inp (Inl p) x) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal for p' f
    apply clarsimp
    apply hypsubst_thin
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Read _ _"])
      apply simp_all
     apply (intro conjI)
      apply assumption
     apply auto
     apply (smt (verit) mem_Collect_eq o_apply option.sel option.simps(3) ran_def sum.case_eq_if sum.simps(4))
    apply (smt (verit) mem_Collect_eq o_apply option.sel option.simps(3) ran_def sum.case_eq_if sum.simps(4))
    done
  done *)

(* lemma step_Out_Inr_loop_op[intro]:
  "step (Out (Inr p) x) op op' \<Longrightarrow>
   buf' = BENQ (Inr p) x buf \<Longrightarrow>
   step Tau (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf' op')"
  apply hypsubst_thin
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  apply (rule SC[rotated])
   apply (rule ST)
  apply (rule cimage_eqI[of _ _ "Write _ (Inr p) _"])
   apply simp_all
  done
 *)
(* lemma step_Inp_Inr_loop_op[intro]:
  "step (Inp (Inr p) (BHD (Inr p) buf)) op op' \<Longrightarrow>
   buf (Inr p) \<noteq> [] \<Longrightarrow>
   buf' = BTL (Inr p) buf \<Longrightarrow>
   step Tau (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf' op')"
  apply hypsubst_thin
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  apply (rule SC[rotated])
   apply (rule ST)
  apply (rule cimage_eqI[of _ _ ])
   apply auto
  apply (metis comp_apply sum.simps(6) ranI)
  done
 *)

lemma step_double_loop_1:
  "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1) (op :: (('a + 'd) + 'e, ('b + 'd) + 'e, 'c) op))))) op' \<Longrightarrow>
   \<exists> (op'' :: (('a + 'd) + 'e, ('b + 'd) + 'e, 'c) op) buf1' buf2'.
   op' = (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1') op''))))  \<and>
   step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)))
   (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2' buf1')) (map_op reassoc reassoc op'')))"
  unfolding feedback_op_def
  apply (drule step_map_op_inv)
  apply auto(* 
  apply (drule step_loop_op)
  apply auto
  subgoal for p op'' x
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io'
      apply (cases io')
        apply auto
      apply (drule step_loop_op)
      apply auto
      apply hypsubst_thin
      apply (intro exI conjI[rotated])
       apply (rule step_map_op)
        apply (rule step_Inp_Inl_loop_op)
        apply (rule step_map_op)
         apply auto
      done
    done
  subgoal for p op'' x
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io'
      apply (cases io')
        apply auto
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      apply (intro exI conjI[rotated])
       apply (rule step_map_op)
        apply (rule step_Out_Inl_loop_op)
        apply (rule step_map_op)
         apply auto
      done
    done
  subgoal for op'
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io' op'
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      subgoal
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule step_map_op)
          apply (rule step_Tau_loop_op_old)
          apply (rule step_map_op)
           apply auto
        done
      subgoal for op'' p
        apply hypsubst_thin
        apply (rule exI[of _op''])
        apply (rule exI[of _ "BTL p buf1"])
        apply (rule exI[of _ "buf2"])
        apply (intro conjI)
        subgoal
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply force
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply auto
          done
        subgoal
          apply (erule step_choicesE)
            apply auto
          subgoal for f
            apply hypsubst_thin
            apply (subst loop_op.code)
            apply simp
            apply (rule SC)
             apply (rule cimage_eqI)
              apply (rule refl)
             apply (rule cimage_eqI[of _ _ "Read (Inr (Inr p)) (\<lambda> x. map_op reassoc reassoc (f x))"])
              apply simp_all
             defer
             apply (rule step_map_op)
              apply simp
              apply (intro conjI impI)
               apply (rule ST')
               apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
            subgoal
              unfolding fun_upd_def
              apply (rule ext)
              apply (auto split: sum.splits)
              done
               apply auto
             apply (smt (verit, ccfv_SIG) BHD_def comp_apply old.sum.simps(6) ranI)
             apply (auto simp add: BHD_def simp flip: choices_map_op)
            apply (rule image_eqI[rotated])
             apply assumption
            apply auto
            done
          done
        done
      subgoal for op'' p x
        apply hypsubst_thin
        apply (rule exI[of _op''])
        apply (rule exI[of _ "BENQ p x buf1"])
        apply (rule exI[of _ "buf2"])
        apply (intro conjI)
        subgoal
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply force
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply auto
          done
        subgoal
          apply (erule step_choicesE)
            apply auto
          apply (subst loop_op.code)
          apply simp
          apply (rule SC)
           apply (rule cimage_eqI)
            apply (rule refl)
           apply (rule cimage_eqI[of _ _ "Write (map_op reassoc reassoc op'') (Inr (Inr p)) x"])
            apply simp_all
           defer
           apply (rule step_map_op[rotated, of _ _ _ Tau])
            apply simp
           apply (rule ST')
           apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
          subgoal
            unfolding fun_upd_def
            apply (rule ext)
            apply (auto split: sum.splits)
            done
           apply auto
          apply (auto simp flip: choices_map_op)
          apply (rule image_eqI[rotated])
           apply assumption
          apply auto
          done
        done
      done
    done
  subgoal for op'' p
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io op'''
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      subgoal for op'''
        apply hypsubst_thin
        apply (rule exI[of _ "op'''"])
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ "BTL p buf2"])
        apply auto
          apply (rule step_map_op[of Tau, rotated])
           apply simp_all
          apply (erule step_choicesE)
            apply auto
          subgoal for f
            apply (subst loop_op.code)
            apply simp
            apply (rule SC)
             apply (rule cimage_eqI[of _ _ "Read (Inr (Inl p)) (\<lambda> x. map_op reassoc reassoc (f x))"])
              apply (rule refl)
             apply (auto simp flip: choices_map_op)
              apply (rule image_eqI[rotated])
               apply assumption
              apply auto
            subgoal
              by (metis (no_types, lifting) comp_apply old.sum.simps(6) ranI)
            done
          done
        done
      done
  subgoal for op'' p x
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io op'''
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      subgoal for op'''
        apply hypsubst_thin
        apply (rule exI[of _ "op'''"])
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ "BENQ p x buf2"])
        apply auto
          apply (rule step_map_op[of Tau, rotated])
           apply simp_all
          apply (erule step_choicesE)
            apply auto
          apply (subst loop_op.code)
          apply simp
          apply (rule SC)
           apply (rule cimage_eqI[of _ _ "Write _  (Inr (Inl p)) x"])
            apply (rule refl)
           apply (auto simp flip: choices_map_op)
           apply (rule image_eqI[rotated])
            apply assumption
           apply auto
            done
          done
        done
      done *)
  oops

lemma step_double_loop_2:
  "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc (op :: (('a + 'd) + 'e, ('b + 'd) + 'e, 'c) op)))) op' \<Longrightarrow>
   \<exists> (op'' :: (('a + 'd) + 'e, ('b + 'd) + 'e, 'c) op) buf1' buf2'.
   op' = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2' buf1')) (map_op reassoc reassoc op''))  \<and>
   step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1) op))))
   (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1') op''))))"
  unfolding feedback_op_def
  apply (drule step_map_op_inv)
  apply auto
  oops(* 
  apply (drule step_loop_op)
  apply auto
  subgoal for p op'' x
    apply hypsubst_thin
    apply (rule exI[of _ "map_op assoc assoc op''"])
    apply (rule exI[of _ buf1])
    apply (rule exI[of _ buf2])
    apply auto
    subgoal
      apply (rule arg_cong[where f="map_op projl projl"])
      apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
       apply (auto simp add: op.map_comp op.map_id)
      done
    subgoal
      apply (rule step_map_op[of "Inp (Inl p) x"])
       apply auto
      apply (erule step_choicesE)
        apply simp_all
      apply (subst loop_op.code)
      apply simp
      subgoal for p' f
        apply clarsimp
        apply hypsubst_thin
        apply (rule SC)
         apply (rule cimage_eqI)
          apply simp_all
         apply (simp flip: choices_map_op)
         apply (intro conjI)
          apply (subst loop_op.code)
          apply (simp flip: choices_map_op add: Set.filter_def)
          apply (rule image_eqI)
           apply (rule refl)
          apply simp
          apply (intro exI[of _  "Read (Inl (Inl p)) (\<lambda> x. map_op assoc assoc (f x))"] conjI)
            apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc", where a="Read (Inl (Inl p)) (\<lambda> x. map_op assoc assoc (f x))", symmetric, simplified])
        using map_op_reassoc_inj apply force
            apply simp
        subgoal
          unfolding comp_def
          apply auto
          apply (rule image_eqI[rotated])
           apply assumption
          subgoal for x
            apply (cases x)
               apply auto
            apply (rule ext)
            apply auto
            apply (simp add: op.map_comp)
            done
          done
           apply (auto simp add: ran_def sum.case_eq_if)
        done
      done
    done
  subgoal for p op'' x
    apply hypsubst_thin
    apply (rule exI[of _ "map_op assoc assoc op''"])
    apply (rule exI[of _ buf1])
    apply (rule exI[of _ buf2])
    apply auto
    subgoal
      apply (rule arg_cong[where f="map_op projl projl"])
      apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
       apply (auto simp add: op.map_comp op.map_id)
      done
    subgoal
      apply (rule step_map_op[of "Out (Inl p) x"])
       apply auto
      apply (erule step_choicesE)
        apply simp_all
      apply (subst loop_op.code)
      apply (rule SC)
       apply (rule cimage_eqI)
        apply simp_all
       apply (simp flip: choices_map_op)
       apply (intro conjI)
        apply (subst loop_op.code)
        apply (simp flip: choices_map_op add: Set.filter_def)
        apply (rule image_eqI)
         apply (rule refl)
        apply simp
        apply (intro exI[of _  "Write (map_op assoc assoc op'') (Inl (Inl p)) x"] conjI)
          apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc", where a="Write (map_op assoc assoc op'') (Inl (Inl p)) x", symmetric, simplified])
      using map_op_reassoc_inj apply force
          apply simp
      subgoal
        unfolding comp_def
        apply auto
        apply (rule image_eqI[rotated])
         apply assumption
        subgoal for x
          apply (cases x)
             apply (auto simp add: op.map_comp)
          done
        done
         apply (auto simp add: ran_def sum.case_eq_if)
      done
    done
  subgoal for op''
    apply hypsubst_thin
    apply (rule exI[of _ "map_op assoc assoc op''"])
    apply (rule exI[of _ buf1])
    apply (rule exI[of _ buf2])
    apply auto
    subgoal
      apply (rule arg_cong[where f="map_op projl projl"])
      apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
       apply (auto simp add: op.map_comp op.map_id)
      done
    subgoal
      apply (rule step_map_op[of "Tau"])
       apply auto
      apply (erule step_choicesE)
        apply simp_all
      apply (subst loop_op.code)
      apply (rule SC)
       apply (rule cimage_eqI)
        apply simp_all
       apply (simp flip: choices_map_op)
       apply (intro conjI)
        apply (subst loop_op.code)
        apply (simp flip: choices_map_op add: Set.filter_def)
        apply (rule image_eqI)
         apply (rule refl)
        apply simp
        apply (intro exI[of _  "Silent (map_op assoc assoc op'')"] conjI)
          apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc", where a="Silent (map_op assoc assoc op'')", symmetric, simplified])
      using map_op_reassoc_inj apply force
          apply simp
      subgoal
        unfolding comp_def
        apply auto
        apply (rule image_eqI[rotated])
         apply assumption
        subgoal for x
          apply (cases x)
             apply (auto simp add: op.map_comp)
          done
        done
         apply (auto simp add: ran_def sum.case_eq_if)
      done
    done
  subgoal for op'' p
    apply hypsubst_thin
    apply (cases p; simp; hypsubst_thin)
    subgoal for lp
      apply (rule exI[of _ "map_op assoc assoc op''"])
      apply (rule exI[of _ buf1])
      apply (rule exI[of _ "BTL lp buf2"])
      apply auto
      subgoal
        apply (rule arg_cong[where f="map_op projl projl"])
        apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
         apply (auto simp add: op.map_comp op.map_id)
        done
      subgoal
        apply (rule step_map_op[of "Tau"])
         apply auto
        apply (erule step_choicesE)
          apply simp_all
        subgoal for p f
          apply (subst loop_op.code)
          apply (rule SC)
           apply (rule cimage_eqI)
            apply (simp_all flip: choices_map_op)
           apply (intro conjI)
            apply (subst loop_op.code)
            apply (simp flip: choices_map_op add: Set.filter_def)
            apply (rule image_eqI)
             apply (rule refl)
            apply simp
            apply (intro exI[of _ "Read (Inl (Inr lp)) _"] conjI)
              apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc" and a="Read _ (\<lambda> x. map_op assoc assoc (f x))", symmetric, simplified])
          using map_op_reassoc_inj apply force
              apply simp_all
          subgoal
            unfolding comp_def
            apply auto
            apply (rule image_eqI[rotated])
             apply assumption
            subgoal for x
              apply (cases x)
                 apply auto
              apply (rule ext)
              apply auto
              apply (simp add: op.map_comp)
              done
            done
             apply (auto simp add: ran_def sum.case_eq_if)
          subgoal for x p'
            apply (cases p')
               apply auto
              done
          subgoal
            by (meson sum.disc(2) sum.sel(2))
          done
        done
      done
    subgoal for rp
      apply (rule exI[of _ "map_op assoc assoc op''"])
      apply (rule exI[of _ "BTL rp buf1"])
      apply (rule exI[of _ "buf2"])
      apply auto
      subgoal
        apply (rule arg_cong[where f="map_op projl projl"])
        apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
         apply (auto simp add: op.map_comp op.map_id)
          done
      subgoal
        apply (rule step_map_op[of "Tau"])
         apply auto
        apply (erule step_choicesE)
          apply simp_all
        subgoal for p f
          apply (rule step_Tau_loop_op_old)
          apply (subst loop_op.code)
          apply (rule step_map_op)
           apply (rule SC)
            apply (simp_all flip: Set.filter_def choices_map_op)
            apply (rule image_eqI)
             apply (rule refl)
            apply simp
            apply (intro conjI)
             apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc" and a="Read (Inr rp) (\<lambda> x. map_op assoc assoc (f x))", symmetric, simplified])
          using map_op_reassoc_inj apply force

          subgoal
            unfolding comp_def
            apply auto
            apply (rule image_eqI[rotated])
             apply assumption
            subgoal for x
              apply (cases x)
                 apply auto
              apply (rule ext)
              apply auto
              apply (simp add: op.map_comp)
              done
            done
            apply (auto simp add: ran_def sum.case_eq_if)
          subgoal for x
            apply (cases x)
               apply (auto split: sum.splits)
          subgoal
            apply (auto simp add: BHD_def)
            apply (meson sum.disc(2) sum.sel(2))
            done
        done
      done
    done
  done
  done
  subgoal for op'' p x
    apply hypsubst_thin
    apply (cases p; simp; hypsubst_thin)
    subgoal for lp
      apply (rule exI[of _ "map_op assoc assoc op''"])
      apply (rule exI[of _ buf1])
      apply (rule exI[of _ "BENQ lp x buf2"])
      apply auto
      subgoal
        apply (rule arg_cong[where f="map_op projl projl"])
        apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
         apply (auto simp add: op.map_comp op.map_id)
          done
      subgoal
        apply (rule step_map_op[of "Tau"])
         apply auto
        apply (erule step_choicesE)
          apply simp_all
        apply (subst loop_op.code)
        apply (rule SC)
         apply (rule cimage_eqI)
          apply (simp_all flip: choices_map_op)
         apply (intro conjI)
          apply (subst loop_op.code)
          apply (simp flip: choices_map_op add: Set.filter_def)
          apply (rule image_eqI)
           apply (rule refl)
          apply simp
          apply (intro exI[of _ "Write _ (Inl (Inr lp)) x"] conjI)
            apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc" and a="Write (map_op assoc assoc op'') (Inl (Inr lp))  x", symmetric, simplified])
        using map_op_reassoc_inj apply force
            apply simp_all
        subgoal
          unfolding comp_def
          apply auto
          apply (rule image_eqI[rotated])
           apply assumption
          subgoal for x
            apply (cases x)
               apply (auto simp add: op.map_comp)
            done
          done
         apply (auto simp add: ran_def sum.case_eq_if)
        done
      done
    subgoal for rp
      apply (rule exI[of _ "map_op assoc assoc op''"])
      apply (rule exI[of _ "BENQ rp x buf1"])
      apply (rule exI[of _ "buf2"])
      apply auto
      subgoal
        apply (rule arg_cong[where f="map_op projl projl"])
        apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
         apply (auto simp add: op.map_comp op.map_id)
          done
      subgoal
        apply (rule step_map_op[of "Tau"])
         apply auto
        apply (erule step_choicesE)
          apply simp_all
        apply (rule step_Tau_loop_op_old)
        apply (subst loop_op.code)
        apply (rule step_map_op)
         apply (rule SC)
          apply (simp_all flip: Set.filter_def choices_map_op)
          apply (rule image_eqI)
           apply (rule refl)
          apply simp
          apply (intro conjI)
           apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc" and a="Write (map_op assoc assoc op'') (Inr rp) x", symmetric, simplified])
        using map_op_reassoc_inj apply force
        subgoal
          unfolding comp_def
          apply auto
          apply (rule image_eqI[rotated])
           apply assumption
          subgoal for x
            apply (cases x)
               apply (auto simp add: op.map_comp)
            done
          done
          apply (auto simp add: ran_def sum.case_eq_if)
          done
        done
      done
    done *)

  subsection \<open>Congruence for strong bisim\<close>
lemma bisim_scomp_op_cong:
  "op ~ op' \<Longrightarrow>
   op\<up> ~ op'\<up>"
  oops

  subsection \<open>Congruence for weak bisim\<close>
lemma wbisim_scomp_op_cong:
  "op \<approx> op' \<Longrightarrow>
   op\<up> \<approx> op'\<up>"
  oops

  subsection \<open>Inputs of loop_op\<close>

lemma inputs_loop_op:
  "sub_op (Read p f) (loop_op wire buf op) n \<Longrightarrow> p \<in> (inputs op - ran wire)"
proof (induct p \<open>loop_op wire buf op\<close> arbitrary: buf op rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (auto simp add: loop_op.code)
next
  case (Read2 p p' f x d g)
  then show ?case by (auto simp add: loop_op.code)
next
  case (Write p p' op' x d g)
  then show ?case by (auto simp add: loop_op.code)
next
  case (Silent p op' d)
  then show ?case by (auto simp add: loop_op.code)
next
  case (Choice p ops d g)
  then show ?case 
    apply -
    apply (subst (asm) (2) loop_op.code)
    apply auto
    subgoal for op
      apply (cases op)
         apply (auto simp add: Read_choices_inputs split: if_splits option.splits)
      subgoal for _  _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (meson cin.rep_eq inputs_after_choices inputs_sub_op_Read sub_op_Read sub_op_Read_inputs)
        done
      subgoal for _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (meson cin.rep_eq inputs_after_choices inputs_sub_op_Read sub_op_Read sub_op_Read_inputs)
        done
      subgoal for _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (simp add: inputs_after_choices)
        done
      subgoal for _ _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (simp add: inputs_after_choices)
        done
      subgoal for _ n
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (simp add: inputs_after_choices)
        done
      done
    subgoal for op
      apply hypsubst_thin
      apply (cases op)
         apply (auto simp add: Read_choices_inputs split: if_splits option.splits; force?)+
      done
    done
qed

lemma inputs_loop_op_le:
  "inputs (loop_op wire buf op) \<subseteq> (inputs op - ran wire)"
  using inputs_loop_op by (metis inputs_sub_op_Read subsetI) 
lemma inputs_loop_op_le_alt[dest!]:
  "ca \<in> inputs (loop_op wirea bufa opa) \<Longrightarrow> ca \<in> inputs opa \<and> ca \<notin> ran wirea"
  using set_mp[OF inputs_loop_op_le, simplified] by fast 

subsection \<open>Outputs of loop_op\<close>

lemma outputs_loop_op:
  "sub_op (Write op' p x) (loop_op wire buf op) n \<Longrightarrow> p \<in> (outputs op - dom wire)"
proof (induct p \<open>loop_op wire buf op\<close> arbitrary: buf op rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (auto simp add: loop_op.code)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (auto simp add: loop_op.code)
next
  case (Silent p op' op2 y d)
  then show ?case by (auto simp add: loop_op.code)
next
  case (Choice p op2 y d ops)
  then show ?case 
    apply -
    apply -
    apply (subst (asm) (2) loop_op.code)
    apply auto
    subgoal for op
      apply (cases op)
         apply (auto simp add: Write_choices_outputs outputs_after_choices split: if_splits option.splits)
      subgoal for _  _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (meson cin.rep_eq outputs_after_choices outputs_sub_op_Write sub_op_Read sub_op_Write_outputs)
        done
      subgoal for _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (meson cin.rep_eq outputs_after_choices outputs_sub_op_Write sub_op_Read sub_op_Write_outputs)
        done
      subgoal for _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (simp add: outputs_after_choices)
        done
      subgoal for _ _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (simp add: outputs_after_choices)
        done
      subgoal for _  n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        apply (simp add: outputs_after_choices)
        done
      done
    subgoal for op
      apply (cases op)
         apply (auto simp add: Write_choices_outputs outputs_after_choices split: if_splits option.splits)
      subgoal for _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        done
      subgoal for _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        done
      subgoal for _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        done
      subgoal for _ _ _ _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        done
      subgoal for _ n
        apply hypsubst_thin
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
         apply assumption
        apply (auto del: disjCI)
        done
      done
    done
next
  case (Write2 p op' x)
  then show ?case by (auto simp add: loop_op.code)
qed

lemma outputs_loop_op_le:
  "outputs (loop_op wire buf op) \<subseteq> (outputs op - dom wire)"
  using outputs_loop_op by (metis outputs_sub_op_Write subsetI) 
lemma outputs_loop_op_le_alt[dest!]:
  "c \<in> outputs (loop_op wire buf op) \<Longrightarrow> c \<in> outputs op \<and> c \<notin> dom wire"
  using set_mp[OF outputs_loop_op_le, simplified] by force

section \<open>spin_op/end_op/silent_op/I_0\<close>
  \<comment> \<open>spin_op/end_op is I_0 in the BNA book\<close>
  \<comment> \<open>In the transition system this is a dead-lock\<close>

corec spin_op :: "('a, 'b, 'd) op" ("\<otimes>") where
  "spin_op = Choice (cimage (\<lambda> _. spin_op) (csingle ()))"

primcorec silent_op where
  "silent_op = Silent silent_op"

lemma finished_spin_op[simp]:
  "finished \<otimes>"
  apply coinduction
  apply (subst spin_op.code)
  apply auto
  done

lemma finished_end_op[simp]:
  "finished \<oslash>"
  by coinduction blast

lemma step_end_op[simp]: "step l \<oslash> t' = False"
  by auto

lemma spin_op_finished[simp]:
  "finished \<otimes>"
  apply coinduction
  apply (subst spin_op.code)
  apply (auto 0 0 simp add:  sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq; hypsubst_thin?)
  done

lemma choices_spin_op[simp]:
  "choices \<otimes> = {||}"
  by (simp add: finished_choices_empty)

lemma traces_end_op[simp]:
  "traces \<oslash> = {LNil}"
  by (auto simp: traces_def intro: finished.intros traced.intros step.intros elim: traced.cases)

lemma step_spin_op_no_label:
  "step io \<otimes> op \<Longrightarrow> False"
  using spin_op_finished step_not_finished by blast

lemma spin_op_parallel:
  "\<otimes> \<parallel> \<otimes> ~ \<otimes> "
  apply (coinduction rule: bisim_coinduct_upto)
  apply safe
  subgoal
    unfolding pcomp_op_def sim_def
    apply auto
    apply (subst (asm) comp_op_code)
    apply auto
    done
  subgoal
    unfolding pcomp_op_def sim_def
    apply auto
    using step_spin_op_no_label apply blast
    done
  done

lemma spin_op_silent_op:
  "\<otimes> \<approx> silent_op"
  apply (coinduction rule: wbisim_coinduct_upto)
  unfolding wsim_def
  apply auto
  subgoal
    using step_spin_op_no_label by blast
  subgoal
    apply (subst (asm) silent_op.code)
    apply auto
    apply hypsubst_thin
    by (metis (mono_tags, lifting) rtranclp.rtrancl_refl wbc_base wbc_sym)
  done

lemma spin_op_end_op:
  \<open>\<otimes> ~ \<oslash>\<close>
  by (simp add: choices_Choice_bisim)

section \<open>id_op/\<I>/I_m\<close>
  \<comment> \<open>id_op is I_m in the BNA paper\<close>

datatype (discs_sels) ('m, 'd) id_op_aux =
  id_Read_aux "'m" "'d \<Rightarrow> ('m \<Rightarrow> 'd buf)"
  | id_Write_aux "('m \<Rightarrow> 'd buf)" "'m" 'd 
  | id_Silent_aux "('m \<Rightarrow> 'd buf)"

abbreviation eval_id_op_aux where
  "eval_id_op_aux c aux \<equiv> (case aux of
    id_Read_aux p f \<Rightarrow> Read p (\<lambda>y. let buf = f y in c buf)
  | id_Write_aux buf q x \<Rightarrow> (Write (c buf) q x))"

corec id_op :: "_ \<Rightarrow> ('m :: {countable, defaults}, 'm, 'd) op" where
  "id_op buf = Choice (cimage (eval_id_op_aux id_op) (cUn 
    (cimage (\<lambda> p. id_Read_aux p (\<lambda> x. BENQ p x buf)) (cUNIV :: 'm cset)) 
    (cimage (\<lambda> p. id_Write_aux (BTL p buf) p (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: 'm cset)))))"

abbreviation id_empty_op ("\<I>") where
  "\<I> \<equiv> id_op (\<lambda> _. [])"

lemma id_op_code:
  "id_op buf = Choice (cUn 
    (cimage (\<lambda> p. Read p ((\<lambda> x. id_op (BENQ p x buf)))) (cUNIV :: 'm cset))
    (cimage (\<lambda> p. Write (id_op (BTL p buf)) p  (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: ('m :: {countable, defaults}) cset))))"
  apply (subst id_op.code)
  apply (unfold cimage_cUn cimage_cinsert op.inject)
  apply simp
  apply (rule arg_cong2[where f = cUn])
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: id_op_aux.splits op.splits option.splits)
  done

subsection \<open>Some basic properties id_op\<close>

lemma step_id_op_Inp:
  "step io (id_op buf) op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op' = id_op (BENQ p x buf) \<and> p \<notin> defaults"
  apply (induct io "id_op buf" op' arbitrary: buf rule: step.induct)
     apply simp_all
   apply (subst (asm) id_op_code)
   apply simp
  apply (subst (asm) (3) id_op_code)
  apply auto
  done

lemma step_id_op_Inp_elim:
  assumes  "step (Inp p x) (id_op buf) op'"
  obtains "op' = id_op (BENQ p x buf)" "p \<notin> defaults"
  apply atomize
  apply (meson assms step_id_op_Inp)
  done

lemma step_id_op_Out:
  "step io (id_op buf) op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   op' = id_op (BTL p buf) \<and> BHD p buf = x \<and> buf p \<noteq> [] \<and> p \<notin> defaults"
  apply (induct io "id_op buf" op' arbitrary: buf rule: step.induct)
     apply simp_all
   apply (subst (asm) id_op_code)
   apply simp
  apply (subst (asm) (3) id_op_code)
  apply auto
  done

lemma no_step_id_op_Tau[elim]:
  assumes \<open>step io (id_op buf) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (induct io \<open>id_op buf\<close> op arbitrary: buf rule: step.induct)
     apply simp_all
   apply (subst (asm) id_op_code)
   apply simp
  apply (subst (asm) (2) id_op_code)
  apply auto
  done

lemma step_id_op_cases:
  assumes \<open>step io (id_op buf) op\<close>
  obtains p x where \<open>io = Inp p x\<close> \<open>p \<notin> defaults\<close> \<open>op = id_op (BENQ p x buf)\<close>
  |       p x where \<open>io = Out p x\<close> \<open>p \<notin> defaults\<close> \<open>op = id_op (BTL p buf)\<close> \<open>BHD p buf = x\<close> \<open>buf p \<noteq> []\<close>
  apply atomize_elim
  using assms
  apply (rule step_choicesE)
    apply (subst (asm) id_op_code, simp)+
  done

lemma step_id_op_Read[intro!]:
  "p \<notin> defaults \<Longrightarrow> buf' = BENQ p x buf \<Longrightarrow> step (Inp p x) (id_op buf) (id_op buf')"
  apply (subst id_op_code)
  apply (rule SC)
   apply simp
   apply (rule disjI1)
   apply force+
  done

lemma step_id_op_Write[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> BHD p buf = x \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> buf' = BTL p buf \<Longrightarrow>
  step (Out p x) (id_op buf) (id_op buf')\<close>
  apply (subst id_op_code)
  apply (rule SC)
   apply simp
   apply (rule disjI2)
   apply force+
  done

lemma choices_id_op[simp]:
  "choices (id_op buf) = cUn (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda>x. id_op (buf(p := bulk_benq [x] (buf p))))) cUNIV)))
       (cUnion (cimage choices (cimage (\<lambda>p. Write (id_op (BTL p buf)) p (BHD p buf)) (cfilter (\<lambda>p. buf p \<noteq> []) cUNIV))))"
  apply (subst id_op_code)
  apply (simp add: BTL_def BENQ_def)
  done

lemma step_Inp_loop_op[intro!]:
  "step (Inp p x) op op' \<Longrightarrow>
   p \<notin> ran wire \<Longrightarrow>
   step (Inp p x) (loop_op wire buf op) (loop_op wire buf op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal for p' f
    apply hypsubst_thin
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Read _ _"])
      apply simp_all
     apply (intro conjI)
      apply assumption
     apply (auto simp add: ran_def split: sum.splits)
    done
  done

lemma step_Inp_Tau_loop_op[intro]:
  "step (Inp p x) op op' \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow> buf' = BTL p buf \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> BHD p buf = x \<Longrightarrow>
   step Tau (loop_op wire buf op) (loop_op wire buf' op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal for p' f
    apply hypsubst_thin
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Read _ _"])
      apply simp_all
     apply (intro conjI)
      apply assumption
     apply (auto simp add: ran_def split: sum.splits)
    done
  done

lemma step_Out_loop_op[intro!]:
  "step (Out p x) op op' \<Longrightarrow>
   wire p = None \<Longrightarrow> buf = buf' \<Longrightarrow>
   step (Out p x) (loop_op wire buf op) (loop_op wire buf' op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal for p'
    apply hypsubst_thin
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Write _ _ _"])
      apply (auto simp add: ran_def split: sum.splits)
    done
  done

lemma step_Out_Tau_loop_op[intro]:
  "step (Out p x) op op' \<Longrightarrow>
   wire p = Some q \<Longrightarrow> buf' = BENQ q x buf \<Longrightarrow>
   step Tau (loop_op wire buf op) (loop_op wire buf' op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal for p'
    apply hypsubst_thin
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Write _ _ _"])
      apply (auto simp add: ran_def split: sum.splits)
    done
  done

lemma step_Tau_loop_op[intro]:
  "step Tau op op' \<Longrightarrow> buf' = buf \<Longrightarrow>
   step Tau (loop_op wire buf op) (loop_op wire buf' op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Silent _"])
      apply (auto simp add: ran_def split: sum.splits)
    done
  done



section \<open>User defined operators\<close>
  (* abbreviation buffered ("\<stileturn> _ \<turnstile>" [150]151) where
  "\<stileturn>op\<turnstile> \<equiv> \<I> \<bullet> op \<bullet> \<I>" *)

abbreviation post_buffered ("_ \<turnstile>" [150]151) where
  "op\<turnstile> \<equiv> op \<bullet> \<I>"

abbreviation pre_buffered ("\<stileturn>_" [150]151) where
  "\<stileturn>op \<equiv> \<I> \<bullet> op"

section \<open>dummy_source_op\<close>                                     
abbreviation dummy_source_op ("\<exclamdown>") where
  "\<exclamdown> \<equiv> \<oslash> \<bullet> \<I>"

lemma finished_dummy_source:
  \<open>finished \<exclamdown>\<close>
  apply coinduction
  unfolding scomp_op_def
  apply (subst comp_op_code)
  apply auto
  done

lemma choices_dummy_source[simp]:
  \<open>choices \<exclamdown> = {||}\<close>
  unfolding scomp_op_def
  apply (subst comp_op_code)
  apply auto
  done

lemma choices_pcomp_op_dummy_source:
  \<open>choices (\<exclamdown> \<parallel> \<exclamdown>) = {||}\<close>
  unfolding pcomp_op_def
  apply (subst comp_op_code)
  apply simp
  done

section \<open>sink_op\<close>                                     
corec drain_op :: "('m :: {countable, defaults}, 'o, 'd) op" where
  "drain_op = Choice ((cimage (\<lambda> p. Read p (\<lambda> x. drain_op)) (cUNIV :: 'm cset)))"

lemma step_drain_op_Inp:
  assumes \<open>step io drain_op op\<close>
    and \<open>io = Inp p x\<close>
  obtains \<open>op = drain_op\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) drain_op.code)
  apply auto
  done

lemma no_step_drain_op_Out:
  assumes \<open>step io drain_op op\<close>
    and \<open>io = Out p x\<close>
  obtains False
  using assms
  apply (subst (asm) drain_op.code)
  apply auto
  done

lemma no_step_drain_op_Tau:
  assumes \<open>step io drain_op op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) drain_op.code)
  apply auto
  done

lemma step_drain_op:
  assumes \<open>step io drain_op op\<close>
  obtains p x where \<open>io = Inp p x\<close> \<open>p \<notin> defaults\<close> \<open>op = drain_op\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) drain_op.code)
  apply auto
  done

lemma step_drain_op_Read[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> step (Inp p x) drain_op drain_op\<close>
  apply (subst drain_op.code)
  apply fastforce
  done

lemma choices_drain_op[simp]:
  \<open>choices drain_op =
  cimage (\<lambda> p. Read p (\<lambda> x. drain_op)) cUNIV\<close>
  apply (subst drain_op.code)
  apply force
  done

abbreviation "sink_gen_op buf \<equiv> id_op (\<lambda> _. []) \<bullet> drain_op"
abbreviation sink_op ("!") where
  "! \<equiv> \<I> \<bullet> drain_op"

section \<open>transp_op - transposition operator\<close>

datatype (discs_sels) ('m, 'n, 'd) transp_op_aux =
  transp_Read_aux "'m + 'n" "'d \<Rightarrow> ('m + 'n \<Rightarrow> 'd buf)"
  | transp_Write_aux "('m + 'n \<Rightarrow> 'd buf)" "'n + 'm" 'd 

abbreviation eval_transp_op_aux where
  "eval_transp_op_aux c aux \<equiv> (case aux of
    transp_Read_aux p f \<Rightarrow> Read p (\<lambda>y. let buf = f y in c buf)
  | transp_Write_aux buf q x \<Rightarrow> (Write (c buf) q x))"

corec transp_op :: "_ \<Rightarrow> ('m :: {countable, defaults} + 'n :: {countable, defaults}, 'n + 'm, 'd) op" where
  "transp_op buf = Choice (cimage (eval_transp_op_aux transp_op) (cUn 
    (cimage (\<lambda> p. transp_Read_aux p (\<lambda> x. BENQ p x buf)) (cUNIV :: ('m + 'n) cset)) 
    (cimage (\<lambda> p. transp_Write_aux (BTL p buf) (case_sum Inr Inl p) (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: ('m + 'n) cset)))))"


lemma transp_op_code:
  "transp_op buf = Choice (cUn 
    (cimage (\<lambda> p. Read p (\<lambda> x. transp_op (BENQ p x buf))) (cUNIV :: ('m :: {countable, defaults} + 'n :: {countable, defaults}) cset)) 
    (cimage (\<lambda> p. Write (transp_op (BTL p buf)) (case_sum Inr Inl p) (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: ('m + 'n) cset))))"
  apply (subst transp_op.code)
  apply (unfold cimage_cUn cimage_cinsert op.inject)
  apply simp
  apply (auto simp add: cset.map_comp o_def intro!: arg_cong2[where f = cUn])
  done

abbreviation transp_empty_op ("\<X>") where
  "\<X> \<equiv> transp_op (\<lambda> _. [])"

lemma step_transp_op_Inp:
  assumes \<open>step io (transp_op buf) op\<close>
    and \<open>io = Inp p x\<close>
  obtains \<open>op = transp_op (BENQ p x buf)\<close> \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) transp_op_code)
  apply auto
  done

lemma step_transp_op_Out:
  assumes \<open>step io (transp_op buf) op\<close>
    and \<open>io = Out p x\<close>
    and \<open>p' = case_sum Inr Inl p\<close>
  obtains \<open>op = transp_op (BTL p' buf)\<close>
    \<open>BHD p' buf = x\<close>
    \<open>buf p' \<noteq> []\<close>
    \<open>p' \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (induct io \<open>transp_op buf\<close> op arbitrary: buf rule: step.induct)
     apply simp_all
   apply (subst (asm) transp_op_code)
   apply simp
  apply (subst (asm) (3) transp_op_code)
  apply (simp add: Set.filter_def split: sum.splits)
   apply (smt (z3) IO.inject(2) IO.simps(4) Inl_inject Un_iff defaults_sum_def image_iff mem_Collect_eq stepReadE stepWriteE sum.case_eq_if sum.collapse(2) sum.simps(4))
  apply (smt (z3) IO.inject(2) IO.simps(4) UnI1 defaults_sum_def image_iff isl_def mem_Collect_eq stepReadE stepWriteE sum.case_eq_if sum.sel(1) sum.sel(2) sum.simps(4))
  done

lemma no_step_transp_op_Tau:
  assumes \<open>step io (transp_op buf) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (induct io \<open>transp_op buf\<close> op arbitrary: buf rule: step.induct)
     apply simp_all
   apply (subst (asm) transp_op_code)
   apply simp
  apply (subst (asm) (2) transp_op_code)
  apply auto
  done


lemma step_transp_op_cases:
  assumes \<open>step io (transp_op buf) op\<close>
  obtains p x where  \<open>io = Inp p x\<close> \<open>p \<notin> defaults\<close> \<open>op = transp_op (BENQ p x buf)\<close> 
  |       p x p' where \<open>io = Out p x\<close> \<open>p' = case_sum Inr Inl p\<close> \<open>p' \<notin> defaults\<close> \<open>p \<notin> defaults\<close> \<open>op = transp_op (BTL p' buf)\<close>
    \<open>BHD p' buf = x\<close> \<open>buf p' \<noteq> []\<close>
  apply atomize_elim
  using assms
  apply (rule step_choicesE)
  subgoal for p f x
    apply (subst (asm) transp_op_code)
    apply simp
    done
  subgoal for p x
    apply (subst (asm) transp_op_code)
    apply (auto simp add: Set.filter_def split: sum.splits)
           apply (metis case_sum_defaults obj_sumE old.sum.simps)+
    done
  subgoal
    apply (subst (asm) transp_op_code)
    using assms no_step_transp_op_Tau
    apply simp
    done
  done


lemma step_transp_op_Read[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = (BENQ p x buf) \<Longrightarrow> step (Inp p x) (transp_op buf) (transp_op buf')\<close>
  apply hypsubst_thin
  apply (subst transp_op_code)
  apply (rule SC[rotated])
   apply (rule SR)
  apply (rule cUnI1)
  apply (rule cimageI)
  apply force
  done

lemma step_transp_op_Write[intro!]:
  \<open>BHD p buf = x \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> buf' = BTL p buf \<Longrightarrow> case_sum Inr Inl p = p' \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow> step (Out p' x) (transp_op buf) (transp_op buf')\<close>
  apply (subst transp_op_code)
  apply (rule SC[rotated])
   apply (rule SW)
  apply (rule cUnI2)
  apply hypsubst_thin
  apply (rule cimageI)
  apply auto
  done

lemma choices_transp_op[simp]:
  \<open>choices (transp_op buf) = cUn
  (cUnion (cimage choices (cimage (\<lambda> p. Read p (\<lambda> x. transp_op (buf(p := bulk_benq [x] (buf p))))) cUNIV)))
  (cUnion (cimage choices (cimage (\<lambda> p. Write (transp_op (BTL p buf)) (case_sum Inr Inl p) (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) cUNIV))))\<close>
  apply (subst transp_op_code)
  apply (simp add: BTL_def BENQ_def)
  done

section \<open>split_op - nondeterministic split operator\<close>

datatype (discs_sels) ('m, 'd) split_op_aux =
  split_Read_aux 'm \<open>'d \<Rightarrow> 'm + 'm \<Rightarrow> 'd buf\<close>
  | split_Write_aux \<open>'m + 'm \<Rightarrow> 'd buf\<close> \<open>'m + 'm\<close> 'd

abbreviation eval_split_op_aux where
  \<open>eval_split_op_aux c aux \<equiv> (case aux of
    split_Read_aux p f \<Rightarrow> Read p (c \<circ> f)
  | split_Write_aux buf p x \<Rightarrow> Write (c buf) p x)\<close>

corec split_op :: \<open>('m :: {countable, defaults} + 'm \<Rightarrow> 'd buf) \<Rightarrow> ('m, 'm + 'm, 'd) op\<close> where
  \<open>split_op buf = Choice (cimage (eval_split_op_aux split_op) (cUn (cUn
    (cimage (\<lambda>p. split_Read_aux p (\<lambda>x. BENQ (Inl p) x buf)) cUNIV)
    (cimage (\<lambda>p. split_Read_aux p (\<lambda>x. BENQ (Inr p) x buf)) cUNIV))
    (cimage (\<lambda>p. split_Write_aux (BTL p buf) p (BHD p buf))
      (cfilter (\<lambda>p. buf p \<noteq> []) cUNIV))))\<close>

lemma split_op_code:
  \<open>split_op buf = Choice (cUn (cUn
    (cimage (\<lambda>p. Read p (\<lambda>x. split_op (BENQ (Inl p) x buf))) cUNIV)
    (cimage (\<lambda>p. Read p (\<lambda>x. split_op (BENQ (Inr p) x buf))) cUNIV))
    (cimage (\<lambda>p. Write (split_op (BTL p buf)) p (BHD p buf))
      (cfilter (\<lambda>p. buf p \<noteq> []) cUNIV)))\<close>
  apply (subst split_op.code)
  apply (unfold cimage_cUn cimage_cinsert op.inject)
  apply (auto simp add: cset.map_comp o_def)
  done


abbreviation split_empty_op (\<open>\<Lambda>\<close>) where \<open>\<Lambda> \<equiv> split_op (\<lambda>_. [])\<close>

lemma step_split_op_Inp:
  assumes \<open>step io (split_op buf) op\<close>
    and \<open>io = Inp p x\<close>
  obtains \<open>op = split_op (BENQ (Inl p) x buf)\<close> | \<open>op = split_op (BENQ (Inr p) x buf)\<close>
  using assms
  apply (subst (asm) split_op_code)
  by force

lemma step_split_op_Out:
  assumes \<open>step io (split_op buf) op\<close>
    and \<open>io = Out p x\<close>
  obtains \<open>op = split_op (BTL p buf)\<close> \<open>buf p \<noteq> []\<close> \<open>BHD p buf = x\<close>
  using assms
  apply (subst (asm) split_op_code)
  by force

lemma no_step_split_op_Tau:
  assumes \<open>step io (split_op buf) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) split_op_code)
  by force

lemma step_split_op_cases:
  assumes \<open>step io (split_op buf) op\<close>
  obtains p x where \<open>io = Inp p x\<close> \<open>op = split_op (BENQ (Inl p) x buf)\<close> \<open>p \<notin> defaults\<close>
  |       p x where \<open>io = Inp p x\<close> \<open>op = split_op (BENQ (Inr p) x buf)\<close> \<open>p \<notin> defaults\<close>
  |       p x where \<open>io = Out p x\<close> \<open>op = split_op (BTL p buf)\<close> \<open>buf p \<noteq> []\<close> \<open>BHD p buf = x\<close> \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) split_op_code)
  by force

lemma step_split_op_Read_L[intro]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BENQ (Inl p) x buf \<Longrightarrow> step (Inp p x) (split_op buf) (split_op buf')\<close>
  apply (subst split_op_code)
  by force

lemma step_split_op_Read_R[intro]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BENQ (Inr p) x buf \<Longrightarrow> step (Inp p x) (split_op buf) (split_op buf')\<close>
  apply (subst split_op_code)
  by force

lemma step_split_op_Write[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> BHD p buf = x \<Longrightarrow> buf' = BTL p buf \<Longrightarrow>
  step (Out p x) (split_op buf) (split_op buf')\<close>
  apply (subst split_op_code)
  by fastforce

lemma choices_split_op[simp]:
  \<open>choices (split_op buf) = cUn (cUn
    (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda>x. split_op (BENQ (Inl p) x buf))) cUNIV)))
    (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda>x. split_op (BENQ (Inr p) x buf))) cUNIV))))
    (cUnion (cimage choices (cimage (\<lambda>p. Write (split_op (BTL p buf)) p (BHD p buf))
      (cfilter (\<lambda>p. buf p \<noteq> []) cUNIV))))\<close>
  apply (subst split_op_code)
  by simp

section \<open>merge_op - nondeterministic merge operator\<close>
datatype (discs_sels) ('m) merge_op_aux =
  merge_Read_aux "'m"

abbreviation eval_merge_op_aux where
  "eval_merge_op_aux c aux \<equiv> (case aux of
    merge_Read_aux p \<Rightarrow> choice2 (Read (Inl p) (\<lambda>y. Write c p y)) (Read (Inr p) (\<lambda>y. Write c p y)))"

corec merge_op :: "('m + 'm :: {countable, defaults}, 'm, 'a) op" ("\<V>") where
  "merge_op = Choice (cimage (eval_merge_op_aux merge_op) 
   (cimage (\<lambda> p. merge_Read_aux p) (cUNIV :: 'm cset)))"

lemma merge_op_code:
  "merge_op = Choice (cimage (\<lambda> p. Choice {|Read (Inl p) (\<lambda>y. Write merge_op p y), Read (Inr p) (\<lambda>y. Write merge_op p y)|}) (cUNIV :: 'm :: {countable, defaults} cset))"
  apply (subst merge_op.code)
  apply (auto simp add: cset.map_comp intro!: arg_cong2[where f = cUn])
  done

lemma step_merge_op_Inp:
  assumes \<open>step io \<V> op\<close>
    and \<open>io = Inp p x\<close>
    and \<open>p' = case_sum id id p\<close>
  obtains \<open>op = Write \<V> p' x\<close>
  using assms
  apply (subst (asm) merge_op_code)
  apply auto
  done

lemma no_step_merge_op_Out:
  assumes \<open>step io \<V> op\<close>
    and \<open>io = Out p x\<close>
  obtains False
  using assms
  apply (subst (asm) merge_op_code)
  apply auto
  done

lemma no_step_merge_op_Tau:
  assumes \<open>step io \<V> op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) merge_op_code)
  apply auto
  done

lemma step_merge_op:
  assumes \<open>step io \<V> op\<close>
  obtains p x p' where \<open>io = Inp p x\<close> \<open>p \<notin> defaults\<close>  \<open>p' = case_sum id id p\<close> \<open>op = Write \<V> p' x\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) merge_op_code)
  apply auto
  done

lemma step_merge_op_Read[intro]:
  \<open>p \<notin> defaults \<Longrightarrow> p' = case_sum id id p \<Longrightarrow> step (Inp p x) \<V> (Write \<V> p' x)\<close>
  apply (subst merge_op_code)
  apply (simp split: sum.splits)
   apply auto
  done

lemma choices_merge_op[simp]:
  \<open>choices \<V> = cUn
  (cUnion (cimage choices (cimage (\<lambda> p. Read (Inl p) (\<lambda> y. Write \<V> p y)) cUNIV)))
  (cUnion (cimage choices (cimage (\<lambda> p. Read (Inr p) (\<lambda> y. Write \<V> p y)) cUNIV)))\<close>
  apply (subst merge_op_code)
  apply auto
  done

section \<open>acopy_op - async copy operator\<close>
datatype (discs_sels) ('m) acopy_op_aux =
  acopy_Read_aux "'m"

abbreviation eval_acopy_op_aux where
  "eval_acopy_op_aux c aux \<equiv> (case aux of
    acopy_Read_aux p \<Rightarrow> Read p (\<lambda>y. choice2 (Write (Write c (Inr p) y) (Inl p) y) (Write (Write c (Inl p) y) (Inr p) y)))"

corec acopy_op :: "('m :: {countable, defaults}, 'm + 'm, 'a) op" ("\<C>") where
  "acopy_op = Choice (cimage (eval_acopy_op_aux acopy_op) 
   (cimage (\<lambda> p. acopy_Read_aux p) (cUNIV :: 'm cset)))"

lemma acopy_op_code:
  "acopy_op = Choice (cimage (\<lambda> p. Read p (\<lambda> y. Choice {|
    Write (Write acopy_op (Inr p) y) (Inl p) y,
    Write (Write acopy_op (Inl p) y) (Inr p) y|})) (cUNIV :: 'm :: {countable, defaults} cset))"
  apply (subst acopy_op.code)
  apply (auto simp add: cset.map_comp intro!: arg_cong2[where f = cUn])
  done

lemma step_acopy_op_Inp:
  assumes \<open>step io \<C> op\<close>
    and \<open>io = Inp p x\<close>
  obtains \<open>op = Choice {|Write (Write \<C> (Inr p) x) (Inl p) x, Write (Write \<C> (Inl p) x) (Inr p) x|}\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) acopy_op_code)
  apply auto
  done

lemma no_step_acopy_op_Out:
  assumes \<open>step io \<C> op\<close>
    and \<open>io = Out p x\<close>
  obtains False
  using assms
  apply (subst (asm) acopy_op_code)
  apply auto
  done

lemma no_step_acopy_op_Tau:
  assumes \<open>step io \<C> op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) acopy_op_code)
  apply auto
  done

lemma step_acopy_op:
  assumes \<open>step io \<C> op\<close>
  obtains p x where \<open>io = Inp p x\<close> \<open>op = Choice {|Write (Write \<C> (Inr p) x) (Inl p) x, Write (Write \<C> (Inl p) x) (Inr p) x|}\<close> \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) acopy_op_code)
  apply auto
  done

lemma step_acopy_op_Read[intro]:
  \<open>p \<notin> defaults \<Longrightarrow> step (Inp p x) \<C> (Choice {|Write (Write \<C> (Inr p) x) (Inl p) x, Write (Write \<C> (Inl p) x) (Inr p) x|})\<close>
  apply (subst acopy_op_code)
  apply fastforce
  done

lemma choices_acopy_op[simp]:
  \<open>choices \<C> = cimage (\<lambda> p. Read p (\<lambda> y. Choice {|Write (Write \<C> (Inr p) y) (Inl p) y, Write (Write \<C> (Inl p) y) (Inr p) y|})) cUNIV\<close>
  apply (subst acopy_op_code)
  apply auto
  done

section \<open>aeq_op - async equality operator\<close>
datatype (discs_sels) ('m, 'd) aeq_op_aux =
  aeq_Read_aux \<open>'m + 'm\<close> \<open>'d \<Rightarrow> 'm + 'm \<Rightarrow> 'd buf\<close>
  | aeq_Write_aux \<open>'m + 'm \<Rightarrow> 'd buf\<close> 'm 'd
  | aeq_Silent_aux \<open>'m + 'm \<Rightarrow> 'd buf\<close>

abbreviation eval_aeq_op_aux where
  \<open>eval_aeq_op_aux c aux \<equiv> (case aux of
    aeq_Read_aux p f \<Rightarrow> Read p (c \<circ> f)
  | aeq_Write_aux buf p x \<Rightarrow> Write (c buf) p x
  | aeq_Silent_aux buf \<Rightarrow> Silent (c buf))\<close>

corec aeq_op :: \<open>('m :: {countable, defaults} + 'm \<Rightarrow> 'd buf) \<Rightarrow> ('m + 'm, 'm, 'd) op\<close> where
  \<open>aeq_op buf = Choice (cimage (eval_aeq_op_aux aeq_op) (cUn (cUn
    (cimage (\<lambda>p. aeq_Read_aux (Inl p) (\<lambda>x. BENQ (Inl p) x buf)) cUNIV)
    (cimage (\<lambda>p. aeq_Read_aux (Inr p) (\<lambda>x. BENQ (Inr p) x buf)) cUNIV))
    (cimage (\<lambda>p. (if BHD (Inl p) buf = BHD (Inr p) buf then aeq_Write_aux (BTL (Inr p) (BTL (Inl p) buf)) p (BHD (Inl p) buf) else aeq_Silent_aux (BTL (Inr p) (BTL (Inl p) buf))))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> [] \<and> buf (Inr p) \<noteq> []) cUNIV))))\<close> 

lemma aeq_op_code:
  "aeq_op buf = Choice (cUn (cUn
    (cimage (\<lambda> p. Read (Inl p) (\<lambda> x. aeq_op (BENQ (Inl p) x buf))) (cUNIV :: 'm :: {countable, defaults} cset))
    (cimage (\<lambda> p. Read (Inr p) (\<lambda> x. aeq_op (BENQ (Inr p) x buf))) (cUNIV :: 'm cset)))
    (cimage (\<lambda>p. (if BHD (Inl p) buf = BHD (Inr p) buf 
      then Write (aeq_op (BTL (Inr p) (BTL (Inl p) buf))) p (BHD (Inl p) buf) 
      else Silent (aeq_op (BTL (Inr p) (BTL (Inl p) buf))))) (cfilter (\<lambda>p. buf (Inl p) \<noteq> [] \<and> buf (Inr p) \<noteq> []) cUNIV)))"
  apply (subst aeq_op.code)
  apply (auto simp add: comp_def cset.map_comp o_def split: if_splits op.splits)
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply force
    apply auto
    done
  done

abbreviation aeq_empty_op (\<open>\<Q>\<close>) where \<open>\<Q> \<equiv> aeq_op (\<lambda>_. [])\<close>

lemma step_aeq_op_Inp_L:
  assumes \<open>step io (aeq_op buf) op\<close>
    and \<open>io = Inp (Inl p) y\<close>
  obtains \<open>op = aeq_op (BENQ (Inl p) y buf)\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) aeq_op_code)
  apply auto
  done

lemma step_aeq_op_Inp_R:
  assumes \<open>step io (aeq_op buf) op\<close>
    and \<open>io = Inp (Inr p) y\<close>
  obtains \<open>op = aeq_op (BENQ (Inr p) y buf)\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) aeq_op_code)
  apply auto
  done

lemma no_step_aeq_op_Out:
  assumes \<open>step io (aeq_op buf) op\<close>
    and \<open>io = Out p x\<close>
  obtains \<open>op = aeq_op (BTL (Inr p) (BTL (Inl p) buf))\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>x = BHD (Inl p) buf\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>BHD (Inl p) buf = BHD (Inr p) buf\<close> \<open>p \<notin> defaults\<close>
  using assms apply atomize
  apply (subst (asm) (2) aeq_op_code)
  apply auto
  done

lemma no_step_aeq_op_Tau:
  assumes \<open>step io (aeq_op buf) op\<close>
    and \<open>io = Tau\<close>
  obtains p where \<open>op = aeq_op (BTL (Inr p) (BTL (Inl p) buf))\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>BHD (Inl p) buf \<noteq> BHD (Inr p) buf\<close> \<open>p \<notin> defaults\<close>
  using assms apply atomize
  apply (subst (asm) (2) aeq_op_code)
  apply auto
  done

lemma step_aeq_op_elim:
  assumes \<open>step io (aeq_op buf) op\<close>
  obtains p y where \<open>io = Inp (Inl p) y\<close> \<open>op = aeq_op (BENQ (Inl p) y buf)\<close> \<open>p \<notin> defaults\<close>
  | p y where \<open>io = Inp (Inr p) y\<close> \<open>op = aeq_op (BENQ (Inr p) y buf)\<close> \<open>p \<notin> defaults\<close>
  | p x where \<open>io = Out p x\<close> \<open>op = aeq_op (BTL (Inr p) (BTL (Inl p) buf))\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>x = BHD (Inl p) buf\<close> \<open>BHD (Inl p) buf = BHD (Inr p) buf\<close> \<open>p \<notin> defaults\<close>
  | p where \<open>io = Tau\<close> \<open>op = aeq_op (BTL (Inr p) (BTL (Inl p) buf))\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>BHD (Inl p) buf \<noteq> BHD (Inr p) buf\<close> \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) aeq_op_code)
  apply fastforce
  done

lemma step_aeq_op_Read_L[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BENQ (Inl p) y buf \<Longrightarrow> step (Inp (Inl p) y) (aeq_op buf) (aeq_op buf')\<close>
  apply (subst aeq_op_code)
  apply auto
  done

lemma step_aeq_op_Read_R[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BENQ (Inr p) y buf \<Longrightarrow> step (Inp (Inr p) y) (aeq_op buf) (aeq_op buf')\<close>
  apply (subst aeq_op_code)
  apply auto
  done

lemma step_aeq_op_Write[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow>
   buf (Inl p) \<noteq> [] \<Longrightarrow> buf (Inr p) \<noteq> [] \<Longrightarrow> BHD (Inl p) buf = BHD (Inr p) buf \<Longrightarrow> 
   buf' = BTL (Inr p) (BTL (Inl p) buf) \<Longrightarrow> y = BHD (Inl p) buf \<Longrightarrow>
   step (Out p y) (aeq_op buf) (aeq_op buf')\<close>
  apply (subst aeq_op_code)
  apply auto
  done

lemma step_aeq_op_Silent[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow>
   buf (Inl p) \<noteq> [] \<Longrightarrow> buf (Inr p) \<noteq> [] \<Longrightarrow> BHD (Inl p) buf \<noteq> BHD (Inr p) buf \<Longrightarrow> 
   buf' = BTL (Inr p) (BTL (Inl p) buf) \<Longrightarrow>
   step Tau (aeq_op buf) (aeq_op buf')\<close>
  apply (subst aeq_op_code)
  apply fastforce
  done

end
