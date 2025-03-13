\<comment> \<open>The basic operators from the "Network Algebra for Synchronous and Asynchronous Dataflow" (https://staff.fnwi.uva.nl/c.a.middelburg/papers/P9508.pdf) \<close>
theory BNA_Operators

imports
  Operator
  "HOL-ex.Sketch_and_Explore"
begin

instantiation num0 :: countable begin
instance proof qed (auto simp: inj_def Rep_num0_inject intro!: exI[of _ Rep_num0])
end

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

lemma step_comp_op_R_Taus:
  "(step Tau)\<^sup>*\<^sup>* op2 op2' \<Longrightarrow> buf = buf' \<Longrightarrow> op1 = op1' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  apply (induct op2 rule: converse_rtranclp_induct)
   apply blast
  apply (meson converse_rtranclp_into_rtranclp step_comp_op_R_Tau)
  done

lemma step_comp_op_L_Taus:
  "(step Tau)\<^sup>*\<^sup>* op1 op1' \<Longrightarrow> buf = buf' \<Longrightarrow> op2 = op2' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  apply (induct op1 rule: converse_rtranclp_induct)
   apply blast
  apply (meson converse_rtranclp_into_rtranclp step_comp_op_L_Tau)
  done

lemma wstep_Tau_comp_op_L[]:
  "wstep (Out p x) op1 op1' \<Longrightarrow>
   wire p = Some q \<Longrightarrow>
   buf' = BENQ q x buf \<Longrightarrow>
   op2 = op2' \<Longrightarrow>
   wstep Tau (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  unfolding wstep_def by (auto intro: step_comp_op_L_Taus)

lemma wstep_Tau_comp_op_R[]:
  "wstep (Inp p x) op2 op2' \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow>
   buf p \<noteq> [] \<Longrightarrow>
   BHD p buf = x \<Longrightarrow>
   buf' = BTL p buf \<Longrightarrow>
   op1' = op1 \<Longrightarrow>
   wstep Tau (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  unfolding wstep_def by (auto intro: step_comp_op_R_Taus)

lemma wstep_comp_op_L_Inp[]:
  "wstep (Inp p x) op1 op1' \<Longrightarrow> buf = buf' \<Longrightarrow> op2 = op2' \<Longrightarrow>  wstep (Inp (Inl p) x) (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  unfolding wstep_def by (auto intro: step_comp_op_L_Taus)

lemma wstep_comp_op_R_Out[]:
  "wstep (Out p x) op2 op2' \<Longrightarrow> buf = buf' \<Longrightarrow> op1 = op1' \<Longrightarrow> wstep (Out (Inr p) x) (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  unfolding wstep_def by (auto intro: step_comp_op_R_Taus)

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

lemma inputs_pcomp_op_le_dest[dest!]:
  "c \<in> inputs (comp_op (\<lambda> _. None) buf op1 op2) \<Longrightarrow> c \<in> Inl ` inputs op1 \<or> c \<in> Inr ` (inputs op2)"
  using set_mp[OF inputs_comp_op_le, simplified] by force
lemma outputs_pcomp_op_le_alt[dest!]:
  "c \<in> outputs (comp_op (\<lambda> _. None) buf op1 op2) \<Longrightarrow> c \<in> Inl ` outputs op1 \<or> c \<in> Inr ` outputs op2"
  using set_mp[OF outputs_comp_op_le, simplified] by force

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

lemma inputs_scomp_op_le_dest[dest!]:
  "c \<in> inputs (comp_op Some buf op1 op2) \<Longrightarrow> c \<in> Inl ` inputs op1"
  using set_mp[OF inputs_comp_op_le, simplified] by force
lemma outputs_scomp_op_le_dest[dest!]:
  "c \<in> outputs (comp_op Some buf op1 op2) \<Longrightarrow>c \<in> Inr ` outputs op2"
  using set_mp[OF outputs_comp_op_le, simplified] by force

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

subsection \<open>Congruence for strong bisim\<close>
lemma bisim_loop_op_cong_gen:
  "op ~ op' \<Longrightarrow>
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) ~
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')"
proof (coinduction arbitrary: op op' buf rule: bisim_coinduct)
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. step (Inp (projl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a)) op2'"
      if "sim (~) op op'"
        and "sim (~) op' op"
        and "\<forall>p'. p = Inr p' \<longrightarrow> p' \<in> defaults"
        and "step (Inp p x) op op''a"
      for p :: "'a + 'b"
        and x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
      using that apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Inp_loop_op)
         apply assumption
        apply simp_all
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a)) op2'"
      if "step (Out (Inl x1) x) op op''a"
        and "sim (~) op op'"
        and "sim (~) op' op"
      for x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x1 :: 'c
      using that apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Out_loop_op)
          apply assumption
         apply simp_all
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a)) op2'"
      if "step (Out (Inr x2) x) op op''a"
        and "sim (~) op op'"
        and "sim (~) op' op"
        and "x2 \<in> defaults"
      for x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x2 :: 'b
      using that apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Out_loop_op)
          apply assumption
         apply simp_all
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a)) op2'"
      if "sim (~) op op'"
        and "sim (~) op' op"
        and "step Tau op op''a"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
      using that apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Tau_loop_op)
         apply assumption
        apply simp_all
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf)) op''a)) op2'"
      if "step (Inp (Inr x2) (BHD x2 buf)) op op''a"
        and "sim (~) op op'"
        and "sim (~) op' op"
        and "x2 \<notin> defaults"
        and "buf x2 \<noteq> []"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x2 :: 'b
      using that apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Inp_Tau_loop_op)
            apply assumption
           apply simp_all
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf)) op''a)) op2'"
      if "step (Out (Inr x2) x) op op''a"
        and "sim (~) op op'"
        and "sim (~) op' op"
        and "x2 \<notin> defaults"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x :: 'd
        and x2 :: 'b
      using that apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Out_Tau_loop_op)
          apply assumption
         apply simp_all
      apply (rule b_base)
      apply force
      done
    ultimately show ?thesis
      using SIM1 by (auto elim !: bisim.cases step_map_op_elim step_loop_op_elim split: if_splits sum.splits)
  qed
next
  case SIM2
  then show ?case 
  proof -
    have "\<exists>op2'. step (Inp (projl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a))"
      if "sim (~) op' op" 
        and "sim (~) op op'"
        and "\<forall>p'. p = Inr p' \<longrightarrow> p' \<in> defaults"
        and "step (Inp p x) op' op''a"
      for p :: "'a + 'b"
        and x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
      using that 
      apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Inp_loop_op)
         apply assumption
        apply simp_all
      apply (rule b_sym)
      apply (rule b_base)
      apply (intro conjI exI)
        apply force+
      done
    moreover have "\<exists>op2'. step (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a))"
      if "step (Out (Inl x1) x) op' op''a"
        and "sim (~) op op'"
        and "sim (~) op' op"
      for x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x1 :: 'c
      using that 
      apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Out_loop_op)
          apply assumption
         apply simp_all
      apply (rule b_sym)
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a))"
      if "step (Out (Inr x2) x) op' op''a"
        and "sim (~) op' op"
        and "sim (~) op op'"
        and "x2 \<in> defaults"
      for x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x2 :: 'b
      using that 
      apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Out_loop_op)
          apply assumption
         apply simp_all
      apply (rule b_sym)
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a))"
      if "sim (~) op' op"
        and "sim (~) op op'"
        and "step Tau op' op''a"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
      using that 
      apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Tau_loop_op)
         apply assumption
        apply simp_all
      apply (rule b_sym)
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf)) op''a))"
      if "step (Inp (Inr x2) (BHD x2 buf)) op' op''a"
        and "sim (~) op' op"
        and "sim (~) op op'"
        and "x2 \<notin> defaults"
        and "buf x2 \<noteq> []"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x2 :: 'b
      using that 
      apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Inp_Tau_loop_op)
            apply assumption
           apply simp_all
      apply (rule b_sym)
      apply (rule b_base)
      apply fast
      done
    moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> bisim_R (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op ~ op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf)) op''a))"
      if "step (Out (Inr x2) x) op' op''a"
        and "sim (~) op' op"
        and "sim (~) op op'"
        and "x2 \<notin> defaults"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x :: 'd
        and x2 :: 'b
      using that 
      apply -
      unfolding sim_def
      apply (drule spec2, drule mp, simp)
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply (rule step_map_op)
        apply (rule step_Out_Tau_loop_op)
          apply assumption
         apply simp_all
      apply (rule b_sym)
      apply (rule b_base)
      apply force
      done
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_loop_op_elim bisim.cases split: if_splits sum.splits)
  qed
qed

lemma bisim_loop_op_cong:
  "op ~ op' \<Longrightarrow>
   op\<up> ~ op'\<up>"
  unfolding feedback_op_def using bisim_loop_op_cong_gen by auto

subsection \<open>Congruence for weak bisim\<close>
lemma wstep_Inp_loop_op[intro]:
  "wstep (Inp p x) op op' \<Longrightarrow>
   p \<notin> ran wire \<Longrightarrow>
   wstep (Inp p x) (loop_op wire buf op) (loop_op wire buf op')"
  unfolding wstep_def
  apply safe
  oops

(* FIXME: move me *)
lemma wbisim_wstep_alt:
  "op1 \<approx> op2 \<Longrightarrow>
   step io op1 op1' \<Longrightarrow>
   \<exists> op2'. wstep io op2 op2' \<and> op1' \<approx> op2'"
  apply (drule step_wstep)
  apply (erule wbisim_wstep[OF wbisimulation_wbisim])
   apply assumption
  unfolding wstep_def
  apply auto
  done

(* FIXME: move me *)
lemma step_taus_loop_[intro]:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   (step Tau)\<^sup>*\<^sup>* (loop_op wire buf op) (loop_op wire buf op')"
  apply (induct op rule: converse_rtranclp_induct)
   apply blast
  apply (meson converse_rtranclp_into_rtranclp step_Tau_loop_op)
  done

(* FIXME: move me *)
lemma wstep_loop_[intro]:
  "wstep (Inp p x) op op' \<Longrightarrow>
   p \<notin> ran wire \<Longrightarrow>
   wstep (Inp p x) (loop_op wire buf op) (loop_op wire buf op')"
  unfolding wstep_def by auto

lemma wstep_Inp_Tau_loop_op[intro]:
  "wstep (Inp p x) op op' \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow> buf' = BTL p buf \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> BHD p buf = x \<Longrightarrow>
   wstep Tau (loop_op wire buf op) (loop_op wire buf' op')"
  unfolding wstep_def by auto

lemma wstep_Out_loop_op[intro]:
  "wstep (Out p x) op op' \<Longrightarrow>
   wire p = None \<Longrightarrow> buf = buf' \<Longrightarrow>
   wstep (Out p x) (loop_op wire buf op) (loop_op wire buf' op')"
  unfolding wstep_def by auto

lemma wstep_Out_Tau_loop_op[intro]:
  "wstep (Out p x) op op' \<Longrightarrow>
   wire p = Some q \<Longrightarrow> buf' = BENQ q x buf \<Longrightarrow>
   wstep Tau (loop_op wire buf op) (loop_op wire buf' op')"
  unfolding wstep_def by auto

lemma wstep_Tau_loop_op[intro]:
  "wstep Tau op op' \<Longrightarrow> buf' = buf \<Longrightarrow>
   wstep Tau (loop_op wire buf op) (loop_op wire buf' op')"
  unfolding wstep_def by auto


lemma wbisim_loop_op_cong_gen:
  "op \<approx> op' \<Longrightarrow>
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<approx>
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')"
proof (coinduction arbitrary: op op' buf rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp (projl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a)) op2'"
      if "op \<approx> op'"
        and "\<forall>p'. p = Inr p' \<longrightarrow> p' \<in> defaults"
        and "step (Inp p x) op op''a"
      for p :: "'a + 'b"
        and x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
      using that apply -
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI wbc_base)
         apply assumption
        apply (rule refl)+
      apply (smt (verit, ccfv_SIG) IO.map(1) in_feedback_wire map_IO_projl_eq_Inp sum.sel(1) wstep_loop_ wstep_map_op)
      done
    moreover have "\<exists>op2'. wstep (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a)) op2'"
      if "step (Out (Inl x1) x) op op''a"
        and "op \<approx> op'"
      for x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x1 :: 'c
      using that apply -
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI wbc_base)
         apply assumption
        apply (rule refl)+
      apply auto
      done      
    moreover have "\<exists>op2'. wstep (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a)) op2'"
      if "step (Out (Inr x2) x) op op''a"
        and "op \<approx> op'"
        and "x2 \<in> defaults"
      for x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x2 :: 'b
      using that apply -
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI wbc_base)
         apply assumption
        apply (rule refl)+
      apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a)) op2'"
      if "op \<approx> op'"
        and "step Tau op op''a"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
      using that apply -
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI wbc_base)
         apply assumption
        apply (rule refl)+
      apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf)) op''a)) op2'"
      if "step (Inp (Inr x2) (BHD x2 buf)) op op''a"
        and "op \<approx> op'"
        and "x2 \<notin> defaults"
        and "buf x2 \<noteq> []"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x2 :: 'b
      using that apply -
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI wbc_base)
         apply assumption
        apply (rule refl)+
      apply (smt (verit, best) case_sum_BHD_R case_sum_BTL_R in_feedback_wire old.sum.simps(6) step_star_map_op wstep_Inp_Tau_loop_op wstep_steps_Tau)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf)) op''a)) op2'"
      if "step (Out (Inr x2) x) op op''a"
        and "op \<approx> op'"
        and "x2 \<notin> defaults"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x :: 'd
        and x2 :: 'b
      using that apply -
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI wbc_base)
         apply assumption
        apply (rule refl)+
      apply (smt (verit, del_insts) case_sum_BENQ_R old.sum.simps(6) step_star_map_op wstep_Out_Tau_loop_op wstep_steps_Tau)
      done
    ultimately show ?thesis
      using SIM1  by (auto elim !: step_map_op_elim step_loop_op_elim split: if_splits sum.splits)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim !: step_map_op_elim step_loop_op_elim split: if_splits sum.splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp (projl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a))"
      if "op \<approx> op'"
        and "\<forall>p'. p = Inr p' \<longrightarrow> p' \<in> defaults"
        and "step (Inp p x) op' op''a"
      for p :: "'a + 'b"
        and x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
      using that apply -
      apply (drule wbisim_sym)
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI)
       apply (rule wbc_sym)
       apply (rule wbc_base)
       apply blast
      apply (smt (verit, ccfv_threshold) IO.map(1) id_apply in_feedback_wire wstep_loop_ wstep_map_op)
      done
    moreover have "\<exists>op2'. wstep (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a))"
      if "step (Out (Inl x1) x) op' op''a"
        and "op \<approx> op'"
      for x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x1 :: 'c
      using that apply -
      apply (drule wbisim_sym)
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI)
       apply (rule wbc_sym)
       apply (rule wbc_base)
       apply blast
      apply auto
      done
    moreover have "\<exists>op2'. wstep (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a))"
      if "step (Out (Inr x2) x) op' op''a"
        and "op \<approx> op'"
        and "x2 \<in> defaults"
      for x :: 'd
        and op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x2 :: 'b
      using that apply -
      apply (drule wbisim_sym)
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI)
       apply (rule wbc_sym)
       apply (rule wbc_base)
       apply blast
      apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op''a))"
      if "op \<approx> op'"
        and "step Tau op' op''a"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
      using that apply -
      apply (drule wbisim_sym)
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI)
       apply (rule wbc_sym)
       apply (rule wbc_base)
       apply blast
      apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf)) op''a))"
      if "step (Inp (Inr x2) (BHD x2 buf)) op' op''a"
        and "op \<approx> op'"
        and "x2 \<notin> defaults"
        and "buf x2 \<noteq> []"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x2 :: 'b
      using that apply -
      apply (drule wbisim_sym)
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI)
       apply (rule wbc_sym)
       apply (rule wbc_base)
       apply blast
      apply (smt (verit, best) case_sum_BHD_R case_sum_BTL_R case_sum_if in_feedback_wire step_star_map_op wstep_Inp_Tau_loop_op wstep_steps_Tau)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op)) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op op' buf. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'b) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op) \<and> op2xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf) op') \<and> op \<approx> op') op2' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf)) op''a))"
      if "step (Out (Inr x2) x) op' op''a"
        and "op \<approx> op'"
        and "x2 \<notin> defaults"
      for op''a :: "('a + 'b, 'c + 'b, 'd) op"
        and x :: 'd
        and x2 :: 'b
      using that apply -
      apply (drule wbisim_sym)
      apply (drule wbisim_wstep_alt, assumption)
      apply (elim conjE exE)
      apply (intro conjI[rotated] exI)
       apply (rule wbc_sym)
       apply (rule wbc_base)
       apply blast
      apply (smt (verit, ccfv_SIG) case_sum_BENQ_R old.sum.simps(6) step_star_map_op wstep_Out_Tau_loop_op wstep_steps_Tau)
      done
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_loop_op_elim split: if_splits sum.splits)
  qed
qed

lemma wbisim_loop_op_cong:
  "op \<approx> op' \<Longrightarrow>
   op\<up> \<approx> op'\<up>"
  unfolding feedback_op_def using wbisim_loop_op_cong_gen by auto

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
  "\<otimes> = Choice ((\<lambda> _. spin_op) |`| {|()|})"

lemma spin_op_code:
  "\<otimes> = Choice {|\<otimes>|}"
  apply (subst spin_op.code)
  apply simp
  done

corec silent_op ("\<odot>") where
  "\<odot> = Silent silent_op"

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
  apply (coinduction rule: bisim_coinduct)
   apply (auto elim: step_spin_op_no_label)
  done

section \<open>Basic operator examples\<close>

corec ex1_op where
  "ex1_op = choice2 (Write ex1_op (1::2) (42::nat)) \<oslash>"

lemma ex1_op_code:
  "ex1_op = Choice {|Write ex1_op (1::2) (42::nat), \<oslash>|}"
  by (subst ex1_op.code, simp)

lemma step_ex1_op_elim[elim!]:
  assumes "step io ex1_op op'"
  obtains "op' = ex1_op" and "io = Out 1 42"
  using assms
  apply atomize_elim
  apply (subst (asm) ex1_op_code)
  apply auto
  done

lemma step_ex1_op_intro[intro!]:
  assumes "io = Out 1 42"
    and "op' = ex1_op"
  shows "step io ex1_op op'"
  using assms apply -
  apply (subst ex1_op_code)
  apply auto
  done

corec ex2_op where
  "ex2_op = choice2 (Write ex2_op (1::2) (42::nat)) ex2_op"

lemma ex2_op_code:
  "ex2_op = Choice {|Write ex2_op (1::2) (42::nat), ex2_op|}"
  by (subst ex2_op.code, simp)

lemma step_ex2_op_aux:
  "step io op op' \<Longrightarrow>
   op = Choice {|Write ex2_op 1 42, ex2_op|} \<Longrightarrow>
   op' = ex2_op \<and> io = Out 1 42"
  apply (induct op op' pred: step)
  using ex2_op_code apply blast+
  done

lemma step_ex2_op_elim[elim!]:
  assumes "step io ex2_op op'"
  obtains "op' = ex2_op" "io = Out 1 42"
  using assms
  apply atomize_elim
  apply (subst (asm) ex2_op_code)
  using step_ex2_op_aux apply metis
  done

lemma step_ex2_op_intro[intro!]:
  assumes "io = Out 1 42"
    and "op' = ex2_op"
  shows "step io ex2_op op'"
  using assms apply -
  apply (subst ex2_op_code)
  apply auto
  done

lemma ex1_bisim_ex2_op:
  "ex1_op ~ ex2_op"
  by (coinduction rule: bisim_coinduct) auto

corec ex3_op where
  "ex3_op = choice2 (Write ex3_op (1::2) (42::nat)) (Silent ex3_op)"

lemma ex3_op_code:
  "ex3_op = Choice {|Write ex3_op (1::2) (42::nat), Silent ex3_op|}"
  by (subst ex3_op.code, simp)

lemma step_ex3_op_elim[elim!]:
  assumes "step io ex3_op op'"
  obtains "op' = ex3_op" "io = Out 1 42" | "op' = ex3_op" "io = Tau" 
  using assms
  apply atomize_elim
  apply (subst (asm) ex3_op_code)
  apply auto
  done

lemma step_ex3_op_intro1[intro]:
  assumes "io = Out 1 42"
    and "op' = ex3_op"
  shows "step io ex3_op op'"
  using assms apply -
  apply (subst ex3_op_code)
  apply auto
  done

lemma step_ex3_op_intro2[intro]:
  assumes "io = Tau"
    and "op' = ex3_op"
  shows "step io ex3_op op'"
  using assms apply -
  apply (subst ex3_op_code)
  apply auto
  done

lemma ex1_bisim_ex3_op:
  "ex1_op \<approx> ex3_op"
  by (coinduction rule: wbisim_coinduct) auto

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
    (cimage (\<lambda> p. id_Read_aux p (\<lambda> x. BENQ p x buf)) (c\<UU> :: 'm cset)) 
    (cimage (\<lambda> p. id_Write_aux (BTL p buf) p (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (c\<UU> :: 'm cset)))))"

abbreviation id_empty_op ("\<I>") where
  "\<I> \<equiv> id_op (\<lambda> _. [])"

lemma id_op_code:
  "id_op buf = Choice (cUn 
    (cimage (\<lambda> p. Read p ((\<lambda> x. id_op (BENQ p x buf)))) (c\<UU> :: 'm cset))
    (cimage (\<lambda> p. Write (id_op (BTL p buf)) p  (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (c\<UU> :: ('m :: {countable, defaults}) cset))))"
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
    apply (subst (asm) id_op_code, auto)+
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
  "choices (id_op buf) = cUn (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda>x. id_op (buf(p := bulk_benq [x] (buf p))))) c\<UU>)))
       (cUnion (cimage choices (cimage (\<lambda>p. Write (id_op (BTL p buf)) p (BHD p buf)) (cfilter (\<lambda>p. buf p \<noteq> []) c\<UU>))))"
  apply (subst id_op_code)
  apply (simp add: BTL_def BENQ_def)
  done

lemma id_op_reads:
  "sub_op (Read p f) (id_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>id_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) id_op_code, simp) 
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) id_op_code, simp; force) 
qed

lemma id_op_writes:
  "sub_op (Write op p x) (id_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>id_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) id_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) id_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) id_op_code, simp)
qed

lemma inputs_id_op[intro]:
  "inputs (id_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using id_op_reads by (metis inputs_sub_op_Read)
lemma inputs_id_op_alt[intro!]:
  "\<forall>x\<in>inputs (id_op buf). x \<notin> defaults"
  using inputs_id_op[unfolded subset_eq, simplified] by fast
lemma inputs_id_op_dest[dest!]:
  "x\<in>inputs (id_op buf) \<Longrightarrow> x \<notin> defaults"
  using inputs_id_op_alt by blast
lemma outputs_id_op[intro]:
  "outputs (id_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using id_op_writes by (metis outputs_sub_op_Write)
lemma outputs_id_op_alt[intro!]:
  "\<forall>x\<in>outputs (id_op buf). x \<notin> defaults"
  using outputs_id_op[unfolded subset_eq, simplified] by fast
lemma outputs_id_op_dest[dest!]:
  "x\<in>outputs (id_op buf) \<Longrightarrow> x \<notin> defaults"
  using outputs_id_op_alt by blast

lemma default_0[simp]: "x \<in> (defaults :: 0 set)"
  by transfer simp

lemma id_op_0_end_op:
  \<open>(\<I> :: ('b :: {countable, all_defaults}, 'b :: {countable, all_defaults}, 'd) op) ~ \<oslash>\<close>
  by (rule choices_Choice_bisim) auto

section \<open>User defined operators\<close>
  (* abbreviation buffered ("\<stileturn> _ \<turnstile>" [150]151) where
  "\<stileturn>op\<turnstile> \<equiv> \<I> \<bullet> op \<bullet> \<I>" *)

abbreviation post_buffered ("_ \<turnstile>" [150]151) where
  "op\<turnstile> \<equiv> op \<bullet> \<I>"

abbreviation pre_buffered ("\<stileturn>_" [150]151) where
  "\<stileturn>op \<equiv> \<I> \<bullet> op"

subsection \<open>Some properties about vdash\<close>

lemma scomp_op_id_left_absorb_gen:
  assumes "inputs op2 \<inter> defaults = {}"
  shows  "map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<approx> map_op projl projr (comp_op Some (buf1 >> buf2 >> buf3) op1 op2)"
  using assms proof (coinduction arbitrary: op1 op2 buf1 buf2 buf3 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1'a (id_op buf2))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Inp p x) op1 op1'a"
      for p :: 'd
        and x :: 'c
        and op1'a :: "('d, 'a, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         apply blast+
      done
    moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2')) op2'a"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Out p x) op2 op2'"
      for p :: 'b
        and x :: 'c
        and op2' :: "('a, 'b, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply blast
      apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some (BENQ q (BHD q buf2) buf3) (map_op projl projr (comp_op Some buf1 op1 (id_op (BTL q buf2)))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "q \<notin> defaults"
        and "buf2 q \<noteq> []"
      for q :: 'a
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         apply assumption
        apply (rule refl)+
      apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      done  
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some (BTL p buf3) (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2')) op2'a"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Inp p (BHD p buf3)) op2 op2'"
        and "buf3 p \<noteq> []"
      for p :: 'a
        and op2' :: "('a, 'b, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce
      apply (metis disjoint_iff_not_equal step_inputs_outputs subset_eq)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some (BENQ q xa buf1) op1'a (id_op buf2))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Out q xa) op1 op1'a"
      for xa :: 'c
        and op1'a :: "('d, 'a, 'c) op"
        and q :: 'a
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some (BTL pb buf1) op1 (id_op (BENQ pb (BHD pb buf1) buf2)))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "buf1 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1'a (id_op buf2))) op2)) op2'"
      if "inputs op2 \<inter> defaults = {}"
        and "step Tau op1 op1'a"
      for op1'a :: "('d, 'a, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce+
      done
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2')) op2'a"
      if "inputs op2 \<inter> defaults = {}"
        and "step Tau op2 op2'"
      for op2' :: "('a, 'b, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce+
      apply (metis disjoint_iff_not_equal step_inputs_outputs subset_eq)
      done
    ultimately show ?thesis
      using SIM1  by (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim!: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2' (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1' op2))"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Inp p x) op1 op1'"
      for p :: 'd
        and x :: 'c
        and op1' :: "('d, 'a, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         apply blast+
      done
    moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2'))"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Out p x) op2 op2'"
      for p :: 'b
        and x :: 'c
        and op2' :: "('a, 'b, 'c) op"
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         prefer 2
         apply (rule refl)
        apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
       apply (rule refl)
      apply fast
      done    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2' (map_op projl projr (comp_op Some ((BENQ q x buf1 >> buf2) >> buf3) op1' op2))"
      if "inputs op2 \<inter> defaults = {}"
        and "step (Out q x) op1 op1'"
      for x :: 'c
        and op1' :: "('d, 'a, 'c) op"
        and q :: 'a
      using that 
      apply (intro exI conjI[rotated] wbc_base)
         apply assumption+
        apply (rule refl)+
      apply fast
      done
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((BTL p buf1 >> buf2) >> buf3) op1 op2'))"
      if "step (Inp p (BHD p buf1)) op2 op2'"
        and "buf1 p \<noteq> []"
        and "inputs op2 \<inter> defaults = {}"
        and "buf3 p = []"
        and "buf2 p = []"
      for p :: 'a
        and op2' :: "('a, 'b, 'c) op"
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2))
     (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some (BTL p buf1) op1 (id_op (BENQ p (BHD p buf1) buf2)))) op2))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Tau)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_id_op_Read)
                  apply simp_all
        apply (meson step_inputs_not_in_defaults)
        done
      also have "step Tau \<dots> 
                 (map_op projl projr (comp_op Some (BENQ p (BHD p buf1) buf3) (map_op projl projr (comp_op Some (BTL p buf1) op1 (id_op buf2))) op2))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                  apply simp_all
        apply (meson step_inputs_not_in_defaults)
        done
      also have "step Tau \<dots> 
                 (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some (BTL p buf1) op1 (id_op buf2))) op2'))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro exI conjI[rotated] wbc_base)
           prefer 2
           apply (rule refl)
          apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
         apply (rule refl)
        apply blast
        done
    qed
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((buf1 >> BTL p buf2) >> buf3) op1 op2'))"
      if "step (Inp p (BHD p buf2)) op2 op2'"
        and "inputs op2 \<inter> defaults = {}"
        and "buf3 p = []"
        and "buf2 p \<noteq> []"
      for p :: 'a
        and op2' :: "('a, 'b, 'c) op"
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2))
     (map_op projl projr (comp_op Some (BENQ p (BHD p buf2) buf3) (map_op projl projr (comp_op Some buf1 op1 (id_op (BTL p buf2)))) op2))"
        using that by auto
      also have "step Tau \<dots>
                 (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op (BTL p buf2)))) op2'))"
        using that by auto
      finally show ?thesis 
        using that apply -
        apply (intro exI conjI[rotated] wbc_base)
           prefer 2
           apply (rule refl)
          apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
         apply (rule refl)
        apply blast
        done
    qed
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((buf1 >> buf2) >> BTL p buf3) op1 op2'))"
      if "step (Inp p (BHD p buf3)) op2 op2'"
        and "inputs op2 \<inter> defaults = {}"
        and "buf3 p \<noteq> []"
      for p :: 'a
        and op2' :: "('a, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
         prefer 2
         apply (rule refl)
        apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
       apply (rule refl)
      apply force
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2' (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1' op2))"
      if "inputs op2 \<inter> defaults = {}"
        and "step Tau op1 op1'"
      for op1' :: "('d, 'a, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
         prefer 3
         apply (rule refl)
        apply assumption+
       apply (rule refl)
      apply force
      done
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2)) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf2 buf3. op1axx = map_op projl projr (comp_op Some buf3 (map_op projl projr (comp_op Some buf1 op1 (id_op buf2))) op2) \<and> op2axx = map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2) \<and> inputs op2 \<inter> (defaults::'a set) = {}) op2'a (map_op projl projr (comp_op Some ((buf1 >> buf2) >> buf3) op1 op2'))"
      if "inputs op2 \<inter> defaults = {}"
        and "step Tau op2 op2'"
      for op2' :: "('a, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
         prefer 2
         apply (rule refl)
        apply (metis disjoint_iff_not_equal in_mono step_inputs_outputs)
       apply (rule refl)
      apply force
      done
    ultimately show ?thesis
      using SIM2  by (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits)
  qed
qed

lemma scomp_op_id_left_absorb:
  assumes "inputs op2 \<inter> defaults = {}"
  shows  "op1\<turnstile> \<bullet> op2 \<approx> op1 \<bullet> op2"
  unfolding scomp_op_def using assms scomp_op_id_left_absorb_gen[of op2  "\<lambda> _. []"  "\<lambda> _. []" op1  "\<lambda> _. []"] by force

lemma map_op_id_f_left_absorb_gen:
  \<open>map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op))
  \<approx> map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))\<close>
proof (coinduction arbitrary: buf1 buf2 op rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) (map_op projl projr (comp_op Some buf2 (id_op (BENQ pa xa buf1)) (map_op id f op))) op2'"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'c
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p x) (map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) (map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op''a))) op2'"
      if "step io'a op op''a"
        and "map_IO id f id io'a = Out p x"
      for p :: 'b
        and x :: 'c
        and io'a :: "('a, 'd, 'c) IO"
        and op''a :: "('a, 'd, 'c) op"
    proof (cases io'a)
      case (Inp x11 x12)
      from this that show ?thesis
        by (fastforce del: wbc_base intro!: wbc_base)
    next
      case (Out x21 x22)
      from this that show ?thesis
        by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    next
      case Tau
      from this that show ?thesis
        by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) (map_op projl projr (comp_op Some (BENQ pa (BHD pa buf1) buf2) (id_op (BTL pa buf1)) (map_op id f op))) op2'"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) (map_op projl projr (comp_op Some (BTL p buf2) (id_op buf1) (map_op id f op''a))) op2'"
      if "buf2 p \<noteq> []"
        and "step io'a op op''a"
        and "map_IO id f id io'a = Inp p (BHD p buf2)"
      for p :: 'a
        and io'a :: "('a, 'd, 'c) IO"
        and op''a :: "('a, 'd, 'c) op"
      using that
      apply (intro exI conjI[rotated, OF wbc_base])
       apply simp
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(1))
      apply auto[1]
      by (metis IO.collapse(1) IO.disc(1) IO.map_disc_iff(1) IO.map_sel(1) IO.map_sel(2) IO.sel(1) IO.sel(2) id_def)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) (map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op''a))) op2'"
      if "step Tau op op''a"
      for op''a :: "('a, 'd, 'c) op"
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' (map_op id f (map_op projl projr (comp_op Some buf2 (id_op (BENQ pa xa buf1)) op)))"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'c
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'a. wstep (Out (f p) x) (map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op))) op2'a \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2'a (map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op2')))"
      if "step (Out p x) op op2'"
      for p :: 'd
        and x :: 'c
        and op2' :: "('a, 'd, 'c) op"
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' (map_op id f (map_op projl projr (comp_op Some (BENQ pa (BHD pa buf1) buf2) (id_op (BTL pa buf1)) op)))"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op))) op2'a \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2'a (map_op id f (map_op projl projr (comp_op Some (BTL p buf2) (id_op buf1) op2')))"
      if "step (Inp p (BHD p buf2)) op op2'"
        and "buf2 p \<noteq> []"
      for p :: 'a
        and op2' :: "('a, 'd, 'c) op"
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op))) op2'a \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op projl projr (comp_op Some buf2 (id_op buf1) (map_op id f op)) \<and> op2 = map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2'a (map_op id f (map_op projl projr (comp_op Some buf2 (id_op buf1) op2')))"
      if "step Tau op op2'"
      for op2' :: "('a, 'd, 'c) op"
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases)
  qed
qed

lemma map_op_id_f_left_absorb:
  \<open>\<stileturn>(map_op id f op) \<approx> map_op id f (\<stileturn>op)\<close>
  unfolding scomp_op_def
  using map_op_id_f_left_absorb_gen by blast

lemma map_op_out_id_vdash_gen:
  "map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<approx> map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))"
proof (coinduction arbitrary: op buf1 buf2 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp (f p) x) (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some buf2 op1' (id_op buf1)))) op2'"
      if "step (Inp p x) op op1'"
      for p :: 'd
        and x :: 'c
        and op1' :: "('d, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf1)) (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op (BTL pa buf1))))) op2'"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some (BENQ q x buf2) op1' (id_op buf1)))) op2'"
      if "step (Out q x) op op1'"
      for x :: 'c
        and op1' :: "('d, 'b, 'c) op"
        and q :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some (BTL pa buf2) op (id_op (BENQ pa (BHD pa buf2) buf1))))) op2'"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) (map_op f id (map_op projl projr (comp_op Some buf2 op1' (id_op buf1)))) op2'"
      if "step Tau op op1'"
      for op1' :: "('d, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some buf2 (map_op f id op''a) (id_op buf1)))"
      if "step io'a op op''a"
        and "map_IO f id id io'a = Inp p x"
      for p :: 'a
        and x :: 'c
        and io'a :: "('d, 'b, 'c) IO"
        and op''a :: "('d, 'b, 'c) op"
    proof (cases "io'a")
      case (Inp x11 x12)
      from this that show ?thesis 
        using that apply -
        apply hypsubst_thin
        apply (intro exI conjI[rotated] wbc_base)
          apply (rule refl)+
        apply fastforce
        done
    next
      case (Out x21 x22)
      from this that show ?thesis 
        using that apply -
        apply hypsubst_thin
        apply (intro exI conjI[rotated] wbc_base)
          apply (rule refl)+
        apply fastforce
        done
    next
      case Tau
      from this that show ?thesis 
        using that apply -
        apply hypsubst_thin
        apply (intro exI conjI[rotated] wbc_base)
          apply (rule refl)+
        apply fastforce
        done
    qed
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf1)) (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op (BTL pa buf1))))"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some (BENQ q x buf2) (map_op f id op''a) (id_op buf1)))"
      if "step io'a op op''a"
        and "map_IO f id id io'a = Out q x"
      for x :: 'c
        and q :: 'b
        and io'a :: "('d, 'b, 'c) IO"
        and op''a :: "('d, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply (rule refl)+
      apply (smt (z3) IO.exhaust IO.simps(15) IO.simps(16) IO.simps(17) IO.simps(4) id_def step_Tau_comp_op_L_alt step_star_map_op step_wstep wstep_steps_Tau)
      done     moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some (BTL pa buf2) (map_op f id op) (id_op (BENQ pa (BHD pa buf2) buf1))))"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'b
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op f id (map_op projl projr (comp_op Some buf2 op (id_op buf1))) \<and> op2xx = map_op projl projr (comp_op Some buf2 (map_op f id op) (id_op buf1))) op2' (map_op projl projr (comp_op Some buf2 (map_op f id op''a) (id_op buf1)))"
      if "step Tau op op''a"
      for op''a :: "('d, 'b, 'c) op"
      using that apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply auto
      done
    ultimately show ?thesis
      using SIM2  by (auto elim !: step_id_op_cases step_comp_op_elim step_map_op_elim split: if_splits)
  qed
qed

lemma map_op_out_id_vdash:
  "map_op f id (op\<turnstile>) \<approx> (map_op f id op)\<turnstile>"
  unfolding scomp_op_def using map_op_out_id_vdash_gen by force

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

lemma scomp_op_dummy_source:
  \<open>\<exclamdown> \<bullet> \<exclamdown> \<approx> \<exclamdown>\<close>
  unfolding scomp_op_def
  by (coinduction rule: wbisim_coinduct_upto'')
    (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases)+

lemma map_op_Inr_id_left_identity_gen:
  \<open>map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op))
  \<approx> map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2)
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>) \<parallel> id_op buf1)
      (map_op Inr id op))\<close>
  unfolding pcomp_op_def
proof (coinduction arbitrary: buf1 buf2 op rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inr pa::'a + 'b) xa) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op))) (map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op (BENQ pa xa buf1)) op))) op2'"
      if "pa \<notin> defaults"
      for pa :: 'b
        and xa :: 'd
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'e, 'd) op) \<I>)) (id_op buf1)) (map_op Inr id op))) op2'a \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op))) (map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op2'))) op2'a"
      if "step (Out p x) op op2'"
      for p :: 'c
        and x :: 'd
        and op2' :: "('b, 'c, 'd) op"
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'e, 'd) op) \<I>)) (id_op buf1)) (map_op Inr id op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op))) (map_op Inr id (map_op projl projr (comp_op Some (BENQ pa (BHD pa buf1) buf2) (id_op (BTL pa buf1)) op))) op2'"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'e, 'd) op) \<I>)) (id_op buf1)) (map_op Inr id op))) op2'a \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op))) (map_op Inr id (map_op projl projr (comp_op Some (BTL p buf2) (id_op buf1) op2'))) op2'a"
      if "step (Inp p (BHD p buf2)) op op2'"
        and "buf2 p \<noteq> []"
      for p :: 'b
        and op2' :: "('b, 'c, 'd) op"
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'e, 'd) op) \<I>)) (id_op buf1)) (map_op Inr id op))) op2'a \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op))) (map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op2'))) op2'a"
      if "step Tau op op2'"
      for op2' :: "('b, 'c, 'd) op"
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inr pb::'a + 'b) xb) (map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op))) op2' (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op (BENQ pb xb buf1))) (map_op Inr id op)))"
      if "pb \<notin> defaults"
      for pb :: 'b
        and xb :: 'd
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p x) (map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'e, 'd) op) \<I>)) (id_op buf1)) (map_op Inr id op))) op2' (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op''a)))"
      if "step io'a op op''a"
        and "map_IO (Inr::'b \<Rightarrow> 'e + 'b) id id io'a = Out p x"
      for p :: 'c
        and x :: 'd
        and io'a :: "('b, 'c, 'd) IO"
        and op''a :: "('b, 'c, 'd) op"
    proof (cases io'a)
      case (Inp x11 x12)
      from this that show ?thesis
        by (fastforce del: wbc_base intro!: wbc_base)
    next
      case (Out x21 x22)
      from this that show ?thesis
        by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    next
      case Tau
      from this that show ?thesis
        by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'e, 'd) op) \<I>)) (id_op buf1)) (map_op Inr id op))) op2' (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ pb (BHD pb buf1) buf2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op (BTL pb buf1))) (map_op Inr id op)))"
      if "pb \<notin> defaults"
        and "buf1 pb \<noteq> []"
      for pb :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'e, 'd) op) \<I>)) (id_op buf1)) (map_op Inr id op))) op2' (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BTL x2 buf2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op''a)))"
      if "step io'a op op''a"
        and "map_IO Inr id id io'a = Inp (Inr x2::'e + 'b) (BHD x2 buf2)"
        and "buf2 x2 \<noteq> []"
      for io'a :: "('b, 'c, 'd) IO"
        and op''a :: "('b, 'c, 'd) op"
        and x2 :: 'b
    proof (cases io'a)
      case (Inp x11 x12)
      from this that show ?thesis
        by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    next
      case (Out x21 x22)
      from this that show ?thesis
        by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    next
      case Tau
      from this that show ?thesis
        by (fastforce del: wbc_base intro!: wbc_base)
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 op. op1 = map_op Inr id (map_op projl projr (comp_op Some buf2 (id_op buf1) op)) \<and> op2 = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::('a, 'e, 'd) op) \<I>)) (id_op buf1)) (map_op Inr id op))) op2' (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op (Some::'e \<Rightarrow> _ option) (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (map_op Inr id op''a)))"
      if "step Tau op op''a"
      for op''a :: "('b, 'c, 'd) op"
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce+)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits)
  qed
qed

lemma map_op_Inr_id_left_identity:
  \<open>map_op Inr id (\<stileturn>op) \<approx> (\<exclamdown> \<parallel> \<I>) \<bullet> (map_op Inr id op)\<close>
  unfolding scomp_op_def
  using map_op_Inr_id_left_identity_gen[of \<open>\<lambda>_. []\<close>  \<open>\<lambda>_. []\<close>]
  by simp

section \<open>sink_op\<close>                                     
corec sink_op :: "('m :: {countable, defaults}, 'o, 'd) op" ("!") where
  "sink_op = Choice ((cimage (\<lambda> p. Read p (\<lambda> x. sink_op)) (c\<UU> :: 'm cset)))"

lemma step_sink_op_Inp:
  assumes \<open>step io sink_op op\<close>
    and \<open>io = Inp p x\<close>
  obtains \<open>op = sink_op\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) sink_op.code)
  apply auto
  done

lemma no_step_sink_op_Out:
  assumes \<open>step io sink_op op\<close>
    and \<open>io = Out p x\<close>
  obtains False
  using assms
  apply (subst (asm) sink_op.code)
  apply auto
  done

lemma no_step_sink_op_Tau:
  assumes \<open>step io sink_op op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) sink_op.code)
  apply auto
  done

lemma step_sink_op:
  assumes \<open>step io sink_op op\<close>
  obtains p x where \<open>io = Inp p x\<close> \<open>p \<notin> defaults\<close> \<open>op = sink_op\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) sink_op.code)
  apply auto
  done

lemma step_sink_op_Read[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> step (Inp p x) sink_op sink_op\<close>
  apply (subst sink_op.code)
  apply auto
  done

lemma choices_sink_op[simp]:
  \<open>choices sink_op =
  cimage (\<lambda> p. Read p (\<lambda> x. sink_op)) c\<UU>\<close>
  apply (subst sink_op.code)
  apply force
  done

corec sink_buf_op :: "_ \<Rightarrow> ('m :: {countable, defaults}, 'o, 'd) op" where
  "sink_buf_op buf = Choice ((cimage (\<lambda> p. Read p (\<lambda> x. (sink_buf_op (BENQ p x buf)))) (c\<UU> :: 'm cset)))"

lemma step_sink_buf_op_Inp:
  assumes \<open>step io (sink_buf_op buf) op\<close>
    and \<open>io = Inp p x\<close>
  obtains \<open>op = (sink_buf_op (BENQ p x buf))\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) sink_buf_op.code)
  apply auto
  done

lemma no_step_sink_buf_op_Out[elim!]:
  assumes \<open>step io (sink_buf_op buf) op\<close>
    and \<open>io = Out p x\<close>
  obtains False
  using assms
  apply (subst (asm) sink_buf_op.code)
  apply auto
  done

lemma no_step_sink_buf_op_Tau[elim!]:
  assumes \<open>step io (sink_buf_op buf) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) sink_buf_op.code)
  apply auto
  done

lemma step_sink_buf_op:
  assumes \<open>step io (sink_buf_op buf) op\<close>
  obtains p x where \<open>io = Inp p x\<close> \<open>p \<notin> defaults\<close> \<open>op = sink_buf_op (BENQ p x buf)\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) sink_buf_op.code)
  apply auto
  done

lemma step_sink_buf_op_Read[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BENQ p x buf \<Longrightarrow> step (Inp p x) (sink_buf_op buf) (sink_buf_op buf')\<close>
  apply (subst sink_buf_op.code)
  apply auto
  done

lemma sink_buf_op_sink:
  "sink_buf_op buf ~ sink_op"
proof (coinduction arbitrary: buf rule: bisim_coinduct)
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. step (Inp p x) (!::('a, 'b, 'c) op) op2' \<and> bisim_R (\<lambda>op1xx op2xx. (\<exists>buf. op1xx = sink_buf_op buf) \<and> op2xx = !) (sink_buf_op (BENQ p x buf)) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'c
      using that by(intro exI conjI[rotated, OF b_base], force, force)
    then show ?thesis
      using SIM1 by (auto elim !: step_sink_buf_op)
  qed
next
  case SIM2
  then show ?case 
  proof -
    have "\<exists>op2'. step (Inp p x) (sink_buf_op buf) (op2'::('a, 'b, 'c) op) \<and> bisim_R (\<lambda>op1xx op2xx. (\<exists>buf. op1xx = sink_buf_op buf) \<and> op2xx = !) op2' !"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'c
      using that by(intro exI conjI[rotated, OF b_base], force, force)
    then show ?thesis
      using SIM2 by (auto elim !: step_sink_op)
  qed
qed


lemma id_sink_op_sink_op:
  "map_op projl projr (comp_op Some buf2 (id_op buf1) !) \<approx> !"
  unfolding scomp_op_def
proof (coinduction arbitrary: buf1 buf2 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (!::('a, 'b, 'c) op) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf1 buf2. op1xx = map_op projl projr (comp_op Some buf2 (id_op buf1) !)) \<and> op2xx = !) (map_op projl projr (comp_op Some buf2 (id_op (BENQ pa xa buf1)) !)) op2'"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'c
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    moreover have "\<exists>op2'. (step (Tau::('a, 'b, 'c) IO))\<^sup>*\<^sup>* ! op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf1 buf2. op1xx = map_op projl projr (comp_op Some buf2 (id_op buf1) !)) \<and> op2xx = !) (map_op projl projr (comp_op Some (BENQ pa (BHD pa buf1) buf2) (id_op (BTL pa buf1)) !)) op2'"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    moreover have "\<exists>op2'. (step (Tau::('a, 'b, 'c) IO))\<^sup>*\<^sup>* ! op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf1 buf2. op1xx = map_op projl projr (comp_op Some buf2 (id_op buf1) !)) \<and> op2xx = !) (map_op projl projr (comp_op Some (BTL pa buf2) (id_op buf1) !)) op2'"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    ultimately show ?thesis
      using SIM1 by (auto 0 0 elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_sink_op split: if_splits sum.splits)
  qed
next
  case SIM2
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some buf2 (id_op buf1) (!::('a, 'b, 'c) op))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf1 buf2. op1xx = map_op projl projr (comp_op Some buf2 (id_op buf1) !)) \<and> op2xx = !) op2' !"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'c
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    then show ?thesis
      using SIM2  by (auto 0 0 elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_sink_op split: if_splits sum.splits)
  qed
qed


lemma sink_sink_gen:
  "map_op projl projr (comp_op Some buf ! !) \<approx> !"
proof (coinduction arbitrary: buf rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (!::('a, 'b, 'c) op) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf. op1xx = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) buf ! !)) \<and> op2xx = !) (map_op projl projr (comp_op Some buf ! !)) op2'"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'c
      using that by (intro exI conjI[rotated] wbc_base; force)
    moreover have "\<exists>op2'. (step (Tau::('a, 'b, 'c) IO))\<^sup>*\<^sup>* ! op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf. op1xx = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) buf ! !)) \<and> op2xx = !) (map_op projl projr (comp_op Some (BTL pa buf) ! !)) op2'"
      if "buf pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'd
      using that by (intro exI conjI[rotated] wbc_base; force)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_sink_op)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim!: step_map_op_elim step_comp_op_elim step_sink_op ;hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some buf ! (!::('d, 'b, 'c) op))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf. op1xx = map_op projl projr (comp_op (Some::'d \<Rightarrow> _ option) buf ! !)) \<and> op2xx = !) op2' !"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'c
      using that by (intro exI conjI[rotated] wbc_base; force)
    then show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_sink_op)
  qed
qed

lemma sink_sink:
  "! \<bullet> ! \<approx> !"
  unfolding scomp_op_def using sink_sink_gen by blast


lemma map_op_id_Inr_move_vdash_gen:
  "map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<approx> map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (! \<parallel> (id_op buf2)))"
proof (coinduction arbitrary: op buf1 buf2 A rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
    explore (auto elim!: step_id_op_cases step_map_op_elim step_comp_op_elim step_sink_op simp add: pcomp_op_def ;hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum (A::'e \<Rightarrow> 'd buf) buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))) (map_op id Inr (map_op projl projr (comp_op Some buf1 op1' (id_op buf2)))) op2'"
      if "step (Inp p x) op op1'"
      for p :: 'a
        and x :: 'd
        and op1' :: "('a, 'c, 'd) op"
      using that by (intro exI conjI[rotated] wbc_base; force)
    moreover have "\<exists>op2'. wstep (Out (Inr pa::'b + 'c) (BHD pa buf2)) (map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum (A::'e \<Rightarrow> 'd buf) buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))) (map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op (BTL pa buf2))))) op2'"
      if "pa \<notin> defaults"
        and "buf2 pa \<noteq> []"
      for pa :: 'c
      using that 
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply (rule refl)+
      apply force
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum (A::'e \<Rightarrow> 'd buf) buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))) (map_op id Inr (map_op projl projr (comp_op Some (BENQ q x buf1) op1' (id_op buf2)))) op2'"
      if "step (Out q x) op op1'"
      for x :: 'd
        and op1' :: "('a, 'c, 'd) op"
        and q :: 'c
      using that 
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply (rule refl)+
      apply force
      done    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum (A::'e \<Rightarrow> 'd buf) buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))) (map_op id Inr (map_op projl projr (comp_op Some (BTL pa buf1) op (id_op (BENQ pa (BHD pa buf1) buf2))))) op2'"
      if "buf1 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'c
      using that 
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply (rule refl)+
      apply force
      done    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum (A::'e \<Rightarrow> 'd buf) buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))) (map_op id Inr (map_op projl projr (comp_op Some buf1 op1' (id_op buf2)))) op2'"
      if "step Tau op op1'"
      for op1' :: "('a, 'c, 'd) op"
      using that 
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply (rule refl)+
      apply force
      done
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_id_op_cases step_map_op_elim step_comp_op_elim step_sink_op simp add: pcomp_op_def)
  qed
next
  case SIM2
  then show ?case
    apply -
    explore (auto simp add: pcomp_op_def elim !: step_id_op_cases step_map_op_elim step_comp_op_elim step_sink_op; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2))))) op2' (map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op''a) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))"
      if "step io'a op op''a"
        and "map_IO id (Inr::'c \<Rightarrow> 'e + 'c) id io'a = Inp p x"
      for p :: 'a
        and x :: 'd
        and io'a :: "('a, 'c, 'd) IO"
        and op''a :: "('a, 'c, 'd) op"
      using that apply -
      apply (cases "io'a"; simp)
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        apply (rule refl)+
      apply force
      done
    moreover have "\<exists>op2'. wstep (Out (Inr pb::'b + 'c) (BHD pb buf2)) (map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum (A::'e \<Rightarrow> 'd buf) buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))) op2' (map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op (BTL pb buf2)))))"
      if "pb \<notin> defaults"
        and "buf2 pb \<noteq> []"
      for pb :: 'c
      using that by (intro exI conjI[rotated] wbc_base; force)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2))))) op2' (map_op projl projr (comp_op Some (BENQ q x (case_sum A buf1)) (map_op id Inr op''a) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))"
      if "step io'a op op''a"
        and "map_IO id Inr id io'a = Out q x"
      for x :: 'd
        and q :: "'e + 'c"
        and io'a :: "('a, 'c, 'd) IO"
        and op''a :: "('a, 'c, 'd) op"
      using that apply -
      apply (cases "io'a"; simp)
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        defer
        apply (rule refl)+
       defer
       apply force+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2))))) op2' (map_op projl projr (comp_op Some (case_sum (BTL pb A) buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))"
      if "A pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'e
      using that 
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        defer
        apply (rule refl)+
       defer
       apply force+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2))))) op2' (map_op projl projr (comp_op Some (case_sum A (BTL pb buf1)) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op (BENQ pb (BHD pb buf1) buf2)))))"
      if "buf1 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'c
      using that 
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        defer
        apply (rule refl)+
       defer
       apply force+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>op buf1 buf2. op1xx = map_op id Inr (map_op projl projr (comp_op Some buf1 op (id_op buf2))) \<and> (\<exists>A. op2xx = map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op) (comp_op (\<lambda>_. None) (\<lambda>_. []) (!::('e, 'b, 'd) op) (id_op buf2))))) op2' (map_op projl projr (comp_op Some (case_sum A buf1) (map_op id Inr op''a) (comp_op (\<lambda>_. None) (\<lambda>_. []) ! (id_op buf2))))"
      if "step Tau op op''a"
      for op''a :: "('a, 'c, 'd) op"
      using that 
      apply -
      apply (intro exI conjI[rotated] wbc_base)
        defer
        apply (rule refl)+
       defer
       apply force+
      done
    ultimately show ?thesis
      using SIM2 by (auto simp add: pcomp_op_def elim !: step_id_op_cases step_map_op_elim step_comp_op_elim step_sink_op)
  qed
qed

lemma map_op_id_Inr_move_vdash:
  "map_op id Inr (op\<turnstile>) \<approx> (map_op id Inr op) \<bullet> (! \<parallel> \<I>)"
  unfolding scomp_op_def using map_op_id_Inr_move_vdash_gen[of "\<lambda> _. []" op "\<lambda> _. []" "\<lambda> _. []"] by simp

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
    (cimage (\<lambda> p. transp_Read_aux p (\<lambda> x. BENQ p x buf)) (c\<UU> :: ('m + 'n) cset)) 
    (cimage (\<lambda> p. transp_Write_aux (BTL p buf) (case_sum Inr Inl p) (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (c\<UU> :: ('m + 'n) cset)))))"


lemma transp_op_code:
  "transp_op buf = Choice (cUn 
    (cimage (\<lambda> p. Read p (\<lambda> x. transp_op (BENQ p x buf))) (c\<UU> :: ('m :: {countable, defaults} + 'n :: {countable, defaults}) cset)) 
    (cimage (\<lambda> p. Write (transp_op (BTL p buf)) (case_sum Inr Inl p) (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (c\<UU> :: ('m + 'n) cset))))"
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
  apply (simp add: Set.filter_def \<UU>_def split: sum.splits)
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
    apply auto
    done
  subgoal for p x
    apply (subst (asm) transp_op_code)
    apply (auto simp add: Set.filter_def \<UU>_def split: sum.splits)
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
  (cUnion (cimage choices (cimage (\<lambda> p. Read p (\<lambda> x. transp_op (buf(p := bulk_benq [x] (buf p))))) c\<UU>)))
  (cUnion (cimage choices (cimage (\<lambda> p. Write (transp_op (BTL p buf)) (case_sum Inr Inl p) (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) c\<UU>))))\<close>
  apply (subst transp_op_code)
  apply (simp add: BTL_def BENQ_def)
  done

lemma transp_op_reads:
  "sub_op (Read p f) (transp_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>transp_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) transp_op_code, simp)
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) transp_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) transp_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) transp_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) transp_op_code, simp; force)
qed

lemma inputs_transp_op[intro]:
  "inputs (transp_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using transp_op_reads by (metis inputs_sub_op_Read)

lemma transp_op_writes:
  "sub_op (Write op p x) (transp_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>transp_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) transp_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) transp_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) transp_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case
    by (subst (asm) (2) transp_op_code, (auto split: sum.splits)[1]) force+
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) transp_op_code, simp)
qed

lemma outputs_transp_op[intro]:
  "outputs (transp_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using transp_op_writes by (metis outputs_sub_op_Write)

lemma transp_id_absorb_left_gen:
  \<open>transp_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3'))
  \<approx> map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (id_op (case_sum buf1 buf1'))
      (transp_op (case_sum buf3 buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (BENQ p x (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')))) op2'"
      if "p \<notin> defaults"
      for p :: "'a + 'b"
        and x :: 'c
      using that by (cases p) (fastforce del: wbc_base intro!: wbc_base)+
    moreover have "\<exists>op2'. wstep (Out (Inl x1a) (BHD x1a buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((BTL x1a buf1' >> buf2') >> buf3'))) op2'"
      if "buf1' x1a \<noteq> []"
        and "x1a \<notin> defaults"
        and "buf2' x1a = []"
        and "buf3' x1a = []"
      for x1a :: 'b
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (id_op (case_sum buf1 buf1'))
    (transp_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x1a (BHD x1a buf1') buf2'))
    (id_op (case_sum buf1 (BTL x1a buf1')))
    (transp_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (id_op (case_sum buf1 (BTL x1a buf1')))
    (transp_op (case_sum buf3 (BENQ x1a (BHD x1a buf1') buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inl x1a) (BHD x1a buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (id_op (case_sum buf1 (BTL x1a buf1')))
    (transp_op (case_sum buf3 buf3'))))\<close>
        using that by (force intro!: step_map_op[of \<open>Out (Inr (Inl x1a)) (BHD x1a buf1')\<close>])
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1a) (BHD x1a buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x1a buf2') >> buf3'))) op2'"
      if "x1a \<notin> defaults"
        and "buf2' x1a \<noteq> []"
        and "buf3' x1a = []"
      for x1a :: 'b
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (id_op (case_sum buf1 buf1'))
    (transp_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL x1a buf2'))
    (id_op (case_sum buf1 buf1'))
    (transp_op (case_sum buf3 (BENQ x1a (BHD x1a buf2') buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inl x1a) (BHD x1a buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL x1a buf2'))
    (id_op (case_sum buf1 buf1'))
    (transp_op (case_sum buf3 buf3'))))\<close>
        using that by (force intro!: step_map_op[of \<open>Out (Inr (Inl x1a)) (BHD x1a buf2')\<close>])
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1a) (BHD x1a buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> BTL x1a buf3'))) op2'"
      if "x1a \<notin> defaults"
        and "buf2' x1a = []"
        and "buf3' x1a \<noteq> []"
      for x1a :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base]) force+
    moreover have "\<exists>op2'. wstep (Out (Inl x1a) (BHD x1a buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> BTL x1a buf3'))) op2'"
      if "x1a \<notin> defaults"
        and "buf2' x1a \<noteq> []"
        and "buf3' x1a \<noteq> []"
      for x1a :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base]) force+
    moreover have "\<exists>op2'. wstep (Out (Inr x2a) (BHD x2a buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (case_sum ((BTL x2a buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2'"
      if "buf1 x2a \<noteq> []"
        and "x2a \<notin> defaults"
        and "buf2 x2a = []"
        and "buf3 x2a = []"
      for x2a :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (id_op (case_sum buf1 buf1'))
    (transp_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BENQ x2a (BHD x2a buf1) buf2) buf2')
    (id_op (case_sum (BTL x2a buf1) buf1'))
    (transp_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (id_op (case_sum (BTL x2a buf1) buf1'))
    (transp_op (case_sum (BENQ x2a (BHD x2a buf1) buf3) buf3'))))\<close>
        using that by auto
      also have \<open>step (Out (Inr x2a) (BHD x2a buf1)) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (id_op (case_sum (BTL x2a buf1) buf1'))
    (transp_op (case_sum buf3 buf3'))))\<close>
        using that by (force intro!: step_map_op[of \<open>Out (Inr (Inr x2a)) (BHD x2a buf1)\<close>])
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2a) (BHD x2a buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> BTL x2a buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2'"
      if "x2a \<notin> defaults"
        and "buf2 x2a \<noteq> []"
        and "buf3 x2a = []"
      for x2a :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (id_op (case_sum buf1 buf1'))
    (transp_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BTL x2a buf2) buf2')
    (id_op (case_sum buf1 buf1'))
    (transp_op (case_sum (BENQ x2a (BHD x2a buf2) buf3) buf3'))))\<close>
        using that by auto
      also have \<open>step (Out (Inr x2a) (BHD x2a buf2)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL x2a buf2) buf2')
    (id_op (case_sum buf1 buf1'))
    (transp_op (case_sum buf3 buf3'))))\<close>
        using that by (force intro!: step_map_op[of \<open>Out (Inr (Inr x2a)) (BHD x2a buf2)\<close>])
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2a) (BHD x2a buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2) >> BTL x2a buf3) ((buf1' >> buf2') >> buf3'))) op2'"
      if "x2a \<notin> defaults"
        and "buf2 x2a = []"
        and "buf3 x2a \<noteq> []"
      for x2a :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) force+
    moreover have "\<exists>op2'. wstep (Out (Inr x2a) (BHD x2a buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2) >> BTL x2a buf3) ((buf1' >> buf2') >> buf3'))) op2'"
      if "x2a \<notin> defaults"
        and "buf2 x2a \<noteq> []"
        and "buf3 x2a \<noteq> []"
      for x2a :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) force+
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_transp_op_cases split: sum.splits if_splits)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (BENQ pa xa (case_sum buf1 buf1'))) (transp_op (case_sum buf3 buf3'))))"
      if "pa \<notin> defaults"
      for pa :: "'a + 'b"
        and xa :: 'c
      using that by (cases pa) (fastforce del: wbc_base intro!: wbc_base)+
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3')) (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BTL x1 buf3')))))"
      if "x1 \<notin> defaults"
        and "buf3' x1 \<noteq> []"
      for x1 :: 'b
      using that by (force del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3)) (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum (BTL x2 buf3) buf3'))))"
      if "x2 \<notin> defaults"
        and "buf3 x2 \<noteq> []"
      for x2 :: 'a
      using that by (force del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (id_op (case_sum (BTL x1 buf1) buf1')) (transp_op (case_sum buf3 buf3'))))"
      if "x1 \<notin> defaults"
        and "buf1 x1 \<noteq> []"
      for x1 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1') buf2')) (id_op (case_sum buf1 (BTL x2 buf1'))) (transp_op (case_sum buf3 buf3'))))"
      if "x2 \<notin> defaults"
        and "buf1' x2 \<noteq> []"
      for x2 :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))))"
      if "x1 \<notin> defaults"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2')) (id_op (case_sum buf1 buf1')) (transp_op (case_sum buf3 (BENQ x2 (BHD x2 buf2') buf3')))))"
      if "x2 \<notin> defaults"
        and "buf2' x2 \<noteq> []"
      for x2 :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_transp_op_cases split: sum.splits)
  qed
qed

lemma transp_id_absorb_left:
  \<open>\<X> \<approx> \<stileturn>\<X>\<close>
  unfolding scomp_op_def
  using transp_id_absorb_left_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

lemma transp_id_absorb_right_gen:
  \<open>transp_op (case_sum (buf1 >> buf2' >> buf3') (buf1' >> buf2 >> buf3))
  \<approx> map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (transp_op (case_sum buf1 buf1'))
      (id_op (case_sum buf3 buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (BENQ p x (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)))) op2'"
      if "p \<notin> defaults"
      for p :: "'a + 'b"
        and x :: 'c
      using that by (cases p) (fastforce del: wbc_base intro!: wbc_base)+
    moreover have "\<exists>op2'. wstep (Out (Inl x1a) (BHD x1a buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((BTL x1a buf1' >> buf2) >> buf3))) op2'"
      if "buf1' x1a \<noteq> []"
        and "x1a \<notin> defaults"
        and "buf2 x1a = []"
        and "buf3 x1a = []"
      for x1a :: 'b
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BENQ x1a (BHD x1a buf1') buf2) buf2')
    (transp_op (case_sum buf1 (BTL x1a buf1')))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by (auto split: sum.splits)
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 (BTL x1a buf1')))
    (id_op (case_sum (BENQ x1a (BHD x1a buf1') buf3) buf3'))))\<close>
        using that by auto
      also have \<open>step (Out (Inl x1a) (BHD x1a buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 (BTL x1a buf1')))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1a) (BHD x1a buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> BTL x1a buf2) >> buf3))) op2'"
      if "x1a \<notin> defaults"
        and "buf2 x1a \<noteq> []"
        and "buf3 x1a = []"
      for x1a :: 'b
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BTL x1a buf2) buf2')
    (transp_op (case_sum buf1 buf1'))
    (id_op (case_sum (BENQ x1a (BHD x1a buf2) buf3) buf3'))))\<close>
        using that by auto
      also have \<open>step (Out (Inl x1a) (BHD x1a buf2)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL x1a buf2) buf2')
    (transp_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1a) (BHD x1a buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> BTL x1a buf3))) op2'"
      if "x1a \<notin> defaults"
        and "buf2 x1a = []"
        and "buf3 x1a \<noteq> []"
      for x1a :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. wstep (Out (Inl x1a) (BHD x1a buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> BTL x1a buf3))) op2'"
      if "x1a \<notin> defaults"
        and "buf2 x1a \<noteq> []"
        and "buf3 x1a \<noteq> []"
      for x1a :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. wstep (Out (Inr x2a) (BHD x2a buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (case_sum ((BTL x2a buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2'"
      if "buf1 x2a \<noteq> []"
        and "x2a \<notin> defaults"
        and "buf2' x2a = []"
        and "buf3' x2a = []"
      for x2a :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2a (BHD x2a buf1) buf2'))
    (transp_op (case_sum (BTL x2a buf1) buf1'))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by (force intro!: step_map_op[of Tau])
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum (BTL x2a buf1) buf1'))
    (id_op (case_sum buf3 (BENQ x2a (BHD x2a buf1) buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inr x2a) (BHD x2a buf1)) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum (BTL x2a buf1) buf1'))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2a) (BHD x2a buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> BTL x2a buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2'"
      if "x2a \<notin> defaults"
        and "buf2' x2a \<noteq> []"
        and "buf3' x2a = []"
      for x2a :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (transp_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2a buf2'))
    (transp_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 (BENQ x2a (BHD x2a buf2') buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inr x2a) (BHD x2a buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2a buf2'))
    (transp_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2a) (BHD x2a buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2') >> BTL x2a buf3') ((buf1' >> buf2) >> buf3))) op2'"
      if "x2a \<notin> defaults"
        and "buf2' x2a = []"
        and "buf3' x2a \<noteq> []"
      for x2a :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. wstep (Out (Inr x2a) (BHD x2a buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (transp_op (case_sum ((buf1 >> buf2') >> BTL x2a buf3') ((buf1' >> buf2) >> buf3))) op2'"
      if "x2a \<notin> defaults"
        and "buf2' x2a \<noteq> []"
        and "buf3' x2a \<noteq> []"
      for x2a :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_transp_op_cases split: sum.splits if_splits)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (BENQ pa xa (case_sum buf1 buf1'))) (id_op (case_sum buf3 buf3'))))"
      if "pa \<notin> defaults"
      for pa :: "'a + 'b"
        and xa :: 'c
      using that by (cases pa) (fastforce del: wbc_base intro!: wbc_base)+
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3)) (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum (BTL x1 buf3) buf3'))))"
      if "x1 \<notin> defaults"
        and "buf3 x1 \<noteq> []"
      for x1 :: 'b
      using that by (force del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3')) (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 (BTL x2 buf3')))))"
      if "x2 \<notin> defaults"
        and "buf3' x2 \<noteq> []"
      for x2 :: 'a
      using that by (force del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1') buf2) buf2') (transp_op (case_sum buf1 (BTL x1 buf1'))) (id_op (case_sum buf3 buf3'))))"
      if "x1 \<notin> defaults"
        and "buf1' x1 \<noteq> []"
      for x1 :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1) buf2')) (transp_op (case_sum (BTL x2 buf1) buf1')) (id_op (case_sum buf3 buf3'))))"
      if "x2 \<notin> defaults"
        and "buf1 x2 \<noteq> []"
      for x2 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))))"
      if "x1 \<notin> defaults"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'b
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = transp_op (case_sum ((buf1 >> buf2') >> buf3') ((buf1' >> buf2) >> buf3)) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2')) (transp_op (case_sum buf1 buf1')) (id_op (case_sum buf3 (BENQ x2 (BHD x2 buf2') buf3')))))"
      if "x2 \<notin> defaults"
        and "buf2' x2 \<noteq> []"
      for x2 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_transp_op_cases split: sum.splits)
  qed
qed

lemma transp_id_absorb_right:
  \<open>\<X> \<approx> \<X>\<turnstile>\<close>
  unfolding scomp_op_def
  using transp_id_absorb_right_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

lemma transp_id_absorb:
  \<open>\<X> \<approx> (\<stileturn>\<X>)\<turnstile>\<close>
  using transp_id_absorb_left transp_id_absorb_right wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

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
    (cimage (\<lambda>p. split_Read_aux p (\<lambda>x. BENQ (Inl p) x buf)) c\<UU>)
    (cimage (\<lambda>p. split_Read_aux p (\<lambda>x. BENQ (Inr p) x buf)) c\<UU>))
    (cimage (\<lambda>p. split_Write_aux (BTL p buf) p (BHD p buf))
      (cfilter (\<lambda>p. buf p \<noteq> []) c\<UU>))))\<close>

lemma split_op_code:
  \<open>split_op buf = Choice (cUn (cUn
    (cimage (\<lambda>p. Read p (\<lambda>x. split_op (BENQ (Inl p) x buf))) c\<UU>)
    (cimage (\<lambda>p. Read p (\<lambda>x. split_op (BENQ (Inr p) x buf))) c\<UU>))
    (cimage (\<lambda>p. Write (split_op (BTL p buf)) p (BHD p buf))
      (cfilter (\<lambda>p. buf p \<noteq> []) c\<UU>)))\<close>
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
  by force

lemma choices_split_op[simp]:
  \<open>choices (split_op buf) = cUn (cUn
    (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda>x. split_op (BENQ (Inl p) x buf))) c\<UU>)))
    (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda>x. split_op (BENQ (Inr p) x buf))) c\<UU>))))
    (cUnion (cimage choices (cimage (\<lambda>p. Write (split_op (BTL p buf)) p (BHD p buf))
      (cfilter (\<lambda>p. buf p \<noteq> []) c\<UU>))))\<close>
  apply (subst split_op_code)
  by simp

lemma split_op_reads:
  \<open>sub_op (Read p f) (split_op buf) n \<Longrightarrow> p \<in> UNIV - defaults\<close>
proof (induct p \<open>split_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) split_op_code, simp)
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) split_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) split_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) split_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) split_op_code, simp; force)
qed

lemma inputs_split_op[intro]:
  \<open>inputs (split_op buf) \<subseteq> UNIV - defaults\<close>
  by (intro subsetI, metis split_op_reads inputs_sub_op_Read)

lemma split_op_writes:
  \<open>sub_op (Write op p x) (split_op buf) n \<Longrightarrow> p \<in> UNIV - defaults\<close>
proof (induct p \<open>split_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) split_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) split_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) split_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) split_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) split_op_code, simp)
qed

lemma outputs_split_op[intro]:
  \<open>outputs (split_op buf) \<subseteq> UNIV - defaults\<close>
  by (intro subsetI, metis split_op_writes outputs_sub_op_Write)

lemma split_id_absorb_right_gen:
  \<open>split_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3'))
  \<approx> map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (split_op (case_sum buf1 buf1'))
      (id_op (case_sum buf3 buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (split_op (case_sum ((BENQ p x buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'b
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((BENQ p x buf1' >> buf2') >> buf3'))) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'b
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf1)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (split_op (case_sum ((BTL x1 buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2'"
      if "x1 \<notin> defaults"
        and "buf1 x1 \<noteq> []"
        and "buf3 x1 = []"
        and "buf2 x1 = []"
      for x1 :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2')
    (split_op (case_sum (BTL x1 buf1) buf1'))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum (BTL x1 buf1) buf1'))
    (id_op (case_sum (BENQ x1 (BHD x1 buf1) buf3) buf3'))))\<close>
        using that by auto
      also have \<open>step (Out (Inl x1) (BHD x1 buf1)) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum (BTL x1 buf1) buf1'))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf2)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (split_op (case_sum ((buf1 >> BTL x1 buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2'"
      if "x1 \<notin> defaults"
        and "buf3 x1 = []"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum(BTL x1 buf2) buf2')
    (split_op (case_sum buf1 buf1'))
    (id_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))))\<close>
        using that by auto
      also have \<open>step (Out (Inl x1) (BHD x1 buf2)) \<dots>
  (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) buf2')
    (split_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3)) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (split_op (case_sum ((buf1 >> buf2) >> BTL x1 buf3) ((buf1' >> buf2') >> buf3'))) op2'"
      if "x1 \<notin> defaults"
        and "buf3 x1 \<noteq> []"
      for x1 :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf1')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((BTL x2 buf1' >> buf2') >> buf3'))) op2'"
      if "x2 \<notin> defaults"
        and "buf1' x2 \<noteq> []"
        and "buf3' x2 = []"
        and "buf2' x2 = []"
      for x2 :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1') buf2'))
    (split_op (case_sum buf1 (BTL x2 buf1')))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 (BTL x2 buf1')))
    (id_op (case_sum buf3 (BENQ x2 (BHD x2 buf1') buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inr x2) (BHD x2 buf1')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 (BTL x2 buf1')))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf2')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> BTL x2 buf2') >> buf3'))) op2'"
      if "x2 \<notin> defaults"
        and "buf3' x2 = []"
        and "buf2' x2 \<noteq> []"
      for x2 :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (split_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2'))
    (split_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 (BENQ x2 (BHD x2 buf2') buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inr x2) (BHD x2 buf2')) \<dots>
  (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2'))
    (split_op (case_sum buf1 buf1'))
    (id_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      finally show ?thesis by blast
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3')) (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> BTL x2 buf3'))) op2'"
      if "x2 \<notin> defaults"
        and "buf3' x2 \<noteq> []"
      for x2 :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_split_op_cases split: sum.splits if_splits)
  qed
next
  case SIM2
  then show ?case
    apply - explore (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_split_op_cases split: sum.splits; hypsubst_thin?)
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum (BENQ pa xa buf1) buf1')) (id_op (case_sum buf3 buf3'))))"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'b
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp pa xa) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 (BENQ pa xa buf1'))) (id_op (case_sum buf3 buf3'))))"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'b
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3)) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum (BTL x1 buf3) buf3'))))"
      if "x1 \<notin> defaults"
        and "buf3 x1 \<noteq> []"
      for x1 :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3')) (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 (BTL x2 buf3')))))"
      if "x2 \<notin> defaults"
        and "buf3' x2 \<noteq> []"
      for x2 :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (split_op (case_sum (BTL x1 buf1) buf1')) (id_op (case_sum buf3 buf3'))))"
      if "x1 \<notin> defaults"
        and "buf1 x1 \<noteq> []"
      for x1 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1') buf2')) (split_op (case_sum buf1 (BTL x2 buf1'))) (id_op (case_sum buf3 buf3'))))"
      if "x2 \<notin> defaults"
        and "buf1' x2 \<noteq> []"
      for x2 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))))"
      if "x1 \<notin> defaults"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = split_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2')) (split_op (case_sum buf1 buf1')) (id_op (case_sum buf3 (BENQ x2 (BHD x2 buf2') buf3')))))"
      if "x2 \<notin> defaults"
        and "buf2' x2 \<noteq> []"
      for x2 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_split_op_cases split: sum.splits)
  qed
qed

lemma split_id_absorb_right:
  \<open>\<Lambda> \<approx> \<Lambda>\<turnstile>\<close>
  unfolding scomp_op_def
  using split_id_absorb_right_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

abbreviation \<open>\<Lambda>' \<equiv> \<stileturn>\<Lambda>\<close>

section \<open>merge_op - nondeterministic merge operator\<close>

datatype (discs_sels) ('m, 'd) merge_op_aux =
  merge_Read_aux \<open>'m + 'm\<close> \<open>'d \<Rightarrow> 'm + 'm \<Rightarrow> 'd buf\<close>
  | merge_Write_aux \<open>'m + 'm \<Rightarrow> 'd buf\<close> 'm 'd

abbreviation eval_merge_op_aux where
  \<open>eval_merge_op_aux c aux \<equiv> (case aux of
    merge_Read_aux p f \<Rightarrow> Read p (c \<circ> f)
  | merge_Write_aux buf p x \<Rightarrow> Write (c buf) p x)\<close>

corec merge_op :: \<open>('m :: {countable, defaults} + 'm \<Rightarrow> 'd buf) \<Rightarrow> ('m + 'm, 'm, 'd) op\<close> where
  \<open>merge_op buf = Choice (cimage (eval_merge_op_aux merge_op) (cUn (cUn (cUn
    (cimage (\<lambda>p. merge_Read_aux (Inl p) (\<lambda>x. BENQ (Inl p) x buf)) c\<UU>)
    (cimage (\<lambda>p. merge_Read_aux (Inr p) (\<lambda>x. BENQ (Inr p) x buf)) c\<UU>))
    (cimage (\<lambda>p. merge_Write_aux (BTL (Inl p) buf) p (BHD (Inl p) buf))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> []) c\<UU>)))
    (cimage (\<lambda>p. merge_Write_aux (BTL (Inr p) buf) p (BHD (Inr p) buf))
      (cfilter (\<lambda>p. buf (Inr p) \<noteq> []) c\<UU>))))\<close>

lemma merge_op_code:
  \<open>merge_op buf = Choice (cUn (cUn (cUn
    (cimage (\<lambda>p. Read (Inl p) (\<lambda>x. merge_op (BENQ (Inl p) x buf))) c\<UU>)
    (cimage (\<lambda>p. Read (Inr p) (\<lambda>x. merge_op (BENQ (Inr p) x buf))) c\<UU>))
    (cimage (\<lambda>p. Write (merge_op (BTL (Inl p) buf)) p (BHD (Inl p) buf))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> []) c\<UU>)))
    (cimage (\<lambda>p. Write (merge_op (BTL (Inr p) buf)) p (BHD (Inr p) buf))
      (cfilter (\<lambda>p. buf (Inr p) \<noteq> []) c\<UU>)))\<close>
  apply (subst merge_op.code)
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
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)+
     apply force
    apply auto
    done
  done

abbreviation merge_empty_op (\<open>\<V>\<close>) where \<open>\<V> \<equiv> merge_op (\<lambda>_. [])\<close>

lemma step_merge_op_Inp_L:
  assumes \<open>step io (merge_op buf) op\<close>
    and \<open>io = Inp (Inl p) x\<close>
  obtains \<open>op = merge_op (BENQ (Inl p) x buf)\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) merge_op_code)
  by force

lemma step_merge_op_Inp_R:
  assumes \<open>step io (merge_op buf) op\<close>
    and \<open>io = Inp (Inr p) x\<close>
  obtains \<open>op = merge_op (BENQ (Inr p) x buf)\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) merge_op_code)
  by force

lemma step_merge_op_Out:
  assumes \<open>step io (merge_op buf) op\<close>
    and \<open>io = Out p x\<close>
  obtains \<open>op = merge_op (BTL (Inl p) buf)\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>BHD (Inl p) buf = x\<close> \<open>p \<notin> defaults\<close>
  |       \<open>op = merge_op (BTL (Inr p) buf)\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>BHD (Inr p) buf = x\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) merge_op_code)
  by auto

lemma no_step_merge_op_Tau:
  assumes \<open>step io (merge_op buf) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) merge_op_code)
  by auto

lemma step_merge_op_elim:
  assumes \<open>step io (merge_op buf) op\<close>
  obtains p x where \<open>io = Inp (Inl p) x\<close> \<open>op = merge_op (BENQ (Inl p) x buf)\<close> \<open>p \<notin> defaults\<close>
  |       p x where \<open>io = Inp (Inr p) x\<close> \<open>op = merge_op (BENQ (Inr p) x buf)\<close> \<open>p \<notin> defaults\<close>
  |       p x where \<open>io = Out p x\<close> \<open>op = merge_op (BTL (Inl p) buf)\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>BHD (Inl p) buf = x\<close> \<open>p \<notin> defaults\<close>
  |       p x where \<open>io = Out p x\<close> \<open>op = merge_op (BTL (Inr p) buf)\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>BHD (Inr p) buf = x\<close> \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) merge_op_code)
  by fastforce

lemma step_merge_op_Read_L[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BENQ (Inl p) x buf \<Longrightarrow> step (Inp (Inl p) x) (merge_op buf) (merge_op buf')\<close>
  apply (subst merge_op_code)
  by fastforce

lemma step_merge_op_Read_R[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BENQ (Inr p) x buf \<Longrightarrow> step (Inp (Inr p) x) (merge_op buf) (merge_op buf')\<close>
  apply (subst merge_op_code)
  by fastforce

lemma step_merge_op_Write_L[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BTL (Inl p) buf \<Longrightarrow> buf (Inl p) \<noteq> [] \<Longrightarrow> BHD (Inl p) buf = x \<Longrightarrow>
  step (Out p x) (merge_op buf) (merge_op buf')\<close>
  apply (subst merge_op_code)
  by fastforce

lemma step_merge_op_Write_R[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BTL (Inr p) buf \<Longrightarrow> buf (Inr p) \<noteq> [] \<Longrightarrow> BHD (Inr p) buf = x \<Longrightarrow>
  step (Out p x) (merge_op buf) (merge_op buf')\<close>
  apply (subst merge_op_code)
  by fastforce

lemma choices_merge_op[simp]:
  \<open>choices (merge_op buf) = cUn (cUn (cUn
    (cUnion (cimage choices (cimage (\<lambda>p. Read (Inl p) (\<lambda>x. merge_op (BENQ (Inl p) x buf))) c\<UU>)))
    (cUnion (cimage choices (cimage (\<lambda>p. Read (Inr p) (\<lambda>x. merge_op (BENQ (Inr p) x buf))) c\<UU>))))
    (cUnion (cimage choices (cimage (\<lambda>p. Write (merge_op (BTL (Inl p) buf)) p (BHD (Inl p) buf))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> []) c\<UU>)))))
    (cUnion (cimage choices (cimage (\<lambda>p. Write (merge_op (BTL (Inr p) buf)) p (BHD (Inr p) buf))
      (cfilter (\<lambda>p. buf (Inr p) \<noteq> []) c\<UU>))))\<close>
  apply (subst merge_op_code)
  by simp

lemma merge_op_reads:
  \<open>sub_op (Read p f) (merge_op buf) n \<Longrightarrow> p \<in> UNIV - defaults\<close>
proof (induct p \<open>merge_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) merge_op_code, simp)
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) merge_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) merge_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) merge_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) merge_op_code, simp; force)
qed

lemma inputs_merge_op[intro]:
  \<open>inputs (merge_op buf) \<subseteq> UNIV - defaults\<close>
  by (intro subsetI, metis merge_op_reads inputs_sub_op_Read)

lemma merge_op_writes:
  \<open>sub_op (Write op p x) (merge_op buf) n \<Longrightarrow> p \<in> UNIV - defaults\<close>
proof (induct p \<open>merge_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) merge_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) merge_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) merge_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) merge_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) merge_op_code, simp)
qed

lemma outputs_merge_op[intro]:
  \<open>outputs (merge_op buf) \<subseteq> UNIV - defaults\<close>
  by (intro subsetI, metis merge_op_writes outputs_sub_op_Write)

lemma merge_id_absorb_left_gen:
  \<open>merge_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3'))
  \<approx> map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (id_op (case_sum buf1 buf1'))
      (merge_op (case_sum buf3 buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
     by (auto elim !: step_merge_op_elim split: if_splits) (fastforce del: wbc_base intro!: wbc_base)+
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (BENQ pa xa (case_sum buf1 buf1'))) (merge_op (case_sum buf3 buf3'))))"
      if "pa \<notin> defaults"
      for pa :: "'a + 'a"
        and xa :: 'b
      using that by (cases pa) (fastforce del: wbc_base intro!: wbc_base)+
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3)) (merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum (BTL pa buf3) buf3'))))"
      if "buf3 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3')) (merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 (BTL pa buf3')))))"
      if "buf3' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1) buf2) buf2') (id_op (case_sum (BTL x1 buf1) buf1')) (merge_op (case_sum buf3 buf3'))))"
      if "x1 \<notin> defaults"
        and "buf1 x1 \<noteq> []"
      for x1 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BENQ x2 (BHD x2 buf1') buf2')) (id_op (case_sum buf1 (BTL x2 buf1'))) (merge_op (case_sum buf3 buf3'))))"
      if "x2 \<notin> defaults"
        and "buf1' x2 \<noteq> []"
      for x2 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum (BENQ pa (BHD pa buf2) buf3) buf3'))))"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = merge_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa buf2')) (id_op (case_sum buf1 buf1')) (merge_op (case_sum buf3 (BENQ pa (BHD pa buf2') buf3')))))"
      if "buf2' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim split: sum.splits)
  qed
qed

lemma merge_id_absorb_left:
  \<open>\<V> \<approx> \<stileturn>\<V>\<close>
  unfolding scomp_op_def
  using merge_id_absorb_left_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

abbreviation \<open>\<V>' \<equiv> \<V>\<turnstile>\<close>

section \<open>acopy_op - async copy operator\<close>
datatype (discs_sels) ('m, 'd) acopy_op_aux =
  acopy_Read_aux \<open>'m\<close> \<open>'d \<Rightarrow> 'm + 'm \<Rightarrow> 'd buf\<close>
  | acopy_Write_aux \<open>'m + 'm \<Rightarrow> 'd buf\<close>  \<open>'m + 'm\<close> 'd

abbreviation eval_acopy_op_aux where
  "eval_acopy_op_aux c aux \<equiv> (case aux of
    acopy_Read_aux p f \<Rightarrow> Read p (c \<circ> f)
  | acopy_Write_aux buf p x \<Rightarrow> Write (c buf) p x)"


corec acopy_op :: "('m + 'm \<Rightarrow> 'a buf) \<Rightarrow> ('m :: {countable, defaults}, 'm + 'm, 'a) op" where
  "acopy_op buf = Choice (cimage (eval_acopy_op_aux acopy_op) (cUn 
    (cimage (\<lambda> p. acopy_Read_aux p (\<lambda> x. BENQ (Inr p) x (BENQ (Inl p) x buf))) (c\<UU> :: 'm cset)) (cUn
    (cimage (\<lambda> p. acopy_Write_aux (BTL (Inl p) buf) (Inl p) (BHD (Inl p) buf)) (cfilter (\<lambda>p. buf (Inl p) \<noteq> [])(c\<UU> :: 'm cset)))
    (cimage (\<lambda> p. acopy_Write_aux (BTL (Inr p) buf) (Inr p) (BHD (Inr p) buf)) (cfilter (\<lambda>p. buf (Inr p) \<noteq> [])(c\<UU> :: 'm cset))))))"

lemma acopy_op_code:
  "acopy_op buf = Choice (cUn 
    (cimage (\<lambda> p. Read p (\<lambda> x. acopy_op (BENQ (Inr p) x (BENQ (Inl p) x buf)))) (c\<UU> :: 'm :: {countable, defaults} cset)) (cUn
    (cimage (\<lambda> p.  Write (acopy_op (BTL (Inl p) buf)) (Inl p) (BHD (Inl p) buf)) (cfilter (\<lambda>p. buf (Inl p) \<noteq> [])(c\<UU> :: 'm cset)))
    (cimage (\<lambda> p.  Write (acopy_op (BTL (Inr p) buf)) (Inr p) (BHD (Inr p) buf)) (cfilter (\<lambda>p. buf (Inr p) \<noteq> [])(c\<UU> :: 'm cset)))))"
  apply (subst acopy_op.code)
  apply (auto simp add: comp_def cset.map_comp o_def split: if_splits op.splits)
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    unfolding Set.filter_def
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply (rule disjI1)
     apply (rule image_eqI)
      apply blast
     apply simp_all
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply force
    apply auto
    done
  done

abbreviation acopy_empty_op  ("\<C>") where \<open>\<C> \<equiv> acopy_op (\<lambda>_. [])\<close>


lemma step_acopy_op_Inp:
  assumes \<open>step io (acopy_op buf) op\<close>
    and \<open>io = Inp p x\<close>
  obtains \<open>op = acopy_op (BENQ (Inr p) x (BENQ (Inl p) x buf))\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) acopy_op_code)
  apply auto
  done


lemma no_step_acopy_op_Out:
  assumes \<open>step io (acopy_op buf) op\<close>
    and \<open>io = Out p x\<close>
  obtains \<open>op = acopy_op (BTL p buf)\<close> \<open>buf p \<noteq> []\<close> \<open>BHD p buf = x\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) acopy_op_code)
  apply auto
  done

lemma no_step_acopy_op_Tau:
  assumes \<open>step io (acopy_op buf) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) acopy_op_code)
  apply auto
  done

lemma step_acopy_op_elim:
  assumes \<open>step io (acopy_op buf) op\<close>
  obtains p x where \<open>io = Inp p x\<close> \<open>op = acopy_op (BENQ (Inr p) x (BENQ (Inl p) x buf))\<close> \<open>p \<notin> defaults\<close> |
    p x where \<open>io = Out (Inl p) x\<close> \<open>op = acopy_op (BTL (Inl p) buf)\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>BHD (Inl p) buf = x\<close> \<open>p \<notin> defaults\<close> |
    p x where \<open>io = Out (Inr p) x\<close> \<open>op = acopy_op (BTL (Inr p) buf)\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>BHD (Inr p) buf = x\<close> \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) acopy_op_code)
  apply auto
  done


lemma step_acopy_op_Read[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BENQ (Inr p) x (BENQ (Inl p) x buf) \<Longrightarrow> step (Inp p x) (acopy_op buf) (acopy_op buf')\<close>
  apply (subst acopy_op_code)
  apply force
  done

lemma step_acopy_op_WriteL[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BTL (Inl p) buf \<Longrightarrow> buf (Inl p) \<noteq> [] \<Longrightarrow> BHD (Inl p) buf = x \<Longrightarrow> step (Out (Inl p) x) (acopy_op buf) (acopy_op buf')\<close>
  apply (subst acopy_op_code)
  apply force
  done

lemma step_acopy_op_WriteR[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BTL (Inr p) buf \<Longrightarrow> buf (Inr p) \<noteq> [] \<Longrightarrow> BHD (Inr p) buf = x \<Longrightarrow> step (Out (Inr p) x) (acopy_op buf) (acopy_op buf')\<close>
  apply (subst acopy_op_code)
  apply force
  done

lemma step_acopy_op_Write[intro]:
  \<open>p \<notin> defaults \<Longrightarrow> buf' = BTL p buf \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> BHD p buf = x \<Longrightarrow> step (Out p x) (acopy_op buf) (acopy_op buf')\<close>
  by (metis Inl_in_defaults Inr_in_defaults obj_sumE step_acopy_op_WriteL step_acopy_op_WriteR)

lemma choices_acopy_op[simp]:
  \<open>choices (acopy_op buf) = cUn (cUn
    (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda> x. acopy_op (BENQ (Inr p) x (BENQ (Inl p) x buf)))) c\<UU>)))
    (cUnion (cimage choices (cimage (\<lambda>p. Write (acopy_op (BTL (Inl p) buf)) (Inl p) (BHD (Inl p) buf))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> []) c\<UU>)))))
    (cUnion (cimage choices (cimage (\<lambda>p. Write (acopy_op (BTL (Inr p) buf)) (Inr p) (BHD (Inr p) buf))
      (cfilter (\<lambda>p. buf (Inr p) \<noteq> []) c\<UU>))))\<close>
  apply (subst acopy_op_code)
  by auto


lemma acopy_op_reads:
  "sub_op (Read p f) (acopy_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>acopy_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) acopy_op_code, simp) 
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) acopy_op_code, simp; force) 
qed

lemma inputs_acopy_op[intro]:
  "inputs (acopy_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using acopy_op_reads by (metis inputs_sub_op_Read)

lemma acopy_op_writes:
  "sub_op (Write op p x) (acopy_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>acopy_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) acopy_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) acopy_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) acopy_op_code, simp)
qed

lemma outputs_acopy_op[intro]:
  "outputs (acopy_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using acopy_op_writes by (metis outputs_sub_op_Write)

lemma acopy_id_absorb_left_gen:
  \<open>acopy_op (case_sum (buf1 >> buf2 >> buf3) (buf1 >> buf2 >> buf3'))
  \<approx> map_op projl projr (comp_op Some buf2
      (id_op buf1)
      (acopy_op (case_sum buf3 buf3')))\<close>
proof (coinduction arbitrary: buf1 buf2 buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) (acopy_op (case_sum ((BENQ p x buf1 >> buf2) >> buf3) ((BENQ p x buf1 >> buf2) >> buf3'))) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'b
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl p) (BHD p buf1)) (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) (acopy_op (case_sum ((BTL p buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3'))) op2'"
      if "buf1 p \<noteq> []"
        and "p \<notin> defaults"
        and "buf3 p = []"
        and "buf2 p = []"
      for p :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some buf2
    (id_op buf1)
    (acopy_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (BENQ p (BHD p buf1) buf2)
    (id_op (BTL p buf1))
    (acopy_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some buf2
    (id_op (BTL p buf1))
    (acopy_op (case_sum (BENQ p (BHD p buf1) buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inl p) (BHD p buf1)) \<dots>
  (map_op projl projr (comp_op Some buf2
    (id_op (BTL p buf1))
    (acopy_op (case_sum buf3 (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto
      finally show ?thesis
        by (smt (verit, del_insts) BAPPEND_BENQ_BHD BAPPEND_BTL BHD_BULK_BENQ_cases BULK_BENQ_right_empty that(1) that(4) wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl p) (BHD p buf2)) (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) (acopy_op (case_sum ((buf1 >> BTL p buf2) >> buf3) ((buf1 >> buf2) >> buf3'))) op2'"
      if "p \<notin> defaults"
        and "buf3 p = []"
        and "buf2 p \<noteq> []"
      for p :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some buf2
    (id_op buf1)
    (acopy_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (BTL p buf2)
    (id_op buf1)
    (acopy_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf2) buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inl p) (BHD p buf2)) \<dots>
  (map_op projl projr (comp_op Some (BTL p buf2)
    (id_op buf1)
    (acopy_op (case_sum buf3 (BENQ p (BHD p buf2) buf3')))))\<close>
        using that by auto
      finally show ?thesis
        by (smt (verit, del_insts) BAPPEND_BENQ_BHD BULK_BENQ_assoc that(3) wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inl p) (BHD p buf3)) (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) (acopy_op (case_sum ((buf1 >> buf2) >> BTL p buf3) ((buf1 >> buf2) >> buf3'))) op2'"
      if "p \<notin> defaults"
        and "buf3 p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr p) (BHD p buf1)) (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((BTL p buf1 >> buf2) >> buf3'))) op2'"
      if "buf1 p \<noteq> []"
        and "p \<notin> defaults"
        and "buf3' p = []"
        and "buf2 p = []"
      for p :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some buf2
    (id_op buf1)
    (acopy_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (BENQ p (BHD p buf1) buf2)
    (id_op (BTL p buf1))
    (acopy_op (case_sum buf3 buf3'))))\<close>
        using that by auto
      also have \<open>step Tau \<dots>
  (map_op projl projr (comp_op Some buf2
    (id_op (BTL p buf1))
    (acopy_op (case_sum (BENQ p (BHD p buf1) buf3) (BENQ p (BHD p buf1) buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inr p) (BHD p buf1)) \<dots>
  (map_op projl projr (comp_op Some buf2
    (id_op (BTL p buf1))
    (acopy_op (case_sum (BENQ p (BHD p buf1) buf3) buf3'))))\<close>
        using that by auto
      finally show ?thesis
        by (smt (verit, del_insts) BAPPEND_BENQ_BHD BAPPEND_BTL BHD_BULK_BENQ_cases BULK_BENQ_right_empty that(1) that(4) wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr p) (BHD p buf2)) (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> BTL p buf2) >> buf3'))) op2'"
      if "p \<notin> defaults"
        and "buf3' p = []"
        and "buf2 p \<noteq> []"
      for p :: 'a
    proof -
      have \<open>step Tau
  (map_op projl projr (comp_op Some buf2
    (id_op buf1)
    (acopy_op (case_sum buf3 buf3'))))
  (map_op projl projr (comp_op Some (BTL p buf2)
    (id_op buf1)
    (acopy_op (case_sum (BENQ p (BHD p buf2) buf3) (BENQ p (BHD p buf2) buf3')))))\<close>
        using that by auto
      also have \<open>step (Out (Inr p) (BHD p buf2)) \<dots>
  (map_op projl projr (comp_op Some (BTL p buf2)
    (id_op buf1)
    (acopy_op (case_sum (BENQ p (BHD p buf2) buf3) buf3'))))\<close>
        using that by auto
      finally show ?thesis
        by (smt (verit, del_insts) BAPPEND_BENQ_BHD BULK_BENQ_assoc that(3) wbc_base)
    qed
    moreover have "\<exists>op2'. wstep (Out (Inr p) (BHD p buf3')) (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> BTL p buf3'))) op2'"
      if "p \<notin> defaults"
        and "buf3' p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_acopy_op_elim split: if_splits)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some buf2 (id_op (BENQ pa xa buf1)) (acopy_op (case_sum buf3 buf3'))))"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'b
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl pa) (BHD pa buf3)) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum (BTL pa buf3) buf3'))))"
      if "buf3 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr pa) (BHD pa buf3')) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 (BTL pa buf3')))))"
      if "buf3' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (BENQ pa (BHD pa buf1) buf2) (id_op (BTL pa buf1)) (acopy_op (case_sum buf3 buf3'))))"
      if "pa \<notin> defaults"
        and "buf1 pa \<noteq> []"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf2 buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1 >> buf2) >> buf3')) \<and> op2 = map_op projl projr (comp_op Some buf2 (id_op buf1) (acopy_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (BTL pa buf2) (id_op buf1) (acopy_op (case_sum (BENQ pa (BHD pa buf2) buf3) (BENQ pa (BHD pa buf2) buf3')))))"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_acopy_op_elim)
  qed
qed

lemma acopy_id_absorb_left:
  \<open>\<C> \<approx> \<stileturn>\<C>\<close>
  unfolding scomp_op_def
  using acopy_id_absorb_left_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

lemma acopy_id_absorb_right_gen:
  \<open>acopy_op (case_sum (buf1 >> buf2 >> buf3) (buf1' >> buf2' >> buf3'))
  \<approx> map_op projl projr (comp_op Some (case_sum buf2 buf2')
      (acopy_op (case_sum buf1 buf1'))
      (id_op (case_sum buf3 buf3')))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    by (auto elim !: step_acopy_op_elim split: if_splits) (fastforce del: wbc_base intro!: wbc_base)+
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum (BENQ pa xa buf1) (BENQ pa xa buf1'))) (id_op (case_sum buf3 buf3'))))"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'b
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inl x1) (BHD x1 buf3)) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum (BTL x1 buf3) buf3'))))"
      if "x1 \<notin> defaults"
        and "buf3 x1 \<noteq> []"
      for x1 :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. wstep (Out (Inr x2) (BHD x2 buf3')) (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 (BTL x2 buf3')))))"
      if "x2 \<notin> defaults"
        and "buf3' x2 \<noteq> []"
      for x2 :: 'a
      using that by (fastforce del: wbc_base intro!: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf1) buf2) buf2') (acopy_op (case_sum (BTL pa buf1) buf1')) (id_op (case_sum buf3 buf3'))))"
      if "buf1 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa buf1') buf2')) (acopy_op (case_sum buf1 (BTL pa buf1'))) (id_op (case_sum buf3 buf3'))))"
      if "buf1' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) fastforce+
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) buf3'))))"
      if "x1 \<notin> defaults"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3'))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf2' buf3 buf3'. op1 = acopy_op (case_sum ((buf1 >> buf2) >> buf3) ((buf1' >> buf2') >> buf3')) \<and> op2 = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 buf3')))) op2' (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 buf2')) (acopy_op (case_sum buf1 buf1')) (id_op (case_sum buf3 (BENQ x2 (BHD x2 buf2') buf3')))))"
      if "x2 \<notin> defaults"
        and "buf2' x2 \<noteq> []"
      for x2 :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base], fastforce, metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
    ultimately show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_id_op_cases split: sum.splits)
  qed
qed

lemma acopy_id_absorb_right:
  \<open>\<C> \<approx> \<C>\<turnstile>\<close>
  unfolding scomp_op_def
  using acopy_id_absorb_right_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

lemma acopy_id_absorb:
  \<open>\<C> \<approx> (\<stileturn>\<C>)\<turnstile>\<close>
  using acopy_id_absorb_left acopy_id_absorb_right wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

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
    (cimage (\<lambda>p. aeq_Read_aux (Inl p) (\<lambda>x. BENQ (Inl p) x buf)) c\<UU>)
    (cimage (\<lambda>p. aeq_Read_aux (Inr p) (\<lambda>x. BENQ (Inr p) x buf)) c\<UU>))
    (cimage (\<lambda>p. (if BHD (Inl p) buf = BHD (Inr p) buf then aeq_Write_aux (BTL (Inr p) (BTL (Inl p) buf)) p (BHD (Inl p) buf) else aeq_Silent_aux (BTL (Inr p) (BTL (Inl p) buf))))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> [] \<and> buf (Inr p) \<noteq> []) c\<UU>))))\<close> 

lemma aeq_op_code:
  "aeq_op buf = Choice (cUn (cUn
    (cimage (\<lambda> p. Read (Inl p) (\<lambda> x. aeq_op (BENQ (Inl p) x buf))) (c\<UU> :: 'm :: {countable, defaults} cset))
    (cimage (\<lambda> p. Read (Inr p) (\<lambda> x. aeq_op (BENQ (Inr p) x buf))) (c\<UU> :: 'm cset)))
    (cimage (\<lambda>p. (if BHD (Inl p) buf = BHD (Inr p) buf 
      then Write (aeq_op (BTL (Inr p) (BTL (Inl p) buf))) p (BHD (Inl p) buf) 
      else Silent (aeq_op (BTL (Inr p) (BTL (Inl p) buf))))) (cfilter (\<lambda>p. buf (Inl p) \<noteq> [] \<and> buf (Inr p) \<noteq> []) c\<UU>)))"
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
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)+
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

lemma step_aeq_op_Out:
  assumes \<open>step io (aeq_op buf) op\<close>
    and \<open>io = Out p x\<close>
  obtains \<open>op = aeq_op (BTL (Inr p) (BTL (Inl p) buf))\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>x = BHD (Inl p) buf\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>BHD (Inl p) buf = BHD (Inr p) buf\<close> \<open>p \<notin> defaults\<close>
  using assms apply atomize
  apply (subst (asm) (2) aeq_op_code)
  apply auto
  done

lemma step_aeq_op_Tau:
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

lemma choices_aeq_op[simp]:
  \<open>choices (aeq_op buf) = cUn (cUn
    (cUnion (cimage choices (cimage (\<lambda>p. Read (Inl p) (\<lambda>x. aeq_op (BENQ (Inl p) x buf))) c\<UU>)))
    (cUnion (cimage choices (cimage (\<lambda>p. Read (Inr p) (\<lambda>x. aeq_op (BENQ (Inr p) x buf))) c\<UU>))))
    (cUnion (cimage choices (cimage (\<lambda>p. (if BHD (Inl p) buf = BHD (Inr p) buf
        then Write (aeq_op (BTL (Inr p) (BTL (Inl p) buf))) p (BHD (Inl p) buf)
        else Silent (aeq_op (BTL (Inr p) (BTL (Inl p) buf)))))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> [] \<and> buf (Inr p) \<noteq> []) c\<UU>))))\<close>
  apply (subst aeq_op_code)
  by simp


lemma aeq_op_reads:
  "sub_op (Read p f) (aeq_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>aeq_op buf\<close> arbitrary: buf rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) aeq_op_code, simp) 
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) aeq_op_code, simp; force) 
qed

lemma inputs_aeq_op[intro]:
  "inputs (aeq_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using aeq_op_reads by (metis inputs_sub_op_Read)

lemma aeq_op_writes:
  "sub_op (Write op p x) (aeq_op buf) n \<Longrightarrow> p \<in> UNIV - defaults"
proof (induct p \<open>aeq_op buf\<close> arbitrary: buf rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) aeq_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) aeq_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) aeq_op_code, simp)
qed

lemma outputs_aeq_op[intro]:
  "outputs (aeq_op buf) \<subseteq> UNIV - defaults"
  apply (intro subsetI)
  using aeq_op_writes by (metis outputs_sub_op_Write)

subsection \<open>Some properties with vdash\<close>

lemma aeq_id_absorb_gen:
  "aeq_op (case_sum (buf1L >> buf2L >> buf3L) (buf1R >> buf2R >> buf3R)) \<approx> map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R) ) (aeq_op (case_sum buf3L buf3R) ))"
proof (coinduction arbitrary: buf1L buf2L buf3L buf1R buf2R buf3R  rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
    explore (elim exE conjE disjE step_id_op_cases step_comp_op_elim step_map_op_elim step_aeq_op_elim; simp split: if_splits sum.splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp (Inl p) y) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BENQ p y buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and y :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Inp (Inr p) y) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((BENQ p y buf1R >> buf2R) >> buf3R))) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and y :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "buf1R p \<noteq> []"
        and "BHD p buf1L = BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p = []"
        and "buf2L p = []"
      for p :: 'a
        and x :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1R p \<noteq> []"
        and "BHD p buf2L = BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p = []"
        and "buf2L p \<noteq> []"
      for p :: 'a
        and x :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "BHD p buf1L = BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p \<noteq> []"
        and "buf2L p = []"
      for p :: 'a
        and x :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "BHD p buf2L = BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p \<noteq> []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf1R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1R p \<noteq> []"
        and "BHD p buf3L = BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p \<noteq> []"
        and "buf2R p = []"
      for p :: 'a
        and x :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "BHD p buf3L = BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p \<noteq> []"
        and "buf2R p \<noteq> []"
      for p :: 'a
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "BHD p buf1L = BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p = []"
        and "buf2L p = []"
      for p :: 'a
        and x :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "BHD p buf2L = BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p = []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3R)) (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "BHD p buf3L = BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p \<noteq> []"
      for p :: 'a
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "buf1R p \<noteq> []"
        and "BHD p buf1L \<noteq> BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p = []"
        and "buf2L p = []"
      for p :: 'a
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))
     (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1L) buf2L) buf2R) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum buf3L buf3R))))"
        using that by auto
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum (BENQ p (BHD p buf1L) buf3L) buf3R))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L (BENQ p (BHD p buf1R) buf2R)) (id_op (case_sum (BTL p buf1L) (BTL p buf1R))) (aeq_op (case_sum (BENQ p (BHD p buf1L) buf3L) buf3R))))"
        using that by auto
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum (BTL p buf1L) (BTL p buf1R))) (aeq_op (case_sum (BENQ p (BHD p buf1L) buf3L) (BENQ p (BHD p buf1R) buf3R)))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum (BTL p buf1L) (BTL p buf1R))) (aeq_op (case_sum buf3L buf3R))))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply (rule refl)+
        apply simp
        done
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1R p \<noteq> []"
        and "BHD p buf2L \<noteq> BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p = []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BENQ p (BHD p buf2L) buf3L) buf3R))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) (BENQ p (BHD p buf1R) buf2R)) (id_op (case_sum buf1L (BTL p buf1R))) (aeq_op (case_sum (BENQ p (BHD p buf2L) buf3L) buf3R))))"
        using that by auto
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) buf2R) (id_op (case_sum buf1L (BTL p buf1R))) (aeq_op (case_sum (BENQ p (BHD p buf2L) buf3L) (BENQ p (BHD p buf1R) buf3R)))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) buf2R) (id_op (case_sum buf1L (BTL p buf1R))) (aeq_op (case_sum buf3L buf3R))))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply (rule refl)+
        apply simp
        done
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "BHD p buf1L \<noteq> BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p \<noteq> []"
        and "buf2L p = []"
      for p :: 'a
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))
     (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1L) buf2L) buf2R) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum buf3L buf3R))))"
        using that by auto
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum (BENQ p (BHD p buf1L) buf3L) buf3R))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L (BTL p buf2R)) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum (BENQ p (BHD p buf1L) buf3L) (BENQ p (BHD p buf2R) buf3R)))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L (BTL p buf2R)) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum buf3L buf3R))))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply (rule refl)+
        apply simp
        done
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "BHD p buf2L \<noteq> BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p = []"
        and "buf2R p \<noteq> []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that 
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BENQ p (BHD p buf2L) buf3L) buf3R))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also  have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) (BTL p buf2R)) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BENQ p (BHD p buf2L) buf3L) (BENQ p (BHD p buf2R) buf3R)))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) (BTL p buf2R)) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply (rule refl)+
        apply simp
        done
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((BTL p buf1R >> buf2R) >> buf3R))) op2'"
      if "buf1R p \<noteq> []"
        and "BHD p buf3L \<noteq> BHD p buf1R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p \<noteq> []"
        and "buf2R p = []"
      for p :: 'a
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))
     (map_op projl projr (comp_op Some (case_sum buf2L (BENQ p (BHD p buf1R) buf2R)) (id_op (case_sum buf1L (BTL p buf1R))) (aeq_op (case_sum buf3L buf3R))))"
        using that by auto
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L (BTL p buf1R))) (aeq_op (case_sum buf3L (BENQ p (BHD p buf1R) buf3R)))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L (BTL p buf1R))) (aeq_op (case_sum (BTL p buf3L) buf3R))))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply (rule refl)+
        apply simp
        done
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((buf1R >> BTL p buf2R) >> buf3R))) op2'"
      if "BHD p buf3L \<noteq> BHD p buf2R"
        and "p \<notin> defaults"
        and "buf3R p = []"
        and "buf3L p \<noteq> []"
        and "buf2R p \<noteq> []"
      for p :: 'a
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))
     (map_op projl projr (comp_op Some (case_sum buf2L (BTL p buf2R)) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L (BENQ p (BHD p buf2R) buf3R)))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L (BTL p buf2R)) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BTL p buf3L) buf3R))))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply (rule refl)+
        apply simp
        done
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((BTL p buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "buf1L p \<noteq> []"
        and "BHD p buf1L \<noteq> BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p = []"
        and "buf2L p = []"
      for p :: 'a
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))
     (map_op projl projr (comp_op Some (case_sum (BENQ p (BHD p buf1L) buf2L) buf2R) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum buf3L buf3R))))"
        using that by auto
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum (BENQ p (BHD p buf1L) buf3L) buf3R))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum (BTL p buf1L) buf1R)) (aeq_op (case_sum buf3L (BTL p buf3R)))))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply (rule refl)+
        apply simp
        done
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> BTL p buf2L) >> buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "BHD p buf2L \<noteq> BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p = []"
        and "buf2L p \<noteq> []"
      for p :: 'a
      using that 
    proof -
      have "step Tau (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R))))
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BENQ p (BHD p buf2L) buf3L) buf3R))))"
        using that apply -
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply force
             apply simp_all
        done
      also have "step Tau \<dots>
     (map_op projl projr (comp_op Some (case_sum (BTL p buf2L) buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L (BTL p buf3R)))))"
        using that by auto
      finally show ?thesis
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply (rule refl)+
        apply blast
        done
    qed
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) (aeq_op (case_sum ((buf1L >> buf2L) >> BTL p buf3L) ((buf1R >> buf2R) >> BTL p buf3R))) op2'"
      if "BHD p buf3L \<noteq> BHD p buf3R"
        and "p \<notin> defaults"
        and "buf3R p \<noteq> []"
        and "buf3L p \<noteq> []"
      for p :: 'a
      using that apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply (rule refl)+
      apply force
      done
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM1 apply (elim exE conjE disjE step_id_op_cases step_comp_op_elim step_map_op_elim step_aeq_op_elim; simp split: if_splits sum.splits ; hypsubst_thin)
                           apply (rule prems; assumption)+
        done
      done
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (elim exE conjE disjE step_id_op_cases step_comp_op_elim step_map_op_elim step_aeq_op_elim; simp split: if_splits sum.splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp pa x) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (BENQ pa x (case_sum buf1L buf1R))) (aeq_op (case_sum buf3L buf3R))))"
      if "(pa::'a + 'a) \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, 'a + 'a, 'b) op"
        and pa :: "'a + 'a"
    proof (cases pa)
      case (Inl a)
      from this that show ?thesis 
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply simp_all
        apply force
        done
    next
      case (Inr b)
      from this that show ?thesis 
        using that apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply simp_all
        apply force
        done
    qed
    moreover have "\<exists>op2'. wstep (Inp (Inl pa) y) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BENQ pa y buf3L) buf3R))))"
      if "Out p x = Inp (Inl pa::'a + 'a) y"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: 'a
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
        and y :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Inp (Inr pa) y) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L (BENQ pa y buf3R)))))"
      if "Out p x = Inp (Inr pa::'a + 'a) y"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: 'a
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
        and y :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3R)) (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BTL pa buf3L) (BTL pa buf3R)))))"
      if "(Out p x::('a + 'a, 'a, 'b) IO) = Out pa (BHD pa buf3R)"
        and "buf3L pa \<noteq> []"
        and "buf3R pa \<noteq> []"
        and "BHD pa buf3L = BHD pa buf3R"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: 'a
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
        and xa :: 'b
      using that by (intro conjI[rotated] exI wbc_base; (rule refl)?; fastforce)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf1L) buf2L) buf2R) (id_op (case_sum (BTL x1 buf1L) buf1R)) (aeq_op (case_sum buf3L buf3R))))"
      if "(x1::'a) \<notin> defaults"
        and "buf1L x1 \<noteq> []"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, 'a + 'a, 'b) op"
        and q :: "'a + 'a"
        and pa :: "'a + 'a"
        and x1 :: 'a
      using that apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply (rule refl)+
      apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      done 
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L (BENQ x2 (BHD x2 buf1R) buf2R)) (id_op (case_sum buf1L (BTL x2 buf1R))) (aeq_op (case_sum buf3L buf3R))))"
      if "(x2::'a) \<notin> defaults"
        and "buf1R x2 \<noteq> []"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, 'a + 'a, 'b) op"
        and q :: "'a + 'a"
        and pa :: "'a + 'a"
        and x2 :: 'a
      using that apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply (rule refl)+
      apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      done 
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum (BTL pa buf2L) buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BENQ pa (BHD pa buf2L) buf3L) buf3R))))"
      if "buf2L pa \<noteq> []"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
      using that apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply (rule refl)+
      apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      done 
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L (BTL pa buf2R)) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L (BENQ pa (BHD pa buf2R) buf3R)))))"
      if "buf2R pa \<noteq> []"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
      using that apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply (rule refl)+
      apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
      done   
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1L buf2L buf3L buf1R buf2R buf3R. op1xx = aeq_op (case_sum ((buf1L >> buf2L) >> buf3L) ((buf1R >> buf2R) >> buf3R)) \<and> op2xx = map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum buf3L buf3R)))) op2' (map_op projl projr (comp_op Some (case_sum buf2L buf2R) (id_op (case_sum buf1L buf1R)) (aeq_op (case_sum (BTL pa buf3L) (BTL pa buf3R)))))"
      if "buf3L pa \<noteq> []"
        and "buf3R pa \<noteq> []"
        and "BHD pa buf3L \<noteq> BHD pa buf3R"
        and "pa \<notin> defaults"
      for io' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) op"
        and op2' :: "('a + 'a, 'a, 'b) op"
        and pa :: 'a
      using that apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply (rule refl)+
      apply auto
      done
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM2 apply (elim exE conjE disjE step_id_op_cases step_comp_op_elim step_map_op_elim step_aeq_op_elim; simp split: if_splits sum.splits ; hypsubst_thin)
                apply (rule prems; assumption)+
        done
      done
  qed
qed  

abbreviation "\<Q>' \<equiv> \<Q>\<turnstile>"

lemma aeq_id_absorb:
  "\<Q> \<approx> \<stileturn>\<Q>"
  unfolding scomp_op_def
  using aeq_id_absorb_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", simplified] by simp

end
