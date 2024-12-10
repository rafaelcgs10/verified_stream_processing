section \<open>The composition operator\<close>

theory Composition

imports
  Operator
begin

(*workaround about termination issue in corecursive*)
lemma case_prod_cong4[fundef_cong]:
  fixes prod prod' f g
  shows "prod = prod' \<Longrightarrow>
    (\<And>x1 x2 y1 y2. prod' = ((x1, x2), (y1, y2)) \<Longrightarrow> f x1 x2 y1 y2 = g x1 x2 y1 y2) \<Longrightarrow>
    ((\<lambda>((x1, x2), (y1, y2)). f x1 x2 y1 y2) prod) = ((\<lambda>((x1, x2), (y1, y2)). g x1 x2 y1 y2) prod')"
  by (auto split: prod.splits)

datatype (discs_sels) ('ip1, 'ip2, 'op1, 'op2, 'd) comp_op_aux =
  Read_aux "'ip1 + 'ip2" "'d \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op"
  | Write_aux "('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op" "'op1 + 'op2" 'd
  | Base_aux "(('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op)"
  | end_op_aux
  | spin_aux

abbreviation eval_comp_op_aux where
  "eval_comp_op_aux c aux \<equiv> (case aux of
    Read_aux p f \<Rightarrow> Read p (\<lambda>y. let (buf, op1, op2) = f y in c buf op1 op2)
  | Write_aux (buf, op1, op2) q x \<Rightarrow> Write (c buf op1 op2) q x
  | Base_aux (buf, op1, op2) \<Rightarrow> c buf op1 op2
  | end_op_aux \<Rightarrow> end_op
  | spin_aux \<Rightarrow> spin_op)"

abbreviation "sound_reads wire buf \<equiv> cfilter (\<lambda> op. case op of Read p f \<Rightarrow> p \<notin> ran wire \<or> buf p \<noteq> [] | _ \<Rightarrow> True)"

corec comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op" where
  "comp_op wire buf op1 op2 =
     Choice (cimage (eval_comp_op_aux (comp_op wire)) (cUn
       (cimage (\<lambda>op. case op of
           Read p f \<Rightarrow> Read_aux (Inl p) (\<lambda>x. (buf, f x, op2))
         | Write op p x \<Rightarrow> (case wire p of
             None \<Rightarrow> Write_aux (buf, op, op2) (Inl p) x
           | Some q \<Rightarrow> Base_aux (BENQ q x buf, op, op2))) (choices op1))
       (cimage (\<lambda>op. case op of
           Read p f \<Rightarrow> if p \<in> ran wire then Base_aux (BTL p buf, op1, f (BHD p buf))
             else Read_aux (Inr p) (\<lambda>x. (buf, op1, f x))
         | Write op p x \<Rightarrow> Write_aux (buf, op1, op) (Inr p) x) (sound_reads wire buf (choices op2)))))"


lemma comp_op_code: "comp_op wire buf op1 op2 =
  Choice (cUn
    (cimage (\<lambda>op. case op of
        Read p f \<Rightarrow> Read (Inl p) (\<lambda>x. comp_op wire buf (f x) op2)
      | Write op p x \<Rightarrow> (case wire p of
          None \<Rightarrow> Write (comp_op wire buf op op2) (Inl p) x
        | Some q \<Rightarrow> comp_op wire (BENQ q x buf) op op2)) (choices op1))
    (cimage (\<lambda>op. case op of
        Read p f \<Rightarrow> if p \<in> ran wire then comp_op wire (BTL p buf) op1 (f (BHD p buf))
          else Read (Inr p) (\<lambda>x. comp_op wire buf op1 (f x))
      | Write op p x \<Rightarrow> Write (comp_op wire buf op1 op) (Inr p) x) (sound_reads wire buf (choices op2))))"
  apply (subst comp_op.code)
  apply (unfold cimage_cUn op.inject)
  apply (rule arg_cong2[where f = cUn])
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: comp_op_aux.splits op.splits option.splits)
  done

lemma comp_op_simps[simp]:
  "comp_op wire buf (Read p1 f1) (Read p2 f2) =
    Choice (cinsert (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Read p2 f2)))
     (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (comp_op wire (buf(p2 := btl (buf p2))) (Read p1 f1) (f2 (BHD p2 buf))))
      else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Read p1 f1) (f2 y)))))"
  "comp_op wire buf (Read p1 f1) (Write op2 q2 x2) =
    choice2 (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Write op2 q2 x2))) (Write (comp_op wire buf (Read p1 f1) op2) (Inr q2) x2)"
  "comp_op wire buf (Read p1 f1) (Choice op2s) = 
    Choice (cinsert (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Choice op2s))) (cimage
       (case_op (\<lambda>p f. if p \<in> ran wire then comp_op wire (buf(p := btl (buf p))) (Read p1 f1) (f (BHD p buf)) else Read (Inr p) (\<lambda>x. comp_op wire buf (Read p1 f1) (f x)))
         (\<lambda>op p. Write (comp_op wire buf (Read p1 f1) op) (Inr p)) (\<lambda>a. undefined))
       (sound_reads wire buf (cUnion (cimage choices op2s)))))"
  "comp_op wire buf (Write op1 q1 x1) (Read p2 f2) =
    Choice (cinsert (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Read p2 f2)) (Inl q1) x1
      | Some q \<Rightarrow> comp_op wire (buf(q := benq x1 (buf q))) op1 (Read p2 f2))
      (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (comp_op wire (buf(p2 := btl (buf p2))) (Write op1 q1 x1) (f2 (BHD p2 buf))))
        else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Write op1 q1 x1) (f2 y)))))"
  "comp_op wire buf (Write op1 q1 x1) (Write op2 q2 x2) =
    choice2 (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Write op2 q2 x2)) (Inl q1) x1
      | Some q \<Rightarrow> comp_op wire (buf(q := benq x1 (buf q))) op1 (Write op2 q2 x2))
      (Write (comp_op wire buf (Write op1 q1 x1) op2) (Inr q2) x2)"
  "comp_op wire buf (Write op1 q1 x1) (Choice op2s) =
     Choice (cinsert (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Choice op2s)) (Inl q1) x1
      | Some q \<Rightarrow> comp_op wire (buf(q := benq x1 (buf q))) op1 (Choice op2s))
      (cimage
       (case_op (\<lambda>p f. if p \<in> ran wire then comp_op wire (buf(p := btl (buf p))) (Write op1 q1 x1) (f (BHD p buf)) else Read (Inr p) (\<lambda>x. comp_op wire buf (Write op1 q1 x1) (f x)))
         (\<lambda>op p. Write (comp_op wire buf (Write op1 q1 x1) op) (Inr p)) (\<lambda>a. undefined))
       (sound_reads wire buf (cUnion (cimage choices op2s)))))"
  "comp_op wire buf (Choice op1s) (Read p2 f2) =
    Choice (cUn (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (comp_op wire (buf(p2 := btl (buf p2))) (Choice op1s) (f2 (BHD p2 buf))))
        else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Choice op1s) (f2 y)))) (cimage
       (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Read p2 f2)))
         (\<lambda>op p x. case wire p of None \<Rightarrow> Write (comp_op wire buf op (Read p2 f2)) (Inl p) x | Some q \<Rightarrow> comp_op wire (buf(q := benq x (buf q))) op (Read p2 f2)) (\<lambda>a. undefined))
       (cUnion (cimage choices op1s))))"
  "comp_op wire buf (Choice op1s) (Write op2 q2 x2) =
    Choice (cinsert (Write (comp_op wire buf (Choice op1s) op2) (Inr q2) x2) (cimage
       (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Write op2 q2 x2)))
         (\<lambda>op p x. case wire p of None \<Rightarrow> Write (comp_op wire buf op (Write op2 q2 x2)) (Inl p) x | Some q \<Rightarrow> comp_op wire (buf(q := benq x (buf q))) op (Write op2 q2 x2)) (\<lambda>a. undefined))
       (cUnion (cimage choices op1s))))"
  "comp_op wire buf (Choice op1s) (Choice op2s) =
    Choice (cUn (cimage
             (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Choice op2s)))
               (\<lambda>op p x.
                   case wire p of None \<Rightarrow> Write (comp_op wire buf op (Choice op2s)) (Inl p) x
                   | Some q \<Rightarrow> comp_op wire (buf(q := benq x (buf q))) op (Choice op2s))
               (\<lambda>a. undefined))
             (cUnion (cimage choices op1s)))
        (cimage
          (case_op
            (\<lambda>p f. if p \<in> ran wire then comp_op wire (buf(p := btl (buf p))) (Choice op1s) (f (BHD p buf))
                   else Read (Inr p) (\<lambda>x. comp_op wire buf (Choice op1s) (f x)))
            (\<lambda>op p. Write (comp_op wire buf (Choice op1s) op) (Inr p)) (\<lambda>a. undefined))
          (sound_reads wire buf (cUnion (cimage choices op2s)))))"
  by (subst comp_op_code, auto simp add: image_iff split: option.splits)+

no_notation Sublist.parallel (infixl "\<parallel>" 50)

definition pcomp_op (infixl "\<parallel>" 64) where
  "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. [])"

definition scomp_op (infixl "\<bullet>" 65) where
  "scomp_op op1 op2 = map_op projl projr (comp_op Some (\<lambda>_. []) op1 op2)"

abbreviation id_empty_op ("\<I>") where
  "\<I> \<equiv> id_op (\<lambda> _. [])"

abbreviation buffered ("\<stileturn> _ \<turnstile>" [150]151) where
  "\<stileturn>op\<turnstile> \<equiv> \<I> \<bullet> op \<bullet> \<I>"

fun reassoc where
  "reassoc (Inl (Inl x)) = Inl x"
| "reassoc (Inl (Inr x)) = Inr (Inl x)"
| "reassoc (Inr x) = Inr (Inr x)"

fun assoc where
  "assoc (Inl x) = Inl (Inl x)"
| "assoc (Inr (Inl x)) = Inl (Inr x)"
| "assoc (Inr (Inr x)) = Inr x"

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

lemma
  "(spin_op \<parallel> spin_op) ~ spin_op"
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


lemma step_comp_op_L:
  "step op1 io op1' \<Longrightarrow>
   (case io of Inp p x \<Rightarrow> True | Out p x \<Rightarrow> p \<notin> dom wire) \<Longrightarrow>
   step (comp_op wire buf op1 op2) (map_IO Inl Inl id io) (comp_op wire buf op1' op2)"
  apply (induct op1 io op1' arbitrary: op2 buf rule: step.induct)
  unfolding pcomp_op_def
  subgoal
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
     apply (auto split: IO.splits intro: step.intros)
    done
  subgoal
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
     apply (auto split: IO.splits option.splits intro: step.intros)
    done
  subgoal
    apply (erule step_choicesE)
    apply simp
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (rule cimage_eqI)
    apply (rule refl)
    apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) [2]
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (rule cimage_eqI)
    apply (rule refl)
    apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) 
    apply (smt (verit) not_Some_eq option.simps(4) step.intros(2))
    done
  done

lemma step_comp_op_R:
  "step op2 io op2' \<Longrightarrow>
   (case io of Out p x \<Rightarrow> True | Inp p x \<Rightarrow> p \<notin> ran wire) \<Longrightarrow>
   step (comp_op wire buf op1 op2) (map_IO Inr Inr id io) (comp_op wire buf op1 op2')"
  apply (induct op2 io op2' arbitrary: op1 buf rule: step.induct)
  unfolding pcomp_op_def
  subgoal for p f x op1 buf
    apply (subst (1) comp_op_code)
    unfolding cfilter_def Set.filter_def
         apply (clarsimp split: IO.splits option.splits intro: step.intros)
    subgoal
    apply (rule step.intros(3))
     apply (rule cUnI2)
       apply simp
       apply (rule image_eqI[of "Read (Inr p) (\<lambda>x. comp_op wire buf op1 (f x))" _ "Read p f"])
        apply simp_all
      subgoal 
        apply (subst cset.acset_inverse)
        apply (auto simp add: countableI' inj_on_def)
        done
      subgoal
        by (meson step.intros(1))
      done
    done
  subgoal for op q x op1 buf
  apply (subst (1) comp_op_code)
    unfolding cfilter_def Set.filter_def
         apply (clarsimp split: IO.splits option.splits intro: step.intros)
 apply (rule step.intros(3))
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
    subgoal for op ops l op' op1 buf
    apply (erule step_choicesE)
      subgoal for p f x
        apply simp
        apply hypsubst_thin
        apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
         apply (rule cUnI2)
        apply simp
         apply (rule image_eqI[of "Read (Inr p) (\<lambda>x. comp_op wire buf op1 (f x))" _ "Read p f"])
          apply simp
    unfolding cfilter_def Set.filter_def
     apply auto
    apply (meson step.intros(1))
    done
  subgoal for p x
        apply simp
        apply hypsubst_thin
        apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
         apply (rule cUnI2)
        apply simp
       apply (rule image_eqI[of _ _ "Write op' p x"])
          apply simp
    unfolding cfilter_def Set.filter_def
     apply auto
    apply (meson step.intros(2))
    done
  done
  done

inductive step_comp_op_inv for wire io where
  "step op1 (Inp p x) op1' \<Longrightarrow> io = Inp (Inl p) x \<Longrightarrow> step_comp_op_inv wire io (comp_op wire buf op1' op2) buf op1 op2"
| "step op2 (Out p x) op2' \<Longrightarrow> io = Out (Inr p) x \<Longrightarrow> step_comp_op_inv wire io (comp_op wire buf op1 op2') buf op1 op2"
| "step op1 (Out p x) op1' \<Longrightarrow> p \<notin> dom wire \<Longrightarrow> io = Out (Inl p) x \<Longrightarrow> step_comp_op_inv wire io (comp_op wire buf op1' op2) buf op1 op2"
| "step op2 (Inp p x) op2' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> io = Inp (Inr p) x \<Longrightarrow> step_comp_op_inv wire io (comp_op wire buf op1 op2') buf op1 op2"
| "step_comp_op_inv wire io op (BENQ q x buf) op1' op2 \<Longrightarrow> step op1 (Out p x) op1' \<Longrightarrow> wire p = Some q \<Longrightarrow> step_comp_op_inv wire io op buf op1 op2"
| "step_comp_op_inv wire io op (BTL p buf) op1 op2' \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> BHD p buf = x \<Longrightarrow> step op2 (Inp p x) op2' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> step_comp_op_inv wire io op buf op1 op2"

lemma step_step_comp_op_inv:
  "step (comp_op wire buf op1 op2) io op \<Longrightarrow>
   step_comp_op_inv wire io op buf op1 op2"
  apply (induct "comp_op wire buf op1 op2" io op arbitrary: op1 op2 buf rule: step.induct)
  subgoal for p f x op1 op2 buf
    apply (cases op1; cases op2)
            apply auto
    done
  subgoal for op q x op1 op2 buf
    apply (cases op1; cases op2)
            apply auto
    done
  subgoal for op ops l op' op1 op2 buf
    apply (cases op1; cases op2)
    subgoal
      apply hypsubst_thin
      apply (auto simp add: split: option.splits if_splits intro: step_comp_op_inv.intros step.intros)
      done
    subgoal
      by (auto split: if_splits intro: step_comp_op_inv.intros step.intros)
    subgoal
      apply hypsubst_thin
      apply (clarsimp split: op.splits if_splits)
      subgoal
        apply (auto 1 1 split: op.splits if_splits; hypsubst_thin)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        subgoal
          by (metis Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        done
      done
    subgoal
      apply hypsubst_thin
      apply (auto split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
      done 
    subgoal
      apply hypsubst_thin
      apply (auto split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
      done 
    subgoal
      apply hypsubst_thin
      apply (clarsimp split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
      subgoal
        apply (auto 1 1 split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        done
      subgoal
        apply (auto 1 1 split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        subgoal
          by (metis Write_in_choices_step Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
        done
      done
    subgoal
      apply hypsubst_thin
      apply (clarsimp split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
      subgoal
        by (metis Write_in_choices_step domIff Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
      subgoal
        apply (auto 1 1 split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
        apply (meson Write_in_choices_step cin.rep_eq step_comp_op_inv.intros(3) domIff step.intros(3))
        done
      subgoal
        by (metis Write_in_choices_step domIff Read_in_choices_step cin.rep_eq step_comp_op_inv.intros step.simps)
      subgoal
        apply (auto 1 1 split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
        done
      subgoal
        apply (auto split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
          apply (meson Read_in_choices_step cin.rep_eq step.intros(3) step_comp_op_inv.intros(1))
         apply (meson Write_in_choices_step cin.rep_eq step_comp_op_inv.intros(3) domIff step.intros(3))
        apply (metis Write_in_choices_step cin.rep_eq step.simps step_comp_op_inv.intros(5))
        done
      subgoal
        apply (auto 1 1 split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
          apply (meson Read_in_choices_step cin.rep_eq step.intros(3) step_comp_op_inv.intros(1))
         apply (meson Write_in_choices_step cin.rep_eq step_comp_op_inv.intros(3) domIff step.intros(3))
        apply (metis Write_in_choices_step cin.rep_eq step.simps step_comp_op_inv.intros(5))
        done
      done
    subgoal
      apply (auto 1 1 split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
      subgoal
        by (meson Read_in_choices_step cin.rep_eq step_comp_op_inv.intros(1) step.intros(3))
      subgoal
        by (meson Write_in_choices_step cin.rep_eq step_comp_op_inv.intros(3) domIff step.simps)
      subgoal
        by (metis Write_in_choices_step cin.rep_eq step_comp_op_inv.intros(5) step.intros(3))
      done
    subgoal
      apply (auto 1 1 split: option.splits op.splits if_splits intro: step_comp_op_inv.intros intro!: step.intros; hypsubst_thin)
      subgoal
        by (meson Read_in_choices_step cin.rep_eq step_comp_op_inv.intros(1) step.intros(3))
      subgoal
        by (meson Write_in_choices_step cin.rep_eq step_comp_op_inv.intros(3) domIff step.simps)
      subgoal
        by (metis Write_in_choices_step cin.rep_eq step_comp_op_inv.intros(5) step.intros(3))
      subgoal
        by (metis Read_in_choices_step cin.rep_eq step.intros(3) step_comp_op_inv.intros(6))
      subgoal
        by (meson Read_in_choices_step cin.rep_eq step.intros(3) step_comp_op_inv.intros(4))
      subgoal
        by (meson Write_in_choices_step cin.rep_eq step.intros(3) step_comp_op_inv.intros(2))
      done
    done
  done

datatype ('ip, 'op, 'd) label = Inpl 'ip 'd | Outl 'op 'd | Tau

inductive trans where
  "trans (Inpl p x) (Read p f) (f x)"
| "trans (Outl q x) (Write op q x) op"
| "cin op ops \<Longrightarrow> trans Tau (Choice ops) op"
| "trans Tau (Choice {||}) (Choice {||})"

inductive_cases transReadE [elim!]: "trans l (Read p f) op'"
inductive_cases transWriteE [elim!]: "trans l (Write op q x) op'"
inductive_cases transChoiceE [elim!]: "trans l (Choice ops) op'"

lemma 
  "trans l (comp_op Some buf op1' op2) op \<Longrightarrow>
   csubset_eq (choices op1') (choices op1) \<Longrightarrow>
   trans l (comp_op Some buf op1 op2) op"
  apply (induct l "comp_op Some buf op1' op2" op arbitrary: op1' op1 op2 buf rule: trans.induct)
    apply (subst (asm) comp_op_code, simp)
    apply (subst (asm) comp_op_code, simp)
  subgoal for op ops op1' op2 buf op1
    apply (subst (asm) (1) comp_op_code)
    apply (simp add: Set.filter_def ranI image_iff bex_Un)
    apply (elim disjE bexE exE conjE)
    subgoal for op
      apply (cases op, simp)
      subgoal for p f
      apply hypsubst_thin
        apply (subst comp_op_code)
        apply simp
        apply (rule trans.intros(3))
        apply (simp add: Set.filter_def ranI image_iff bex_Un)
        apply (rule disjI1)
        apply (rule bexI[of _ "Read p f"])
         apply auto
        done
      subgoal for op' p x
        apply (subst comp_op_code)
        apply simp
        apply (rule trans.intros(3))
        apply (simp add: Set.filter_def ranI image_iff bex_Un)
        apply (rule disjI1)
     apply (rule bexI[of _ "Write op' p x"])
         apply auto
        done
      subgoal
        by blast
      done
    subgoal for op
      apply hypsubst_thin
   apply (cases op, simp)
      subgoal for p f
        apply hypsubst_thin
     apply (subst comp_op_code)
        apply simp
        apply (rule trans.intros(3))
        apply (simp add: Set.filter_def ranI image_iff bex_Un)
        apply (rule disjI2)
        apply (rule exI[of _ "Read p f"])
        apply auto
        oops


lemma step_dummy_source_io:
  "step op io op' \<Longrightarrow>
   op = dummy_source_op x \<Longrightarrow>
   op' = dummy_source_op x \<and> (\<exists> p. io = Out p x)"
  by (subst (asm) dummy_source_op.code, auto)

lemma step_comp_op_inv_source_sink_False:
  "step_comp_op_inv Some io op' buf op1 op2 \<Longrightarrow>
   op1 = dummy_source_op 42 \<Longrightarrow>
   op2 = sink_op \<Longrightarrow>
   False"
  apply (induct op' _ op1 op2 rule: step_comp_op_inv.induct)
       apply (auto simp add: ranI dest: step_dummy_source_io)
   apply (metis IO.simps(4) sink_op.code stepReadE)
  apply (metis sink_op.code stepReadE)
  done

(* Axiom A9 *)
lemma dummy_source_op_sink_op_sping_op:
  "(dummy_source_op 42) \<bullet> sink_op ~ spin_op"
  unfolding scomp_op_def
  apply (coinduction rule: bisim_coinduct_upto)
  subgoal
    unfolding sim_def
    apply safe
    subgoal
      apply (drule step_map_op_inv)
      apply safe
      apply hypsubst_thin
      subgoal for io op'
        apply (drule step_step_comp_op_inv)
        apply (drule step_comp_op_inv_source_sink_False)
          apply auto
        done
      done
    subgoal 
      using step_spin_op_no_label by blast
    done
  done

lemma scomp_op_W_Id_can_end:
  "can_end (comp_op Some buf W cp_op)"
  apply (coinduction arbitrary: buf)
  subgoal for buf
    apply (rule disjI2)
    apply (intro conjI exI disjI1)
      apply (subst comp_op_code)
      apply auto
    done
  done

lemma scomp_op_AW_Id_can_end:
  "can_end (comp_op Some buf AW cp_op)"
  apply (coinduction arbitrary: buf)
  subgoal for buf
    apply (rule disjI2)
    apply (intro conjI exI disjI1)
      apply (subst comp_op_code)
      apply auto
    done
  done

lemma step_comp_op_inv_Sone_AW_Write:
  "step_comp_op_inv Some io op buf op1 op2 \<Longrightarrow>
   op1 = AW \<Longrightarrow>
   op2 = Write cp_op p x \<Longrightarrow>
   io = Out (Inr p) x \<and> (\<exists> buf'. op = comp_op Some buf' op1 cp_op)"
  apply (induct op buf op1 op2 rule: step_comp_op_inv.induct)
  subgoal
    using step_AW_inv by blast
  subgoal
    by fastforce
  subgoal
    by blast
  subgoal
    by (simp add: ranI)
  subgoal
    apply (auto simp add: ranI split: if_splits)
     apply (frule step_AW_inv)
      apply auto
    using step_AW_inv apply blast
    done
  subgoal
    apply (auto simp add: ranI split: if_splits)
    done
  done

lemma step_id_op_Inp:
  "step (id_op buf) io op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op' = id_op (BENQ p x buf)"
  apply (induct "id_op buf" io op' arbitrary: buf rule: step.induct)
    apply simp_all
   apply (subst (asm) id_op_code)
   apply simp
  apply (subst (asm) (3) id_op_code)
  apply auto
  done

lemma step_id_op_Out:
  "step (id_op buf) io op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   op' = id_op (BTL p buf) \<and> BHD p buf = x \<and> buf p \<noteq> []"
  apply (induct "id_op buf" io op' arbitrary: buf rule: step.induct)
    apply simp_all
   apply (subst (asm) id_op_code)
   apply simp
  apply (subst (asm) (3) id_op_code)
  apply auto
  done

lemma choices_id_op[simp]:
  "choices (id_op buf) = (cUn 
    (cimage (\<lambda> p. Read p ((\<lambda> x. id_op (BENQ p x buf)))) cUNIV)
    (cimage (\<lambda> p. Write (id_op (BTL p buf)) p (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: ('m :: countable) cset))))"
  unfolding choices_def
  apply (subst id_op_code)
  apply (auto simp add: Set.filter_def)
  subgoal premises prems for _ n
    using prems(2-) apply -
    apply (induct n arbitrary: buf)
     apply auto
    done
  subgoal for p
    apply (rule bexI[of _ 1])
     apply (auto simp add: natcUNIV.rep_eq)
    done
  subgoal for p
    apply (rule bexI[of _ 1])
     apply (auto simp add: natcUNIV.rep_eq)
    done
  done

lemma BHD_BAPPEND_2_cases:
  "BHD p ((buf1 >> buf2) >> buf3) = x \<Longrightarrow>
  ((buf1 >> buf2) >> buf3) p \<noteq> [] \<Longrightarrow>
   BHD p buf3 = x \<and> buf3 p \<noteq> [] \<or>
   buf3 p = [] \<and> BHD p buf2 = x \<and> buf2 p \<noteq> [] \<or>
   buf3 p = [] \<and> buf2 p = [] \<and> BHD p buf1 = x \<and> buf1 p \<noteq> []"
  by (metis append_Nil hd_append)

lemma step_comp_op_Some_id_op_id_op:
  "step (comp_op Some buf2 op1 op2) io op \<Longrightarrow>
   op1 = id_op buf1 \<Longrightarrow>
   op2 = id_op buf3 \<Longrightarrow>
   (\<exists> p x. io = Inp (Inl p) x \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some buf2' (id_op (BENQ p x buf1')) (id_op buf3') \<and>
      buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3')) \<or>

   (\<exists> p x. io = Out (Inr p) x \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some buf2' (id_op buf1') (id_op (BTL p buf3')) \<and> BHD p buf3' = x \<and> buf3' p \<noteq> [] \<and>
     buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3'))"
  apply (drule step_step_comp_op_inv)
  subgoal
    apply (rotate_tac 2)
    apply (induct op buf2 op1 op2 arbitrary: buf1 buf3 rule: step_comp_op_inv.induct)
    subgoal
      using step_id_op_Inp by fast
    subgoal
      using step_id_op_Out by fast
    subgoal
      using step_id_op_Inp by fast
    subgoal
      using step_id_op_Out by (metis ranI)
    subgoal for op q x buf op1' op2 op1 p buf1 buf3
      apply hypsubst_thin
      apply (drule step_id_op_Out)
       apply (rule refl)
      apply auto
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      subgoal
        apply (intro exI conjI)
         apply (rule refl)
        apply (subst (1 2) BULK_BENQ_assoc[symmetric])
        apply (rule ext)
        apply hypsubst_thin
        apply (auto simp add: fun_upd_idem_iff)
        apply (smt (verit, del_insts) append_Cons append_assoc eq_Nil_appendI list.collapse)
        done
      subgoal for p
        apply hypsubst_thin
        apply (drule spec)+
        apply (drule mp)
         apply (rule refl)
        apply (drule mp)
         apply (rule refl)
        apply auto
        apply (drule sym)
        apply simp
        apply (auto split: if_splits)
        done
      done
    subgoal for op p buf op1 op2' x op2 buf1 buf3
      apply hypsubst_thin
      apply (drule step_id_op_Inp)
       apply (rule refl)
      apply auto
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      subgoal
        apply (intro exI conjI)
         apply (rule refl)
        apply (subst (1 2) BULK_BENQ_assoc[symmetric])
        apply hypsubst_thin
        apply (auto simp add: fun_upd_idem_iff)
        apply (drule sym)
        apply simp
        apply (rule ext)
        apply auto
        done
      subgoal for p
        apply hypsubst_thin
        apply (drule spec)+
        apply (drule mp)
         apply (rule refl)
        apply (drule mp)
         apply (rule refl)
        apply auto
        apply (drule sym)
        apply simp
        apply (auto split: if_splits)
        done
      done
    done
  done

lemma id_id_gen:
  "bisim (map_op projl projr (comp_op Some buf2 (id_op buf1) (id_op buf3))) (id_op (buf1 >> buf2 >> buf3))"
  apply (coinduction arbitrary: buf1 buf2 buf3 rule: bisim_coinduct_upto)
  subgoal for buf1 buf2 buf3
    unfolding sim_def
    apply auto
    subgoal for io op
      apply (drule step_map_op_inv)
      apply safe
      apply (drule step_comp_op_Some_id_op_id_op)
        apply simp_all
      apply (elim exE disjE)
      subgoal for io' op'' p x
        apply simp
        apply (intro conjI exI)
         apply (subst id_op_code)
         apply (rule step.intros(3))
          apply simp
          apply (rule disjI1)
          apply (rule image_eqI[of _ _ p])
           apply (rule refl)
          apply (simp add: cUNIV.rep_eq)
         apply (rule step.intros(1))
        apply (rule bc_base)
        apply auto
        apply (intro conjI exI)
         apply (rule refl)
        apply (rule arg_cong[where f=id_op]) 
        apply (auto split: option.splits)
        apply hypsubst_thin
        apply (rule ext)
        apply (clarsimp split: if_splits)
        apply meson
        done
      subgoal for io' op'' p x
        apply auto
        subgoal for p'
          apply (drule sym[of x])
          apply simp
          apply hypsubst_thin
          apply (intro conjI exI)
           apply (subst id_op_code)
           apply (rule step.intros(3))
            apply simp
            apply (rule disjI2)
            apply (rule image_eqI[of _ _ p])
             apply (rule refl)
            apply (simp add: cUNIV.rep_eq)
          using step.intros(2) apply force
          apply (rule bc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op]) 
          apply (auto split: option.splits)
          done
        done
      done      
    subgoal for io op
      apply (cases io)
      subgoal for p x
        apply hypsubst_thin
        apply (drule step_id_op_Inp)
         apply simp
        apply hypsubst_thin
        apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op (BENQ p x buf1)) (id_op buf3))"])
        apply (intro conjI)
        subgoal
          apply (rule step_map_op[where f=projl and g=projr and io="Inp (Inl p) x", simplified])
          apply (subst comp_op_code)
          apply simp
          apply (rule step.intros(3))
           apply (simp add: Set.filter_def)
           apply (rule disjI1)
           apply simp
           apply (rule image_eqI)
            apply (rule refl)
           apply simp
           apply (rule disjI1)
           apply (rule image_eqI[of _ _ p])
            apply (rule refl)
           apply (simp add: cUNIV.rep_eq)
          apply simp
          apply (rule step.intros(1))
          done
        subgoal
          apply (rule bc_sym)
          apply (rule bc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply (rule ext)
          apply auto
          done
        done
      subgoal for p x
        apply hypsubst_thin
        apply (drule step_id_op_Out)
         apply simp
        apply (elim conjE)
        apply (drule BHD_BAPPEND_2_cases)
         apply simp
        apply hypsubst_thin
        apply (elim exE disjE)
        subgoal
          apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op buf1) (id_op (BTL p buf3)))"])
          apply (intro conjI)
          subgoal
            apply (rule step_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply (simp add: Set.filter_def)
             apply (rule disjI2)
             apply (rule image_eqI)
              apply (rule refl)
             apply (simp add: cUNIV.rep_eq)
             apply (intro conjI)
              apply (rule disjI2)
              apply (rule image_eqI[of _ _ p])
               apply (rule refl)
              apply (auto simp add: step.intros(2))
            done
          subgoal
            apply (rule bc_sym)
            apply (rule bc_base)
            apply (intro exI conjI) 
             apply (rule refl)
            apply (rule arg_cong[where f=id_op])
            apply (rule ext)
            apply (auto simp only: split: if_splits)
              apply (smt (verit, best) fun_upd_apply tl_append2)+
            done
          done
        subgoal
          apply (rule exI[of _ "map_op projl projr (comp_op Some (BTL p buf2) (id_op buf1) (id_op buf3))"])
          apply (intro conjI)
          subgoal
            apply (rule step_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply (simp add: Set.filter_def)
             apply (rule disjI2)+
             apply (rule image_eqI)
              apply (rule refl)
             apply (simp add: cUNIV.rep_eq)
             apply (intro conjI)
              apply (rule disjI1)
              apply (rule image_eqI[of _ _ p])
               apply (rule refl)
              apply simp
             apply simp
            apply simp
            apply (simp add: ranI)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply (simp add: Set.filter_def)
             apply (rule disjI2)+
             apply (rule image_eqI)
              apply (rule refl)
             apply (simp add: cUNIV.rep_eq)
             apply (intro conjI)
              apply (rule disjI2)
              apply (rule image_eqI[of _ _ p])
               apply (rule refl)
              apply simp_all
            apply (metis fun_upd_triv step.intros(2))
            done
          subgoal
            apply (rule bc_sym)
            apply (rule bc_base)
            apply (intro exI conjI) 
             apply (rule refl)
            apply (rule arg_cong[where f=id_op])
            apply (rule ext)
            apply (auto simp only:  split: if_splits)
             apply (smt (verit, best) append_self_conv2 fun_upd_other fun_upd_same tl_append2)+
            done
          done
        subgoal
          apply (elim conjE)
          apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op (BTL p buf1)) (id_op buf3))"])
          apply (intro conjI)
          subgoal
            apply (rule step_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
            apply (subst (1) comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply (simp add: cUNIV.rep_eq Set.filter_def)
             apply (rule disjI1)
             apply simp
             apply (rule image_eqI)
              defer
              apply (simp add: cUNIV.rep_eq)
              apply (rule disjI2)
              apply (rule image_eqI[of _ _ p])
               apply (rule refl)
              apply simp
             apply simp_all
            apply (subst (1) comp_op_code)
            apply (rule step.intros(3))
             apply (simp add: cUNIV.rep_eq Set.filter_def)
             apply (rule disjI2)
             apply (rule image_eqI)
              apply (rule refl)
             apply simp_all
             apply (intro conjI)
              apply (rule disjI1)
              apply (rule image_eqI[of _ _ p])
               apply (rule refl)
              apply (simp_all add: ranI)
            apply (subst (1) comp_op_code)
            apply (rule step.intros(3))
             apply simp
             apply (rule disjI2)
             apply (rule image_eqI)
              apply (rule refl)
             apply simp
             apply (intro conjI)
              apply (rule disjI2)
              apply (rule image_eqI[of _ _ p])
               apply (rule refl)
              apply simp
            using cUNIV.rep_eq apply blast
             apply simp_all
            apply (metis fun_upd_triv step.simps)
            done
          subgoal
            apply (rule bc_sym)
            apply (rule bc_base)
            apply (intro exI conjI) 
             apply (rule refl)
            apply (rule arg_cong[where f=id_op])
            apply (rule ext)
            apply (auto simp only:  split: if_splits)
            apply (smt (verit, best) append_self_conv2 fun_upd_other fun_upd_same tl_append2)+
            done
          done
        done
      done
    done
  done

lemma scomp_op_id_id:
  "\<I> \<bullet> \<I> ~ \<I>"
  unfolding scomp_op_def
  using id_id_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] apply simp
  done


inductive step_comp_op_assoc_inv for io where
  "step op1 (Inp p x) op1' \<Longrightarrow> io = Inp (Inl p) x \<Longrightarrow> step_comp_op_assoc_inv io op1 buf1 op2 buf2 op3 op1' buf1 op2 buf2 op3"
| "step op3 (Out p x) op3' \<Longrightarrow> io = Out (Inr p) x \<Longrightarrow> step_comp_op_assoc_inv io op1 buf1 op2 buf2 op3 op1 buf1 op2 buf2 op3'"
| "step op1 (Out p x) op1' \<Longrightarrow> step_comp_op_assoc_inv io op1' (BENQ p x buf1) op2 buf2 op3 op1'' buf1' op2' buf2' op3' \<Longrightarrow>
   step_comp_op_assoc_inv io op1 buf1 op2 buf2 op3 op1'' buf1' op2' buf2' op3'"
| "step op2 (Inp p x) op2' \<Longrightarrow> buf1 p \<noteq> [] \<Longrightarrow> step_comp_op_assoc_inv io op1' (BTL p buf1) op2' buf2 op3 op1'' buf1' op2'' buf2' op3' \<Longrightarrow>
   step_comp_op_assoc_inv io op1 buf1 op2 buf2 op3 op1' buf1' op2'' buf2' op3'"
| "step op2 (Out p x) op2' \<Longrightarrow> step_comp_op_assoc_inv io op1' buf1 op2' (BENQ p x buf2) op3 op1'' buf1' op2'' buf2' op3' \<Longrightarrow>
   step_comp_op_assoc_inv io op1 buf1 op2 buf2 op3 op1' buf1' op2'' buf2' op3'"
| "step op3 (Inp p x) op3' \<Longrightarrow> buf2 p \<noteq> [] \<Longrightarrow> step_comp_op_assoc_inv io op1' buf1 op2 (BTL p buf2) op3' op1'' buf1' op2' buf2' op3'' \<Longrightarrow>
   step_comp_op_assoc_inv io op1 buf1 op2 buf2 op3 op1' buf1' op2' buf2' op3''"

lemma step_step_comp_op_inv_aux:
  "step_comp_op_inv wire io op buf op1 op2 \<Longrightarrow> step (comp_op wire buf op1 op2) io op"
  oops

lemma aux2:
  "step_comp_op_inv Some io op2 buf op op' \<Longrightarrow> op |\<in>| ops \<Longrightarrow> step_comp_op_inv Some io op2 buf (Choice ops) op'"
  apply (induct op2 buf op op' rule: step_comp_op_inv.induct)
  subgoal
    by (auto 10 10 intro: step.intros step_comp_op_inv.intros)
  subgoal
    apply hypsubst_thin
    oops

lemma aux2:
  "step op1 (Out p x) op1' \<Longrightarrow> 
   step (comp_op Some (BENQ p x buf) op1' op2) io op \<Longrightarrow>
   step (comp_op Some buf op1 op2) io op"
  oops

lemma aux3:
  "op |\<in>| ops \<Longrightarrow>
   step op io op2 \<Longrightarrow>
   step (Choice ops) io op"
  oops

lemma
  "Read p f |\<in>| choices op \<Longrightarrow>
   step op (Inp p x) (f x)"
  oops

inductive choices_set where
  "choices_set (Read p f) (Read p f)"
| "choices_set (Write op' p x) (Write op' p x) "
| "choices_set op op' \<Longrightarrow> op' |\<in>| ops \<Longrightarrow> choices_set op (Choice ops)"

lemma choices_to_inductive:
  "op |\<in>| choices op' \<longleftrightarrow>
   choices_set op op'"
  apply (rule iffI)
  subgoal
    unfolding choices_def
    apply safe
    subgoal for n
      apply (induct n arbitrary: op')
      subgoal for op'
        apply (cases op; cases op')
                apply (auto intro: choices_set.intros)
        done
      subgoal for n op'
        apply (cases op; cases op')
        apply auto
        using choices_set.intros(3) natcUNIV.rep_eq apply auto
        done
      done
    done
  subgoal
    apply (induct op op' rule: choices_set.induct)
      apply auto
    done
  done

lemma choices_set_is_Read_comp_op:
  "choices_set op (comp_op Some buf op1' op2) \<Longrightarrow>
   choices_set op1' op1 \<Longrightarrow>
   is_Read op \<Longrightarrow>
   choices_set op (comp_op Some buf op1 op2)"
  apply (induct op "comp_op Some buf op1' op2" arbitrary: op2 op1 buf rule: choices_set.induct)
  subgoal
    apply (subst (asm) comp_op_code)
    apply simp
    done
  subgoal
    apply (subst (asm) comp_op_code)
    apply simp
    done
  subgoal for op op' ops op2 buf op1
    apply (subst (asm) (3) comp_op_code)
    apply (auto simp add: ranI split: op.splits if_splits)
    subgoal for p f
      apply (subst comp_op_code)
      apply auto
      apply hypsubst_thin
      apply (rule choices_set.intros(3))
       apply assumption
      apply simp
      apply (rule disjI1)
      apply (rule image_eqI[of _ _ "Read p f"])
       apply auto
      apply (metis choices_set.simps choices_to_inductive cin.rep_eq no_Choice_in_choices)
      done
    subgoal for op' p' x
      apply hypsubst_thin
      apply (subst comp_op_code)
      apply auto
      apply (rule choices_set.intros(3))
       apply assumption
      apply simp
      apply (rule disjI1)
      apply (rule image_eqI[of _ _ "Write op' p' x"])
       apply auto
      apply (metis choices_set.simps choices_to_inductive cin.rep_eq no_Choice_in_choices)
      done
    subgoal for p f
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply (subst comp_op_code)
      apply auto
      apply (rotate_tac 4)
      apply (rule choices_set.intros(3))
       apply assumption
      apply simp
      apply (rule disjI2)
      unfolding Set.filter_def
      apply simp
      apply (rule image_eqI[of _ _ "Read p f"])
       apply (auto simp add: ranI)
      oops

lemma aux3:
  "choices_set op (comp_op Some buf op1' op2) \<Longrightarrow>
   (\<forall> op. choices_set op op1' \<longrightarrow>  choices_set op op1) \<Longrightarrow>
   is_Read op \<Longrightarrow>
   choices_set op (comp_op Some buf op1 op2)"
  apply (induct op "comp_op Some buf op1' op2" arbitrary: op2 op1 buf rule: choices_set.induct)
  subgoal
    apply (subst (asm) comp_op_code)
    apply simp
    done
  subgoal
    apply (subst (asm) comp_op_code)
    apply simp
    done
  subgoal for op op' ops op2 buf op1
    apply (subst (asm) (3) comp_op_code)
    apply (auto simp add: ranI split: op.splits if_splits)
  subgoal for p f
      apply (subst comp_op_code)
      apply auto
      apply hypsubst_thin
      apply (rule choices_set.intros(3))
       apply assumption
      apply simp
      apply (rule disjI1)
      apply (rule image_eqI[of _ _ "Read p f"])
       apply auto
      apply (metis choices_set.simps choices_to_inductive cin.rep_eq no_Choice_in_choices)
      done
    subgoal for op' p' x
      apply hypsubst_thin
      apply (subst comp_op_code)
      apply auto
      apply (rule choices_set.intros(3))
       apply assumption
      apply simp
      apply (rule disjI1)
      apply (rule image_eqI[of _ _ "Write op' p' x"])
       apply auto
      apply (metis choices_set.simps choices_to_inductive cin.rep_eq no_Choice_in_choices)
      done
    subgoal for p f
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply (subst comp_op_code)
      apply auto
      apply (rotate_tac 4)
      apply (rule choices_set.intros(3))
       apply assumption
      apply simp
      apply (rule disjI2)
      unfolding Set.filter_def
      apply simp
      apply (rule image_eqI[of _ _ "Read p f"])
       apply (auto simp add: ranI)
      done
    subgoal for op' p' x
      apply hypsubst_thin
      apply (rotate_tac 3)
      apply (erule choices_set.cases)
        apply simp_all
      done
    done
  done

lemma aux3b:
  "op |\<in>| choices (comp_op Some buf op1' op2) \<Longrightarrow>
   (\<forall> op. op |\<in>| choices op1' \<longrightarrow> op |\<in>| choices op1) \<Longrightarrow>
   is_Read op \<Longrightarrow>
   op |\<in>| choices (comp_op Some buf op1 op2)"
  by (meson aux3 choices_to_inductive)

lemma aux2:
  "Write op1' p x \<in> rcset (choices op1) \<Longrightarrow>
   Read p' f \<in> rcset (choices (comp_op Some buf2 (map_op projl projr (comp_op Some (buf(p := bulk_benq [x] (buf p))) op1' op2)) op3)) \<Longrightarrow>
   Read p' f \<in> rcset (choices (comp_op Some buf2 (map_op projl projr (comp_op Some buf op1 op2)) op3))"
  apply (drule aux3b[simplified, of _ _ _ _ "map_op projl projr (comp_op Some buf op1 op2)"])
  subgoal
    apply auto
    apply (subst comp_op_code)
    apply simp
    apply (rule disjI1)
      apply (rule bexI[of _ "Write op1' p x"])
     apply simp_all
    done
   apply simp
  apply auto
  done

lemma step_comp_op_inv_step_comp_op_assoc_inv2:
  "step_comp_op_inv Some io op buf2 op2 op3 \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   \<exists>op1' op2' op3' buf2'.
   step_comp_op_assoc_inv (Out (Inr (projr p)) x) op1 buf op2 buf2 op3 op1 buf op2' buf2' op3' \<and>
   comp_op Some buf op1 (map_op projl projr op) = comp_op Some buf op1 (map_op projl projr (comp_op Some buf2' op2' op3'))"
  apply (induct op buf2 op2 op3 arbitrary: rule: step_comp_op_inv.induct)
       apply fast
    apply (force intro: step_comp_op_assoc_inv.intros)
    apply (force intro: step_comp_op_assoc_inv.intros)
    apply (force intro: step_comp_op_assoc_inv.intros)
  subgoal for op q xa bufa op1' op2 op1a p'
    apply auto
    subgoal for op2' op3' buf2'
    apply hypsubst_thin
    apply (intro conjI[rotated] exI)
    apply (rule refl)
    apply (rule step_comp_op_assoc_inv.intros(5)[of _ _ _ _ _ _ _ _ _ op1])
       apply fast+
      done
    done
    apply (force intro: step_comp_op_assoc_inv.intros)
  done

lemma step_csubset_eq:
  "step op' io op'' \<Longrightarrow>
   csubset_eq (choices op') (choices op) \<Longrightarrow>
   step op io op''"
  apply (induct op' io op'' arbitrary: op rule: step.induct)
  apply (simp_all add: cUN_csubset_iff Write_in_choices_step Read_in_choices_step)
  done

lemma step_Choice_csubset_eq:
  "step (Choice ops') io op'' \<Longrightarrow>
   csubset_eq ops' ops \<Longrightarrow>
   step (Choice ops) io op''"
  apply (induct "Choice ops'" io op'' arbitrary: ops' ops rule: step.induct)
  apply (simp_all add: cUN_csubset_iff Write_in_choices_step Read_in_choices_step)
  apply (metis cin.rep_eq cinsert_absorb cinsert_csubset step.intros(3))
  done

lemma csubset_eq_comp_op_benq:
  "Write op1' p x |\<in>| choices op1 \<Longrightarrow>
   csubset_eq (choices (comp_op Some (buf(p := bulk_benq [x] (buf p))) op1' op2)) (choices (comp_op Some buf op1 op2))"
  apply (subst (2) comp_op_code)
  apply (simp flip: choices_map_op)
  apply (rule semilattice_sup_class.le_supI1)
  apply (metis (mono_tags, lifting) cUN_upper cimage.rep_eq cin.rep_eq image_eqI op.simps(11))
  done

lemma
  "csubset_eq (choices op1') (choices op1) \<Longrightarrow>
   csubset_eq (choices (map_op projl projr (comp_op Some buf op1' op2))) (choices (map_op projl projr (comp_op Some buf op1 op2)))"
  apply (cases "choices op1' = cempty")
  subgoal
    apply auto
  apply (subst (asm) comp_op_code)
    apply auto
    subgoal for op op'
      apply (cases op'; simp add: ranI Set.filter_def)
      subgoal for p f
  apply (subst comp_op_code)
    apply (simp add: ranI Set.filter_def)
    apply (rule disjI2)
        apply hypsubst_thin
        apply (rule exI[of _ "Read p f"])
        apply (simp add: ranI)
        oops

lemma
  "csubset_eq (choices op1') (choices op1) \<Longrightarrow>
   csubset_eq (un_Choice (map_op projl projr (comp_op Some buf op1' op2))) (un_Choice (map_op projl projr (comp_op Some buf op1 op2)))"
 apply (cases "choices op1' = cempty")
  subgoal
    apply auto
  apply (subst (asm) comp_op_code)
    apply auto
    subgoal for op'
      apply (cases op'; simp add: ranI Set.filter_def)
      subgoal for p f
  apply (subst (1 2) comp_op_code)
    apply (simp add: ranI Set.filter_def)
        apply hypsubst_thin
        oops
  
lemma step_comp_op_csubset_eq:
  "step (comp_op Some buf op1 op2) io op'' \<Longrightarrow>
   csubset_eq (un_Choice (comp_op Some buf op1 op2)) (un_Choice (comp_op Some buf' op1' op2')) \<Longrightarrow>
   step (comp_op Some buf' op1' op2') io op''"
  apply (subst comp_op_code)
   apply (subst (asm) (1 2 3) comp_op_code)
  apply (rule step_Choice_csubset_eq)
   apply simp_all
  apply blast
  done

coinductive silent_steps where
  "csubset_eq (choices op2) (choices op1) \<Longrightarrow> silent_steps op1 op2"
| "silent_steps op op' \<Longrightarrow> silent_steps (Write op p x) (Write op' p x)"

lemma Write_op1_silet_steps:
  "Write op1' p x |\<in>| choices op1 \<Longrightarrow>
   silent_steps (comp_op Some buf op1 op2) (comp_op Some (buf(p := bulk_benq [x] (buf p))) op1' op2)"
  by (rule silent_steps.intros(1)) (erule csubset_eq_comp_op_benq)

(*
lemma silent_steps_step:
  "silent_steps op1 op2 \<Longrightarrow>
   step op2 io op3 \<Longrightarrow>
   step op1 io op3"
  by (induct op1 op2 arbitrary: rule: silent_steps.induct)
    (auto simp flip: cin.rep_eq intro: step.intros)
*)
(*
lemma silent_steps_choices:
  "silent_steps op1 op2 \<Longrightarrow>
   csubset_eq (choices op2) (choices op1)"
  by (induct op1 op2 arbitrary: rule: silent_steps.induct) auto
*)
lemma silent_steps_trans:
  "silent_steps op1 op2 \<Longrightarrow>
   silent_steps op2 op3 \<Longrightarrow>
   silent_steps op1 op3"
  apply (coinduction arbitrary: op1 op2 op3 rule: silent_steps.coinduct)
  apply (erule silent_steps.cases)+
    apply auto[1]
  subgoal for op1 op2 op3 op2a op1a op op' p x
    apply hypsubst_thin
    apply simp
    oops

lemma
  "step (comp_op Some buf op1' op2) io op \<Longrightarrow>
   silent_steps op1 op1' \<Longrightarrow>
   step (comp_op Some buf op1 op2) io op"
  oops
(*
lemma choices_cempty_silent_steps:
  "choices op = {||} \<Longrightarrow>
   silent_steps op op' \<Longrightarrow>
   choices op' =  {||}"
  using silent_steps_choices by auto
*)
lemma
  "step op2 io op3 \<Longrightarrow>
   silent_steps op1 op3"
  oops
(* 
lemma
  "silent_steps op1 op1' \<Longrightarrow>
   silent_steps (comp_op Some buf op1 op2) (comp_op Some buf op1' op2)"
  apply (induct op1 op1' arbitrary: op2 buf rule: silent_steps.induct)
   apply (auto intro: silent_steps.intros)
  subgoal for op' ops op op2 buf
    apply (rule silent_steps_trans[rotated])
    apply assumption
      apply (subst (1) comp_op_code)
    apply simp
    apply (rule silent_steps.intros(3)[rotated])
      apply (subst (1) comp_op_code)
     apply (rule silent_steps.intros(1))
    apply (auto)
    apply (meson UN_iff image_eqI silent_steps.intros(1))
    apply (auto simp add: ranI Set.filter_def split: op.splits)
    subgoal sorry

     apply (rule exI)
    apply (intro conjI)
      apply (rule disjI2)
      apply (rule imageI[of "Write _ _ _"])
    apply (rule CollectI)
      apply (intro conjI allI impI)
         apply simp
    apply simp
      apply blast
      apply simp
    apply (simp add: ranI)
    apply (rule silent_steps.intros(4))
    sledgehammer

    oops
 *)

lemma
  "choices_set op1' op1 \<Longrightarrow>
   step op2 (Out p x) op2' \<Longrightarrow>
   step (comp_op Some buf op1 op2) (Out (Inr p) x) (comp_op Some buf op1' op2')"
  apply (induct op1' op1 arbitrary: op2 op2' buf rule: choices_set.induct)
  oops

inductive choices_comp_op for wire where
  "Read p f |\<in>| choices op1 \<Longrightarrow> choices_comp_op wire (Read (Inl p) (\<lambda>x. comp_op wire buf (f x) op2)) buf op1 op2"
| "Write op p x |\<in>| choices op2 \<Longrightarrow> choices_comp_op wire (Write (comp_op wire buf op1 op) (Inr p) x) buf op1 op2"
| "Write op p x |\<in>| choices op1 \<Longrightarrow> p \<notin> dom wire \<Longrightarrow> choices_comp_op wire (Write (comp_op wire buf op op2) (Inl p) x) buf op1 op2"
| "Read p f |\<in>| choices op2 \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> choices_comp_op wire (Read (Inr p) (\<lambda>x. comp_op wire buf op1 (f x))) buf op1 op2"
| "Write op' p x |\<in>| choices op1 \<Longrightarrow> wire p = Some q \<Longrightarrow> choices_comp_op wire op (BENQ q x buf) op' op2 \<Longrightarrow> choices_comp_op wire op buf op1 op2"
| "Read p f |\<in>| choices op2 \<Longrightarrow> p \<in> ran wire \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> choices_comp_op wire op (BTL p buf) op1 (f (BHD p buf)) \<Longrightarrow> choices_comp_op wire op buf op1 op2"

lemma choices_comp_op: "op' |\<in>| choices (comp_op wire buf op1 op2) \<longleftrightarrow> choices_comp_op wire op' buf op1 op2"
  apply (rule iffI)
  subgoal
    unfolding choices_def
    apply safe
    apply (erule thin_rl)
    subgoal for n
      apply (induct n arbitrary: buf op1 op2)
      apply (subst (asm) comp_op_code; simp)
      apply (subst (asm) (2) comp_op_code; auto)
      subgoal for n buf op1 op2 x
        apply (cases x)
          apply (auto intro: choices_comp_op.intros split: option.splits)
        done
      subgoal for n buf op1 op2 x
        apply (cases x)
          apply (auto intro: choices_comp_op.intros split: if_splits option.splits)
        done
      done
    done
  apply (induct op' buf op1 op2 pred: choices_comp_op)
  apply (subst (2) comp_op_code; auto simp: Set.filter_def split: op.splits)
  apply (subst (2) comp_op_code; auto simp: Set.filter_def split: op.splits)
     apply (subst (2) comp_op_code; auto simp: Set.filter_def ranI is_Choice_def split: op.splits)
  using is_Choice_def apply force
     apply (subst (2) comp_op_code; auto simp: Set.filter_def ranI is_Choice_def split: op.splits)
   apply (subst comp_op_code; auto simp: Set.filter_def ranI is_Choice_def simp del: fun_upd_apply split: op.splits option.splits)
  using domIff apply fastforce
  apply (subst comp_op_code; auto simp: Set.filter_def ranI is_Choice_def simp del: fun_upd_apply split: op.splits option.splits)
  done

lemma comp_op_not_Read_Write[simp]:
  "\<not> is_Read (comp_op Some buf op1 op2)"
  "\<not> is_Write (comp_op Some buf op1 op2)"
  oops

lemma
  "step (comp_op Some buf op1 op2) l s \<Longrightarrow>
   \<exists> buf' op1' op2' x. s = comp_op Some buf' op1' op2' \<and>
   step (Choice (cUn (cimage (\<lambda>op1. comp_op Some buf op1 op2) (choices op1)) (cimage (comp_op Some buf op1) (choices op2)))) l x \<and>
   x |\<in>| cUn (cimage (\<lambda>op1. comp_op Some buf' op1 op2) (choices op1')) (cimage (comp_op Some buf' op1) (choices op2'))"
  oops


lemma op_bisim_choices:
  "op ~ Choice (choices op)"
  apply (coinduction arbitrary: op rule: bisim_coinduct_upto)
  subgoal for op
    unfolding sim_def
    apply (intro conjI impI allI)
    subgoal for l s
      by (metis (no_types, lifting) bc_refl step.simps step_choicesE)
    subgoal
      by (smt (verit) IO.inject(1) IO.simps(4) Read_in_choices_step Write_in_choices_step bc_refl choices_to_inductive cin.rep_eq no_Choice_in_choices op.inject(3) op.simps(7) op.simps(9) step.cases)
    done
  done

abbreviation "cant_step op io \<equiv> \<not> (\<exists> op'. step op io op')"

inductive not_bisim where
  "step op1 io op' \<Longrightarrow> cant_step op2 io \<Longrightarrow> not_bisim op1 op2"
| "step op2 io op' \<Longrightarrow> cant_step op1 io \<Longrightarrow> not_bisim op1 op2"
| "(\<And>op1' op2' io. step op1 io op1' \<and> step op2 io op2' \<and> not_bisim op1' op2') \<Longrightarrow> not_bisim op1 op2"


lemma not_bisimI:
  "not_bisim op1 op2 \<Longrightarrow> \<not> op1 ~ op2"
  apply (induct op1 op2 pred: not_bisim)
    subgoal
      apply safe
      apply (erule bisim.cases)
      unfolding sim_def
      apply force
      done
    subgoal
      apply safe
      apply (erule bisim.cases)
      unfolding sim_def
      apply force
      done
    subgoal for op1 op2
      apply safe
      apply (cases "\<exists> io op1'. step op1 io op1'")
      subgoal
        apply safe
      apply (erule bisim.cases)
      unfolding sim_def
      apply hypsubst_thin
      apply fast
      done
    subgoal
      by auto
    done
  done


corec may_end where
  "may_end = choice2 (Read (1::1) (\<lambda> _. end_op)) (Write end_op (1::1) (1::nat))"

lemma may_end_code:
  "may_end = Choice {| Read (1::1) (\<lambda> _. end_op), Write end_op (1::1) (1::nat) |}"
  apply (subst may_end.code)
  apply simp
  done

lemma choices_may_end[simp]:
  "choices may_end = {|Read (1::1) (\<lambda> _. end_op), Write end_op (1::1) (1::nat)|}"
  apply (subst may_end_code)
  apply auto
  done

lemma choices_comp_op_mayend[simp]:
  "choices (comp_op Some (\<lambda> _. []) may_end may_end) = 
   cUn {| Read (Inl 1) (\<lambda>x. comp_op Some (\<lambda>_. []) \<oslash> may_end), Write (comp_op Some (\<lambda>_. []) may_end end_op) (Inr 1) (Suc 0)|}
  (choices (comp_op Some ((\<lambda>_. [])(1 := [Suc 0])) end_op may_end))"
  apply (subst comp_op_code)
  apply (force simp add: ranI Set.filter_def)
  done

lemma
  "step (map_op projl projr (comp_op Some buf1 (map_op projl projr (comp_op Some buf2 may_end end_op)) may_end)) io op \<Longrightarrow>
   io = Out 1 1 \<Longrightarrow>
   op = map_op projl projr (comp_op Some buf1 (map_op projl projr (comp_op Some buf2 may_end end_op)) end_op)"
  apply (induct "map_op projl projr (comp_op Some buf1 (map_op projl projr (comp_op Some buf2 may_end end_op)) may_end)" io op arbitrary: buf1 buf2 pred: step)
    apply simp_all
   apply (subst (asm) (2) comp_op_code, simp)
  apply (subst (asm) (6) comp_op_code)
  apply (auto simp flip: choices_map_op split: op.splits)
  oops

lemma step_bisim:
  "step op1 io op1' \<Longrightarrow>
   op1 ~ op2 \<Longrightarrow>
   \<exists> op2'. step op2 io op2' \<and> op1' ~ op2'"
  apply (induct op1 io op1' arbitrary: op2 pred: step)
  subgoal
    apply (erule bisim.cases)
    apply auto
    done
  subgoal
    apply (erule bisim.cases)
    apply auto
    done
  subgoal
    apply (erule bisim.cases)
    apply (auto 10 10 elim: simE)
    done
  done

inductive choice_steps where
  "\<not> is_Choice op \<Longrightarrow> choice_steps op op"
| "op' |\<in>| ops \<Longrightarrow> choice_steps op' op \<Longrightarrow> choice_steps (Choice ops) op"

inductive io_step where
  "io_step (Read p f) (Inp p x) (f x)"
| "io_step (Write op q x) (Out q x) op"

lemma step_choice_steps_io_step:
  "step op io op' \<Longrightarrow> \<exists> op''. choice_steps op op'' \<and> io_step op'' io op'"
  by (induct op io op' pred: step) (auto 10 10 intro: choice_steps.intros io_step.intros)

lemma step_step_choice_steps_io:
  "choice_steps op op'' \<Longrightarrow> io_step op'' io op' \<Longrightarrow> step op io op'"
  by (induct op op'' arbitrary: op' pred: choice_steps) (auto 10 10 intro: step.intros io_step.intros elim: io_step.cases)

lemma choice_steps_choices:
  "choice_steps op op' \<longleftrightarrow>  op' |\<in>| choices op"
  apply safe
  subgoal
  apply (induct op op' pred: choice_steps)
  apply (metis choices_set.simps choices_to_inductive is_Choice_def op.exhaust)
  apply auto
    done
  subgoal 
    unfolding choices_def
    apply safe
    subgoal premises prems for n
      using prems(2-) apply -
      apply (induct n arbitrary: op)
      subgoal for op
        apply (cases op)
      apply (auto intro: choice_steps.intros)
        done
      subgoal for n op
        apply (cases op)
          apply (auto intro: choice_steps.intros)
        done
      done
    done
  done

lemma Collect_choice_steps_countable[simp]:
  "countable {op'. choice_steps op op'}"
  apply (simp add: choice_steps_choices)
  done

lemma choices_choice_steps:
  "choices op = cset.acset {op'. choice_steps op op'}"
  apply (simp add: choice_steps_choices)
  done

lemma bisim_choices_bisim:
  "op1 ~ op2 \<Longrightarrow>
   rel_cset bisim (choices op1) (choices op2)"
  unfolding choices_def rel_set_def
  apply auto
  apply (rule rel_setI)
   apply auto
  subgoal premises prems for op n
    using prems(1,3) apply -
    apply (induct n arbitrary: op1 op2)
    subgoal for op1 op2
      oops

lemma sorried:
  "step (comp_op wire buf op1 op2) io op \<Longrightarrow>
   op1 ~ op1' \<Longrightarrow>
   \<exists> op1'' op2' buf'. op = comp_op wire buf' op1'' op2' \<and>
   step (comp_op wire buf op1' op2) io (comp_op wire buf op1' op2)"
  apply (induct "comp_op wire buf op1 op2" io op arbitrary: buf op1 op2 op1' pred: step)
    apply (subst (asm) comp_op_code, simp)
  apply (subst (asm) comp_op_code, simp)
  subgoal for op ops l op' buf op1 op2 op1'
    apply auto
    apply (subst (asm) (3) comp_op_code)
    apply (simp add: Set.filter_def ranI image_iff bex_Un)
    oops


lemma bisim_Read_Choice[simp]:
  "bisim (Read p f) (Choice ops) \<longleftrightarrow> ((\<forall>op. op |\<in>| ops \<longrightarrow> bisim (Read p f) op) \<and> ops \<noteq> cempty)"
  apply (safe intro!: context_conjI)
  subgoal for op
    apply (cases op)
    subgoal
        apply (erule bisim.cases)
      apply simp
      apply (rule bisim.intros)
          unfolding sim_def
      apply auto
          subgoal for x
      apply (drule spec2)
      apply (drule mp)
       apply (rule step.intros(1)[of _ _ x])
      apply safe
      apply (drule spec2)
      apply (drule mp)
       apply (rule step.intros(3)[rotated])
        apply assumption
       apply simp
      apply safe
      apply (intro conjI[rotated] exI)
             apply assumption
            oops

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
      apply (induct "comp_op wire buf op1 op2" io op arbitrary: buf op1 op2 op1' op2' pred: step)
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
                 apply (rule step.intros(3))
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
               apply (rule step.intros(3))
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI1)
                apply (erule bexI[rotated])
                apply simp
               apply (rule step.intros(2))
              apply (metis (mono_tags, lifting) bc_base)
              done
            subgoal for q
              apply (drule bisim_choices_Write)
               apply simp
              apply safe
              apply hypsubst_thin
              apply (drule meta_spec)+
              apply (drule meta_mp)
               apply (rule refl)
              apply (drule meta_mp)
               apply assumption
              apply (drule meta_mp)
               apply assumption
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule step.intros(3))
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI1)
                apply (erule bexI[rotated])
                apply simp
               apply assumption+
              done
            done
          subgoal
            by force
          done
        subgoal for op
          apply (cases op)
          subgoal for p f
            apply (simp add: Set.filter_def ranI image_iff bex_Un split: if_splits)
            subgoal
              apply (drule bisim_choices_Read[simplified, where x="BHD p buf"], assumption)
              apply safe
              apply hypsubst_thin
              apply (drule meta_spec)+
              apply (drule meta_mp)
               apply (rule refl)
              apply (drule meta_mp)
               apply assumption
              apply (drule meta_mp)
               apply assumption
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule step.intros(3))
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI2)
                apply (intro conjI exI)
                  apply assumption
                 apply simp_all
              done
            subgoal
              apply hypsubst_thin
              apply auto
              subgoal for x
                apply (drule bisim_choices_Read[simplified, where x="x"], assumption)
                apply safe
                apply hypsubst_thin
                apply (intro conjI exI)
                 apply (subst comp_op_code)
                 apply simp
                 apply (rule step.intros(3))
                  apply (simp add: Set.filter_def ranI image_iff bex_Un)
                  apply (rule disjI2)
                  apply (intro conjI exI)
                    apply assumption
                   apply simp_all
                 apply (rule step.intros(1))
                apply (rule bc_base)
                apply (intro exI conjI)
                   apply simp_all
                done
              done
            done
          subgoal 
            apply auto
            apply hypsubst_thin
            apply (drule bisim_choices_Write[of op2])
             apply simp
            apply safe
            apply (intro conjI exI)
             apply (subst comp_op_code)
             apply simp
             apply (rule step.intros(3))
              apply (simp add: Set.filter_def ranI image_iff bex_Un)
              apply (rule disjI2)
              apply (intro conjI exI)
                apply assumption
               apply simp_all
             apply (rule step.intros(2))
            apply (metis (mono_tags, lifting) bc_base)
            done
          subgoal
            by fast
          done
        done
      done
    subgoal for io op
      apply (rotate_tac 2)
      apply (induct "comp_op wire buf op1' op2'" io op arbitrary: buf op1 op2 op1' op2' pred: step)
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
                 apply (rule step.intros(3))
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
               apply (rule step.intros(3))
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI1)
                apply (erule bexI[rotated])
                apply simp
               apply (rule step.intros(2))
              apply (smt (verit, ccfv_threshold) bc_base bisim_sym)
              done
            subgoal for q
              apply (subst (asm) (5) bisim_sym)
              apply (drule bisim_choices_Write)
               apply simp
              apply safe
              apply hypsubst_thin
              apply (drule meta_spec)+
              apply (drule meta_mp)
               apply (rule refl)
              apply (drule meta_mp)
               apply (subst bisim_sym)
               apply assumption
              apply (drule meta_mp)
               apply assumption
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule step.intros(3))
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI1)
                apply (erule bexI[rotated])
                apply simp
               apply assumption+
              done
            done
          subgoal
            by force
          done
        subgoal for op
          apply (cases op)
          subgoal for p f
            apply (simp add: Set.filter_def ranI image_iff bex_Un split: if_splits)
            subgoal
              apply (subst (asm) (6) bisim_sym)
              apply (drule bisim_choices_Read[simplified, where x="BHD p buf"], assumption)
              apply safe
              apply hypsubst_thin
              apply (drule meta_spec)+
              apply (drule meta_mp)
               apply (rule refl)
              apply (drule meta_mp)
               apply assumption
              apply (drule meta_mp)
               apply (subst bisim_sym)
               apply assumption
              apply safe
              apply (intro conjI exI)
               apply (subst comp_op_code)
               apply simp
               apply (rule step.intros(3))
                apply (simp add: Set.filter_def ranI image_iff bex_Un)
                apply (rule disjI2)
                apply (intro conjI exI)
                  apply assumption
                 apply simp_all
              done
            subgoal
              apply hypsubst_thin
              apply auto
              subgoal for x
                apply (subst (asm) (6) bisim_sym)
                apply (drule bisim_choices_Read[simplified, where x="x"], assumption)
                apply safe
                apply hypsubst_thin
                apply (intro conjI exI)
                 apply (subst comp_op_code)
                 apply simp
                 apply (rule step.intros(3))
                  apply (simp add: Set.filter_def ranI image_iff bex_Un)
                  apply (rule disjI2)
                  apply (intro conjI exI)
                    apply assumption
                   apply simp_all
                 apply (rule step.intros(1))
                apply (smt (verit, ccfv_threshold) bc_base bisim_sym)
                done
              done
            done
          subgoal 
            apply auto
            apply hypsubst_thin
            apply (subst (asm) (6) bisim_sym)
            apply (drule bisim_choices_Write[of op2'])
             apply simp
            apply safe
            apply (intro conjI exI)
             apply (subst comp_op_code)
             apply simp
             apply (rule step.intros(3))
              apply (simp add: Set.filter_def ranI image_iff bex_Un)
              apply (rule disjI2)
              apply (intro conjI exI)
                apply assumption
               apply simp_all
             apply (rule step.intros(2))
            apply (smt (verit, ccfv_threshold) bc_base bisim_sym)
            done
          subgoal
            by fast
          done
        done
      done
    done
  done

lemma step_comp_op_end_op_W:
  "step op' io op \<Longrightarrow>
   op' = map_op projl projr (comp_op Some buf W W) \<Longrightarrow>
   io = Out 1 42 \<and> (\<exists> buf'. op = (map_op projl projr (comp_op Some buf' W W)))"
  apply (induct op' io op arbitrary: buf pred: step)
  apply (subst (asm) comp_op_code, simp)
  apply (subst (asm) comp_op_code, simp)
  subgoal for op ops l op'
    apply (subst (asm) (3) comp_op_code)
    apply auto
    done
  done

lemma
  "map_op projl projr (comp_op Some buf W W) ~ W"
  unfolding scomp_op_def
  apply (coinduction arbitrary: buf rule: bisim_coinduct_upto)
  unfolding sim_def
  apply (intro conjI allI impI)
  subgoal for io op
    apply (drule step_comp_op_end_op_W)
     apply auto
    apply (intro conjI exI)
     apply (subst W.code)
     apply (rule step.intros(2))
    apply (rule bc_base)
    apply auto
    done
  oops

inductive tau_steps where
  "tau_steps op op"
| "tau_steps op' op \<Longrightarrow> op' |\<in>| ops \<Longrightarrow> tau_steps (Choice ops) op"

lemma tau_steps_step:
  "tau_steps op2 op1 \<Longrightarrow> 
   step op1 io op \<Longrightarrow>
   step op2 io op"
  apply (induct op2 op1 pred: tau_steps)
  subgoal
    by fast
  subgoal for op' opa ops
    using step.intros(3) by blast
  done

declare cin.rep_eq[simp del] cin.rep_eq[symmetric, simp]

lemma no_Choice_in_choices[simplified, simp, dest!]: "Choice ops |\<in>| choices op \<Longrightarrow> False"
  unfolding cin.rep_eq by blast


abbreviation "op_aCb_c \<equiv> Write (Choice {|Write end_op 1 (42::nat), Write end_op 1 43|}) 1 44"
abbreviation "op_Cab_ac \<equiv> Choice {|Write (Write end_op 1 42) 1 44, Write (Write end_op 1 43) 1 44|}"

lemma
  "op_aCb_c ~ op_Cab_ac \<Longrightarrow> False"
  apply (erule bisim.cases)
  unfolding sim_def
  apply auto
  apply (drule spec2)
  apply (drule mp)
   apply (rule step.intros(2))
  apply (drule spec2)
  apply (drule mp)
   apply (rule step.intros(3))
    apply (rule cinsertI1)
   apply (rule step.intros(2))
  apply auto
  subgoal
    apply (erule bisim.cases)
    unfolding sim_def
    apply auto
    apply (drule spec2)
    apply (drule mp)
     apply (rule step.intros(3))
      apply (rule cinsertI2)
      apply (rule cinsertI1)
     apply (rule step.intros(2))
    apply (drule spec2)
    apply (drule mp)
     apply (rule step.intros(2))
    apply auto
    done
  subgoal
    apply (erule bisim.cases)
    unfolding sim_def
    apply auto
    apply (drule spec2)
    apply (drule mp)
     apply (rule step.intros(3))
      apply (rule cinsertI1)
     apply (rule step.intros(2))
    apply (drule spec2)
    apply (drule mp)
     apply (rule step.intros(2))
    apply auto
    done
  done

lemma step_comp_op_inv_end_op_op_aCb_c:
  "step_comp_op_inv Some io op buf op1 op2 \<Longrightarrow>
   op1 = end_op \<Longrightarrow>
   op2 = op_aCb_c \<Longrightarrow>
   io = Out (Inr 1) 44 \<and> op = comp_op Some buf \<oslash> (Choice {|Write \<oslash> 1 42, Write \<oslash> 1 43|})"
  apply (induct buf op1 op2 pred: step_comp_op_inv)
       apply simp_all
  subgoal
    apply (subst comp_op_code)
    apply auto
    done
  subgoal
    by auto
  subgoal for op p buf op1 op2' x op2
    apply auto
    done
  done

lemma step_map_op_end_op_op_aCb_c:
  "step (map_op projl projr (comp_op Some buf \<oslash> op_aCb_c)) io op \<Longrightarrow>
   io = Out 1 44 \<and> op = map_op projl projr (comp_op Some buf \<oslash> (Choice {|Write \<oslash> 1 42, Write \<oslash> 1 43|}))"
  apply (drule step_map_op_inv)
  apply (elim exE conjE)
  apply (drule step_step_comp_op_inv)
  apply (drule step_comp_op_inv_end_op_op_aCb_c)
    apply simp_all
  done

lemma
  "map_op projl projr (comp_op Some buf \<oslash> op_aCb_c) ~ map_op projl projr (comp_op Some buf \<oslash> op_Cab_ac)"
  unfolding scomp_op_def
  apply (coinduction arbitrary: buf rule: bisim_coinduct_upto)
  subgoal for buf
    unfolding sim_def
    apply (intro allI conjI impI)
    subgoal for io op
      apply (drule step_map_op_end_op_op_aCb_c)
      apply (elim conjE)
      apply hypsubst_thin
      apply (intro conjI exI)
       apply (subst comp_op_code)
       apply simp
      apply (rule step.intros(3)[rotated])
      apply (rule step.intros(2))
      defer
       apply (rule bc_base)
       apply (intro conjI exI)
      defer
      apply (rule refl)
        oops


  find_theorems Choice bisim

(*


coinductive simulates where
  "sim simulates s t \<Longrightarrow> simulates s t"

lemma "simulates op_aCb_c op_Cab_ac"
  apply (coinduction)
  apply auto
  apply (rule exI conjI)+
   apply (rule step.intros)
  apply (rule cinsertI1)
   apply (rule step.intros)
  apply (rule simulates.intros)
  apply (simp add: sim_def)
  oops

lemma "bisim_cong R s t \<Longrightarrow> bisim_cong (\<lambda>s t. R s t \<and> R t s) s t"
  apply (induct s t rule: bisim_cong.induct)
  sledgehammer

lemma "simulates s t \<Longrightarrow> simulates t s \<Longrightarrow> s ~ t"
  apply (coinduction arbitrary: s t rule: bisim_coinduct_upto)
  apply auto
*)

lemma 
  "step (map_op projl projr (comp_op Some (buf :: 'd \<Rightarrow> 'c buf) op1' op2)) io (map_op projl projr (comp_op Some (buf' :: 'd \<Rightarrow> 'c buf) op1'' op2')) \<Longrightarrow>
   refines op1 op1' \<Longrightarrow>
   \<exists> (buf'' :: 'd \<Rightarrow> 'c buf) op1''' op2''. step (map_op projl projr (comp_op Some buf op1 op2)) io (map_op projl projr (comp_op Some buf'' op1''' op2'')) \<and>
   map_op projl projr (comp_op Some buf'' op1''' op2'') = map_op projl projr (comp_op Some buf' op1'' op2')"
  apply (induct "map_op projl projr (comp_op Some buf op1' op2)" io "map_op projl projr (comp_op Some buf' op1'' op2')" arbitrary: op1' op1 op2 buf buf' op1'' op2' rule: step.induct)
  subgoal
    apply (subst (asm) comp_op_code)
    apply simp
    done
  subgoal
    apply (subst (asm) (2) comp_op_code)
    apply simp
    done
  subgoal for op ops l op' op1' op2 buf op1
    apply (subst (asm) (9) comp_op_code)
    apply (simp flip:  add:  Set.filter_def ranI image_iff bex_Un)
    oops

lemma a[simp]:
  "choices (Write end_op 1 1) =  {|Write end_op 1 1 |}"
  by simp

lemma comp_op_end_op_end_op[simp]:
  "comp_op wire buf end_op end_op = end_op"
  apply (coinduction arbitrary: buf)
  apply (auto intro: rel_setI)
  done

lemma bisim_rewrite_step:
  "op1 ~ op1' \<Longrightarrow>
   \<exists> op2'. step op1 io op2 = step op1' io op2' \<and> op2' ~ op2"
  oops

lemma map_IO_projl_projr[simp]:
  "map_IO projl projr id (map_IO Inl Inr id io) = io"
  by (smt (verit, ccfv_SIG) IO.exhaust IO.simps(10) IO.simps(9) id_def sum.sel(1) sum.sel(2))


lemma
  "step_comp_op_inv Some io op buf op1' op2 \<Longrightarrow>
   csubset_eq (choices op1') (choices op1) \<Longrightarrow>
   step_comp_op_inv Some io op buf op1 op2"
  apply (induct op buf op1' op2 arbitrary: op1 rule: step_comp_op_inv.induct)
  subgoal for op1 p x op1' buf op2 op1''
    apply simp
    apply (rule step_comp_op_inv.intros(1))
     apply (drule step_csubset_eq)
      apply assumption+
    apply simp
    done
  subgoal for op2 p x op2' buf op1 op1''
    apply simp
    apply hypsubst_thin
    oops


lemma cin_cfilter[simp]:
  "x |\<in>| cfilter P A \<longleftrightarrow> x |\<in>| A \<and> P x"
  by (metis cfilter.rep_eq cin.rep_eq member_filter)

lemma cUnion_cempty[simp]:
  "cUnion {||} = {||}"
  using cUN_empty by auto

lemma cfilter_cempty[simp]:
  "cfilter P {||} = {||}"
  by auto


corec cp_once :: "(1, 1, 'd) op" where
  "cp_once = Read 1 (Write end_op 1)"

abbreviation "read_or_write \<equiv> Choice {| Read (1::2) (\<lambda> _. end_op), Write (Read (2::2) (\<lambda> _. end_op)) (1::1) (1::nat) |}"

lemma choices_read_or_write[simp]:
  "choices read_or_write = {| Read (1::2) (\<lambda> _. end_op), Write (Read (2::2) (\<lambda> _. end_op)) (1::1) (1::nat) |}"
  by (auto simp del: cimage_cinsert)

lemma cUnion_cinsert[simp]:
  "cUnion (cinsert x A) = cUn x (cUnion A)"
  apply (subst (3 8) cset.map_id[symmetric])
  apply fastforce
  done

lemma assoc_counter_example:
  "read_or_write \<bullet> ((end_op :: (1, 1, nat) op) \<bullet> (Write end_op (1::1) 1)) ~ read_or_write \<bullet> (end_op :: (1, 1, nat) op) \<bullet> (Write end_op (1::1) 1) \<Longrightarrow> False"
  apply (erule bisim.cases)
  apply simp
  apply hypsubst_thin
  unfolding sim_def scomp_op_def
  apply (drule spec2)
  apply (drule mp)
   apply (rule step_map_op)
   apply (subst comp_op_code)
   apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (rule cimageI)
    apply (simp (no_asm) only: choices_Choice)
    apply (rule cUN_I)
     apply (rule cinsertI2)
     apply (rule cinsertI1)
    apply simp
   apply (simp (no_asm) only: op.case option.case)
  apply (rule step_comp_op_R)
   apply (rule step_map_op)
  apply (rule step_comp_op_R)
    apply (rule step.intros(2))
    apply simp
   apply simp
  apply (erule thin_rl)
  apply (elim exE conjE)
  apply (subst (asm) (2) comp_op_code)
  apply (erule step_choicesE)
  subgoal
    apply simp
    done
  subgoal
    apply (auto simp del: cimage_cinsert simp add:  ranI split: op.splits)
    apply hypsubst_thin
    apply (simp add: comp_def cimage_cUnion)
    apply (erule bisim.cases)
    apply hypsubst_thin
    apply (erule thin_rl)
    unfolding sim_def
    apply (drule spec2)
    apply (drule mp)
    apply (rule step.intros(3))
      apply (rule cinsertI1)
    apply (rule step.intros(1))
    apply auto
    done
  done


end


lemma
  "step (map_op projl projr (comp_op Some (buf1 :: 'd \<Rightarrow> 'c buf) op1 (map_op projl projr (comp_op Some (buf2 :: 'e \<Rightarrow> 'c buf) op2 op3)))) io op \<Longrightarrow>
   \<exists> op1' op2' op3' (buf1' :: 'd \<Rightarrow> 'c buf) (buf2' :: 'e \<Rightarrow> 'c buf).
     step (map_op projl projr (comp_op Some buf2 (map_op projl projr (comp_op Some buf1 op1 op2)) op3)) io 
          (map_op projl projr (comp_op Some buf2' (map_op projl projr (comp_op Some buf1' op1' op2')) op3')) \<and>
    op = map_op projl projr (comp_op Some buf1' op1' (map_op projl projr (comp_op Some buf2' op2' op3')))"
  apply (induct "map_op projl projr (comp_op Some buf1 op1 (map_op projl projr (comp_op Some buf2 op2 op3)))" io op arbitrary: buf1 buf2 op1 op2 op3 rule: step.induct)
  subgoal
    apply (subst (asm) comp_op_code)
    apply simp
    done
  subgoal
    apply (subst (asm) comp_op_code)
    apply simp
    done
  subgoal premises prems for op ops l op' buf1 buf2 op1 op2 op3
    using prems(1,2,4) apply -
    apply (subst (asm) comp_op_code)
    apply (subst (asm) (10) comp_op_code)
    apply (auto simp add: Set.filter_def ranI image_iff bex_Un)
    subgoal for op''
      apply (cases op'')
      subgoal
        apply simp
        sorry
      subgoal for op1' p x
        apply simp
        apply (drule prems(3))
        apply hypsubst_thin
        apply (elim exE conjE)
        apply (intro conjI[rotated] exI)
         apply simp
        apply hypsubst_thin
        oops

lemma scomp_op_assoc:
  "map_op projl projr (comp_op Some (\<lambda> _. []) cp_op (map_op projl projr (comp_op Some (\<lambda> _. [1]) cp_op cp_op))) ~
   map_op projl projr (comp_op Some (\<lambda> _. [1]) (map_op projl projr (comp_op Some (\<lambda> _. []) cp_op cp_op)) cp_op)"
  apply (coinduction rule: bisim_coinduct_upto)
    unfolding sim_def
  apply (intro conjI allI impI)
  subgoal for io op
    oops


lemma scomp_op_assoc:
  "map_op projl projr (comp_op Some buf1 (op1 :: (1, 1, nat) op) (map_op projl projr (comp_op Some buf2 (op2 :: (1, 1, nat) op) (op3 :: (1, 1, nat) op)))) ~
   map_op projl projr (comp_op Some buf2 (map_op projl projr (comp_op Some buf1 op1 op2)) op3)"
  apply (coinduction arbitrary: op1 op2 op3 buf1 buf2 rule: bisim_coinduct_upto)
  subgoal for op1 op2 op3 buf1 buf2
    apply (intro conjI)
    subgoal
      unfolding sim_def
      apply safe
      subgoal for io op
        apply (drule step_map_op_inv)
        apply safe
        subgoal for io op
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
          apply (rule bc_bisim)
          oops

  


  find_theorems map_op choices


end

lemma
  "read_or_write \<bullet> (cp_once \<bullet> read_or_write) ~ (read_or_write \<bullet> cp_once) \<bullet> read_or_write \<Longrightarrow> False"

          
end
          apply (drule aux)
           apply (rule refl)
          apply auto
          subgoal for op1' op2' op3' buf1' buf2'
            apply (intro exI conjI)
             apply assumption
            apply (rule bc_base)
            apply (intro conjI exI)
            apply simp
            apply (rule refl)
            done
          done
        done
      done

          oops

          thm append_assoc

lemma
  "op1 \<bullet> (op2 \<bullet> op3) ~ op1 \<bullet> op2 \<bullet> op3"
  unfolding scomp_op_def
  

end

inductive can_input for R p where
  "(\<forall> op \<in> range (f o Observed). R op) \<Longrightarrow> can_input R p (Read p f)"
| "can_input R p op \<Longrightarrow> can_input R p (Write op p' x)"
| "(\<forall> op \<in> range f. can_input R p op) \<Longrightarrow> p \<noteq> p' \<Longrightarrow> can_input R p (Read p' f)"
| "op |\<in>| ops \<Longrightarrow> can_input R p op \<Longrightarrow> can_input R p (Choice ops)"

lemma uses_input_mono[mono]: "R \<le> S \<Longrightarrow> can_input R \<le> can_input S"
  apply safe
  subgoal for p op
    apply (rotate_tac )
    apply (induct op rule: can_input.induct)
    apply (auto 4 4 intro: can_input.intros)
    done
  done

coinductive sticky_input for p where
  "can_input (sticky_input p) p op \<Longrightarrow> sticky_input p op"

abbreviation "Readd p f \<equiv> scomp_op (id_op (\<lambda> _. BEmpty)) (Read p f)"

lemma
  "bisim (scomp_op (id_op buf) (Read (1::1) (\<lambda> _. end_op))) op"
  unfolding scomp_op_def
  apply (coinduction arbitrary: buf op rule: bisim_coinduct_upto)
  apply (intro conjI iffI)
  oops

coinductive buffered_reads where
  "buffered_reads buf (f x) \<Longrightarrow> BHD p buf = None \<Longrightarrow> buffered_reads buf (Read p f)"
| "buffered_reads (BTL p buf) (f x) \<Longrightarrow> BHD p buf = Some x \<Longrightarrow> buffered_reads buf (Read p f)"
| "buffered_reads buf op \<Longrightarrow> buffered_reads buf (Write op p x)"
| "(\<forall> op. op |\<in>| ops \<longrightarrow> buffered_reads buf op) \<Longrightarrow> buffered_reads buf (Choice ops)"
| "buffered_reads (BENQ p x buf) op \<Longrightarrow> buffered_reads buf op"

lemma
  "traced hist_op ios \<longleftrightarrow> amazing_trace ios"

lemma
  "traced (\<stileturn> hist_op \<turnstile> \<bullet> \<stileturn> foo_op \<turnstile>) \<longleftrightarrow> amazing_trace_2 ios"

lemma
  "bisim (\<I> \<bullet> \<stileturn>op\<turnstile>) \<stileturn>op\<turnstile>"
  unfolding scomp_op_def
  apply (coinduction arbitrary: buf op rule: bisim_coinduct_upto)
  apply (intro conjI iffI)
  oops


end
lemma can_end_pcomp_op_Inl:
  "can_end (pcomp_op op1 op2) \<Longrightarrow> can_end op1"
  apply (coinduction arbitrary: op1 op2)
  subgoal for op1 op2
    apply auto
    unfolding pcomp_op_def
    apply (cases op1; cases op2)
    apply (auto simp: choices_empty_diverged diverged_can_end can_end_op2_None_can_end_iff can_end_op1_None_can_end_iff natcUNIV.rep_eq split: if_splits)
    apply (metis (no_types, lifting) can_end.simps can_end_Read no_Choice_in_choices op.distinct(5) op.exhaust_sel op.split_sel)+
    done
  done


lemma cUnion_cempty[simp]:
  "cUnion {||} = {||}"
  using cUN_empty by auto

lemma can_end_comp_opI:
  "can_end op1 \<Longrightarrow>
   can_end op2 \<Longrightarrow>
   can_end (comp_op wire buf op1 op2)"
  apply (coinduction arbitrary: op1 op2)
  subgoal for op1 op2
    apply (erule can_end.cases)
    subgoal
      apply (erule can_end.cases)
      apply (auto simp: can_end_op2_None_can_end_iff can_end_op1_None_can_end_iff diverged_choices_empty natcUNIV.rep_eq split: if_splits)
      apply (smt (verit, ccfv_threshold) can_end.simps can_end_op2.coinduct cin.rep_eq)
      done
    subgoal
      apply (erule can_end.cases)
      apply (auto simp: can_end_op2_None_can_end_iff can_end_op1_None_can_end_iff diverged_choices_empty natcUNIV.rep_eq split: if_splits)
      apply (smt (verit, del_insts) can_end.simps can_end_op1.coinduct cin.rep_eq)
      apply (smt (verit, del_insts) can_end.simps can_end_op1.coinduct cin.rep_eq)
      apply (smt (verit, del_insts) can_end.simps can_end_op1.coinduct cin.rep_eq)
      apply (smt (verit, ccfv_threshold) can_end.simps can_end_op2.coinduct cin.rep_eq)+
      done
    done
  done

lemma can_end_pcomp_op[simp]:
  "can_end (pcomp_op op1 op2) \<longleftrightarrow> can_end op1 \<and> can_end op2"
  using can_end_pcomp_op_Inl can_end_pcomp_op_Inr can_end_comp_opI pcomp_op_def by metis

lemma step_pstep_comp_op_inv:
  "step (pcomp_op op1 op2) io op \<Longrightarrow>
   (\<exists> op1' p x op2'. step op1 (Inp p x) op1' \<and> op = (pcomp_op op1' op2) \<and> io = Inp (Inl p) x) \<or>
   (\<exists> op1' p x op2'. step op1 (Out p x) op1' \<and> op = (pcomp_op op1' op2) \<and> io = Out (Inl p) x) \<or>
   (\<exists> op2' p x op1'. step op2 (Inp p x) op2' \<and> op = (pcomp_op op1 op2') \<and> io = Inp (Inr p) x) \<or>
   (\<exists> op2' p x op1'. step op2 (Out p x) op2' \<and> op = (pcomp_op op1 op2') \<and> io = Out (Inr p) x)"
  apply (induct "pcomp_op op1 op2" io op arbitrary: op1 op2 rule: step.induct)
  subgoal for p f x op1 op2
    apply simp
    unfolding pcomp_op_def
    apply (cases op1; cases op2)
    apply simp_all
    done
  subgoal for p f x op1 op2
    apply simp
    unfolding pcomp_op_def
    apply (cases op1; cases op2)
    apply simp_all
    done
  subgoal for opa ops l op' op1 op2
    apply simp
    unfolding pcomp_op_def
    apply (cases op1; cases op2; simp; hypsubst_thin)
    subgoal 
      by (auto 10 10 simp add: cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros )
    subgoal
      by (auto 10 10 simp add: cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros )
    subgoal
      apply (auto simp add: cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros ; hypsubst_thin?)
      subgoal
        by (metis step.intros(1)) 
      subgoal for x
        apply (cases x)
        apply auto
        apply (metis Read_in_choices_step cin.rep_eq step.intros(3))
        apply (metis Write_in_choices_step cin.rep_eq step.intros(3))
        done
      done
    subgoal
      by (auto 10 10 simp add: cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros )
    subgoal
      by (auto 10 10 simp add: cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros )
    subgoal
      apply (auto simp add: cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros ; hypsubst_thin?)
      subgoal
        by (metis step.intros(2))   
      subgoal for x
        apply (cases x)
        apply auto
        apply (metis Read_in_choices_step cin.rep_eq step.intros(3))
        apply (metis Write_in_choices_step cin.rep_eq step.intros(3))
        done
      done
    subgoal
      apply (auto simp add: can_end_op2_None_can_end_iff can_end_op1_None_can_end_iff cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros ; hypsubst_thin?)
      subgoal for x
        apply (cases x)
        apply auto
        apply (metis Read_in_choices_step cin.rep_eq step.intros(3))
        apply (metis Write_in_choices_step cin.rep_eq step.intros(3))
        done
      done
    subgoal
      apply (auto simp add: can_end_op2_None_can_end_iff can_end_op1_None_can_end_iff cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros ; hypsubst_thin?)
      subgoal
        by (metis step.intros(2))  
      subgoal for x
        apply (cases x)
        apply auto
        apply (metis Read_in_choices_step cin.rep_eq step.intros(3))
        apply (metis Write_in_choices_step cin.rep_eq step.intros(3))
        done
      done
    subgoal
      apply (auto simp add: can_end_op2_None_can_end_iff can_end_op1_None_can_end_iff sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros ; hypsubst_thin?)
      subgoal for x
        apply (cases x)
        apply auto
        apply (metis Read_in_choices_step cin.rep_eq step.intros(3))
        apply (metis Write_in_choices_step cin.rep_eq step.intros(3))
        done
      subgoal for x
        apply (cases x)
        apply auto
        apply (metis Read_in_choices_step cin.rep_eq step.intros(3))
        apply (metis Write_in_choices_step cin.rep_eq step.intros(3))
        done
      subgoal 
        apply (auto simp add: bot_cset.rep_eq cinsert.rep_eq split: if_splits)
        done
      done
    done
  done

lemma step_pcomp_op_L:
  "step op1 io op1' \<Longrightarrow>
   step (pcomp_op op1 op2) (map_IO Inl Inl id io) (pcomp_op op1' op2)"
  apply (induct op1 io op1' arbitrary: op2 rule: step.induct)
  unfolding pcomp_op_def
  subgoal
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (simp add: cinsert.rep_eq)
    apply (rule disjI1)
    apply (rule refl)
    apply (auto simp add: observation.map_id)
    apply (rule step.intros(1))
    done
  subgoal
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (simp add: cinsert.rep_eq)
    apply (rule disjI1)
    apply (rule refl)
    apply (auto simp add: observation.map_id)
    apply (rule step.intros(2))
    done
  subgoal
    apply (erule step_choicesE)
    apply (simp_all add: observation.map_id)
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (rule cUnI1)
    apply (rule cimage_eqI)
    apply (rule refl)
    apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) [2]
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (rule cUnI1)
    apply (rule cimage_eqI)
    apply (rule refl)
    apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) [2]
    done
  done


lemma step_pcomp_op_R:
  "step op2 io op2' \<Longrightarrow>
   step (pcomp_op op1 op2) (map_IO Inr Inr id io) (pcomp_op op1 op2')"
  apply (induct op2 io op2' arbitrary: op1 rule: step.induct)
  unfolding pcomp_op_def
  subgoal
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (simp add: cinsert.rep_eq)
    apply (rule disjI1)
    apply (rule refl)
    apply (auto simp add: observation.map_id)
    apply (rule step.intros(1))
    done
  subgoal
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (simp add: cinsert.rep_eq)
    apply (rule disjI1)
    apply (rule refl)
    apply (auto simp add: observation.map_id)
    apply (rule step.intros(2))
    done
  subgoal
    apply (erule step_choicesE)
    apply (simp_all add: observation.map_id)
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (rule cUnI2)
    apply (rule cimage_eqI)
    apply (rule refl)
    apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) [2]
    apply (subst (1) comp_op_code)
    apply (rule step.intros(3))
    apply (rule cUnI1)
    apply (rule cUnI2)
    apply (rule cimage_eqI)
    apply (rule refl)
    apply (auto simp add: cinsert.rep_eq sup_cset.rep_eq cimage.rep_eq cUnion.rep_eq bot_cset.rep_eq image_iff intro: step.intros) [2]
    done
  done


lemma pcomp_op_diverged: 
  "diverged op1 \<Longrightarrow>
   bisim (pcomp_op op1 op2) (map_op Inr Inr op2)"
  apply (coinduction arbitrary: op1 op2 rule: bisim_coinduct_upto)
  subgoal for op1 op2
    unfolding pcomp_op_def
    apply (cases op1; cases op2)
    subgoal
      by (auto elim: diverged.cases)
    subgoal
      by (auto elim: diverged.cases)
    subgoal
      by (auto elim: diverged.cases)
    subgoal
      by (auto elim: diverged.cases)
    subgoal
      by (auto elim: diverged.cases)
    subgoal
      by (auto elim: diverged.cases)
    subgoal
      apply (auto simp add: diverged_choices_empty can_end_op2_None_can_end_iff can_end_op1_None_can_end_iff csingleton_iff choices_empty_diverged_iff rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def dest!: diverged_choices_empty)
      apply (metis (mono_tags, lifting) bc_base cin.rep_eq diverged.intros step.intros(1))
      apply (smt (verit, del_insts) bc_base bc_sym cin.rep_eq cinsertI1 diverged.simps step.intros(1) step.intros(3))
      done
    subgoal
      apply (auto simp add: diverged_choices_empty can_end_op2_None_can_end_iff can_end_op1_None_can_end_iff csingleton_iff choices_empty_diverged_iff rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def dest!: diverged_choices_empty)
      apply (smt (verit, ccfv_threshold) bc_base cin.rep_eq diverged.simps step.intros(2))
      apply (smt (verit, del_insts) bc_base bc_sym cin.rep_eq cinsertI1 diverged.simps step.intros(2) step.intros(3))
      done
    subgoal for ops1 ops2
      apply (intro conjI iffI)
      apply (metis can_end_map_op can_end_pcomp_op_Inr pcomp_op_def)
      apply (metis diverged_can_end can_end_map_op can_end_comp_opI pcomp_op_def)
      subgoal 
        unfolding sim_def
        apply (intro conjI impI allI)
        apply (drule step_pstep_comp_op_inv[unfolded pcomp_op_def])
        apply (auto simp add: csingleton_iff choices_empty_diverged_iff rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
        apply (metis cin.rep_eq diverged.simps op.inject(3) step_not_diverged)
        apply (metis cin.rep_eq diverged.simps op.inject(3) step_not_diverged)
        subgoal for op2' p x op
          apply (intro conjI exI)
          apply (rule step.intros(3)[rotated])
          apply (drule step_map_op[where f=Inr and g=Inr])
          apply (simp add: observation.map_id)
          apply (auto simp add: cimage.rep_eq)
          apply (rule bc_base)
          apply auto
          done
        subgoal for op2' p x op
          apply (intro conjI exI)
          apply (rule step.intros(3)[rotated])
          apply (drule step_map_op[where f=Inr and g=Inr])
          apply (simp add: observation.map_id)
          apply (auto simp add: cimage.rep_eq)
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal 
        unfolding sim_def
        apply (intro conjI impI allI)
        apply (drule step_map_op_inv)
        apply (elim exE conjE)
        apply hypsubst_thin
        subgoal for l s' io' op''
          apply (rule exI[of _ "comp_op (\<lambda>_. None) (\<lambda>_. BEnded) (Choice ops1) op''"])
          apply (intro conjI[rotated])
          apply (rule bc_sym)
          apply (rule bc_base)
          apply blast
          apply (rule step_pcomp_op_R[unfolded pcomp_op_def])
          apply assumption
          done
        done
      done
    done
  done

lemma pcomp_op_commute: "pcomp_op op1 op2 = map_op (case_sum Inr Inl) (case_sum Inr Inl) (pcomp_op op2 op1)"
  apply (coinduction arbitrary: op1 op2 rule: op.coinduct_upto)
  apply (safe del: iffI)
  subgoal for op1 op2
    unfolding pcomp_op_def
    by (subst (1 2) comp_op_code; simp)
  subgoal for op1 op2
    unfolding pcomp_op_def
    by (subst (asm) (1 2) comp_op_code; simp)
  subgoal for op1 op2
    unfolding pcomp_op_def
    by (subst (asm) (1 2) comp_op_code; simp)
  subgoal for op1 op2
    unfolding pcomp_op_def
    by (subst (1 2) comp_op_code; simp)
  subgoal for op1 op2
    unfolding pcomp_op_def
    by (subst (asm) (1 2) comp_op_code; simp)
  subgoal for op1 op2
    unfolding pcomp_op_def
    by (subst (asm) (1 2) comp_op_code; simp)
  subgoal for op1 op2
    unfolding pcomp_op_def
    by (subst (asm) (1 2) comp_op_code; simp)
  subgoal premises prems for op1 op2
    unfolding pcomp_op_def
    apply (subst (3 4) comp_op_code)
    apply (simp only: op.sel op.map cUn_commute cimage_cUn cimage_cimage)
    apply (rule cUn_parametric[THEN rel_funD, THEN rel_funD])
    apply (simp add: rel_cset_alt_def cinsert.rep_eq bot_cset.rep_eq op.cong_refl)
    apply (smt (verit, best) can_end_op1_None_can_end_iff can_end_op2_None_can_end_iff comp_op.cong_refl rel_set_def)
    apply (subst (2) cUn_commute)
    apply (rule cUn_parametric[THEN rel_funD, THEN rel_funD])
    apply (rule cimage_parametric[THEN rel_funD, THEN rel_funD, rotated])
    apply (rule cset.rel_refl_strong[of _ "eq_onp (\<lambda>x. x |\<in>| choices op1)"])
    apply (simp add: eq_onp_def)
    apply (rule rel_funI)
    apply (auto simp add: eq_onp_def rel_fun_def comp_def
        intro!: op.cong_Read op.cong_Write intro: op.cong_base split: op.splits) []
    apply (rule cimage_parametric[THEN rel_funD, THEN rel_funD, rotated])
    apply (rule cset.rel_refl_strong[of _ "eq_onp (\<lambda>x. x |\<in>| choices op2)"])
    apply (simp add: eq_onp_def)
    apply (rule rel_funI)
    apply (auto simp add: eq_onp_def rel_fun_def comp_def
        intro!: op.cong_Read op.cong_Write intro: op.cong_base split: op.splits) []
    done
  done


lemma in_choices_case_op: "x \<in> rcset (choices op) \<Longrightarrow>
  case_op RE WR (\<lambda>_. undefined) x \<in> case_op (\<lambda>p f. {RE p f}) (\<lambda>op q x. {WR op q x}) CH x"
  by (auto split: op.splits)

lemma step_map_op_reassoc_map_IO_assoc:
  "step op (map_IO assoc assoc id io) op' \<Longrightarrow>
   step (map_op reassoc reassoc op) io (map_op reassoc reassoc op')"
  apply (induct op "map_IO assoc assoc id io" op' arbitrary: io rule: step.induct)
  subgoal for p f x io
    apply (cases io)
    apply (simp_all add: observation.map_id)
    apply (metis comp_apply id_apply reassoc_assoc step.simps)
    done
  subgoal for p f x io
    apply (cases io)
    apply (simp_all add: observation.map_id)
    apply (metis comp_apply id_apply reassoc_assoc step.simps)
    done
  subgoal for op ops op' io
    apply (cases io)
    apply (simp_all add: observation.map_id)
    subgoal
      by (metis IO.simps(9) cimage_eqI cin.rep_eq observation.map_id step.intros(3))
    subgoal
      by (metis IO.simps(10) cimageI cin.rep_eq id_def step.simps)
    done
  done

lemma step_map_op_assoc_map_IO_reassoc:
  "step op (map_IO reassoc reassoc id io) op' \<Longrightarrow>
   step (map_op assoc assoc op) io (map_op assoc assoc op')"
  apply (induct op "map_IO reassoc reassoc id io" op' arbitrary: io rule: step.induct)
  subgoal for p f x io
    apply (cases io)
    apply (simp_all add: observation.map_id)
    apply (smt (verit) assoc.simps(1) assoc.simps(2) assoc.simps(3) comp_apply reassoc.elims step.intros(1))
    done
  subgoal for p f x io
    apply (cases io)
    apply (simp_all add: observation.map_id)
    apply (smt (verit, ccfv_SIG) assoc.simps(1) assoc.simps(2) assoc.simps(3) reassoc.elims step.intros(2))
    done
  subgoal for op ops op' io
    apply (cases io)
    apply (simp_all add: observation.map_id)
    subgoal
      by (metis IO.simps(9) cimage_eqI cin.rep_eq observation.map_id step.intros(3))
    subgoal
      by (metis IO.simps(10) cimageI cin.rep_eq id_def step.simps)
    done
  done

lemma step_map_op_reassocD:
  "step (map_op reassoc reassoc op) io op' \<Longrightarrow>
   step op (map_IO assoc assoc id io) (map_op assoc assoc op')"
  apply (induct "map_op reassoc reassoc op" io op' arbitrary: op rule: step.induct)
  subgoal
    apply (simp_all add: observation.map_id)
    apply (smt (verit, del_insts) assoc_reassoc comp_apply observation.map_ident op.map_comp op.map_id op.simps(25) step.intros(1))
    done
  subgoal for op q x opa
    apply (cases op)
    apply (simp_all add: observation.map_id)
    apply (metis (no_types, lifting) assoc_reassoc id_apply op.map_comp op.map_id0 op.simps(25) op.simps(26) step.intros(2))
    apply (metis (no_types, opaque_lifting) assoc_reassoc op.map_comp op.map_id op.simps(26) step.intros(2))
    apply (metis (no_types, opaque_lifting) assoc_reassoc id_apply op.map_comp op.map_id0 op.simps(26) op.simps(27) step.intros(2))
    done
  subgoal for op ops l op' op''
    apply (cases op)
    apply (simp_all add: observation.map_id)
    subgoal
      apply (auto 10 10 simp add: sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros; hypsubst_thin?)
      apply (smt (verit, del_insts) IO.simps(9) assoc_reassoc cin.rep_eq observation.map_id op.inject(1) op.map_comp op.map_id op.simps(25) reassoc_assoc step.intros(1) step.intros(3) step_map_op_assoc_map_IO_reassoc)
      done
    subgoal
      apply (auto simp add: sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros; hypsubst_thin?)
      apply (smt (verit, ccfv_threshold) assoc_reassoc cimageI cin.rep_eq id_apply op.map_comp op.map_id0 op.simps(26) op.simps(27) step.intros(2) step.intros(3))
      done
    subgoal
      apply (cases op'')
      apply (auto simp add: sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros; hypsubst_thin?)+
      done
    done
  done

lemma step_map_op_assocD:
  "step (map_op assoc assoc op) io op' \<Longrightarrow>
   step op (map_IO reassoc reassoc id io) (map_op reassoc reassoc op')"
  apply (induct "map_op assoc assoc op" io op' arbitrary: op rule: step.induct)
  subgoal
    apply (simp_all add: observation.map_id)
    apply (smt (verit, del_insts) reassoc_assoc comp_apply observation.map_ident op.map_comp op.map_id op.simps(25) step.intros(1))
    done
  subgoal for op q x opa
    apply (cases op)
    apply (simp_all add: observation.map_id)
    apply (metis (no_types, lifting) reassoc_assoc id_apply op.map_comp op.map_id0 op.simps(25) op.simps(26) step.intros(2))
    apply (metis (no_types, opaque_lifting) reassoc_assoc op.map_comp op.map_id op.simps(26) step.intros(2))
    apply (metis (no_types, opaque_lifting) reassoc_assoc id_apply op.map_comp op.map_id0 op.simps(26) op.simps(27) step.intros(2))
    done
  subgoal for op ops l op' op''
    apply (cases op)
    apply (simp_all add: observation.map_id)
    subgoal
      apply (auto 10 10 simp add: sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros; hypsubst_thin?)
      apply (smt (verit, del_insts) IO.simps(9) assoc.simps(1) assoc.simps(2) assoc.simps(3) cin.rep_eq observation.map_id op.map_comp op.map_id reassoc.elims reassoc_assoc reassoc_assoc step.intros(1) step.intros(3) step_map_op_reassoc_map_IO_assoc)
      done
    subgoal
      apply (auto simp add: sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros; hypsubst_thin?)
      apply (smt (verit, del_insts) cimageI cin.rep_eq id_def op.map_comp op.map_id0 op.simps(26) op.simps(27) reassoc_assoc step.intros(2) step.intros(3))
      done
    subgoal
      apply (cases op'')
      apply (auto simp add: sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro: step.intros; hypsubst_thin?)+
      done
    done
  done

lemma step_pcomp_assoc_reassoc_Inl:
  "step op (Inp (Inl (Inl p)) x) (map_op assoc assoc op') \<Longrightarrow>
   step (map_op reassoc reassoc op) (Inp (Inl p) x) op'"
  by (metis (no_types, lifting) IO.simps(9) assoc.simps(1) observation.map_id op.map_comp op.map_id reassoc_assoc step_map_op_reassoc_map_IO_assoc)

lemma step_pcomp_reassoc_assoc_Inl:
  "step op (Inp (Inl p) x) (map_op reassoc reassoc op') \<Longrightarrow>
   step (map_op assoc assoc op) (Inp (Inl (Inl p)) x) op'"
  by (metis (no_types, lifting) IO.simps(9) assoc_reassoc observation.map_id op.map_comp op.map_id reassoc.simps(1) step_map_op_assoc_map_IO_reassoc)

(* FIXME: move me *)
lemma bisim_assoc_reassoc:
  "bisim (map_op assoc assoc op) op' \<Longrightarrow>
   bisim (map_op reassoc reassoc op') op"
  apply (coinduction arbitrary: op op' rule: bisim_coinduct_upto)
  subgoal for op op'
    apply clarsimp
    apply (erule bisim.cases)
    subgoal for s t
      unfolding sim_def
      apply auto
      apply hypsubst_thin
      subgoal for l s
        by (smt (verit, del_insts) assoc_reassoc bc_base bisim_sym op.map_comp op.map_id reassoc_assoc step_map_op_reassocD step_map_op_reassoc_map_IO_assoc)
      subgoal for l s
        apply hypsubst_thin
        apply (drule spec2)
        apply (drule mp)
        apply (rule step_map_op_reassocD[of _ l s])
        apply (simp add: op.map_comp op.map_id)
        apply auto
        apply (drule spec2)
        apply (drule mp)
        apply assumption
        apply auto
        apply (metis (mono_tags, lifting) bc_base bc_sym step_map_op_reassoc_map_IO_assoc)
        done
      subgoal for l s
        apply hypsubst_thin
        apply rotate_tac
        apply (drule spec2)
        apply (drule mp)
        apply (rule step_map_op_reassocD[of _ l s])
        apply (simp add: op.map_comp op.map_id)
        apply auto
        apply (drule spec2)
        apply (drule mp)
        apply assumption
        apply auto
        apply (smt (verit, del_insts) bc_base bc_sym op.map_comp op.map_id reassoc_assoc step_map_op_reassoc_map_IO_assoc)
        done
      subgoal for l s
        apply hypsubst_thin
        apply (drule spec2)
        apply (drule mp)
        apply (rule step_map_op_reassocD[of _ l s])
        apply (simp add: op.map_comp op.map_id)
        apply auto
        apply (drule spec2)
        apply (drule mp)
        apply assumption
        apply auto
        apply (metis (mono_tags, lifting) bc_base bc_sym step_map_op_reassoc_map_IO_assoc)
        done
      done
    done
  done


lemma pcomp_op_associativity:
  "bisim (pcomp_op op1 (pcomp_op op2 op3)) (map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2) op3))"
  apply (coinduction arbitrary: op1 op2 op3 rule: bisim_coinduct_upto)
  subgoal for op1 op2 op3
    apply (intro conjI)
    subgoal by auto
    subgoal
      unfolding sim_def
      apply (intro allI impI)
      subgoal for l s'              
        apply (drule step_pstep_comp_op_inv)
        apply (elim exE disjE)
        subgoal for op1' p x
          apply (elim disjE exE conjE)
          subgoal for op2'
            apply hypsubst_thin
            apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1' op2) op3)"])
            apply (intro conjI)
            subgoal
              by (metis IO.simps(9) IO.simps(9) IO.simps(9) assoc.simps(1) observation.map_id step_map_op_reassoc_map_IO_assoc step_pcomp_op_L step_pcomp_op_L)
            subgoal
              by (auto intro: bc_base)
            done
          done
        subgoal for op1' p x
          apply (elim disjE exE conjE)
          subgoal for op2'
            apply hypsubst_thin
            apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1' op2) op3)"])
            apply (intro conjI)
            subgoal
              using step_map_op_reassoc_map_IO_assoc step_pcomp_op_L
              by (metis IO.simps(10) assoc.simps(1) id_apply)
            subgoal
              by (auto intro: bc_base)
            done
          done
        subgoal for op23 p x
          apply (elim disjE exE conjE)
          subgoal for op23'
            apply hypsubst_thin
            apply (drule step_pstep_comp_op_inv)
            apply (elim exE disjE)
            subgoal for op2' pa xa
              apply (elim disjE exE conjE)
              apply hypsubst_thin
              subgoal for op2''
                apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2') op3)"])
                apply (intro conjI)
                subgoal
                  apply (drule step_pcomp_op_R[of _ _ _ op1])
                  apply (drule step_pcomp_op_L[of _ _ _ op3])
                  apply (rule step_map_op_reassoc_map_IO_assoc)
                  apply (simp add: observation.map_id)
                  done
                subgoal
                  by (auto intro: bc_base)
                done
              done
            subgoal for op2' pa xa
              apply (elim disjE exE conjE)
              apply hypsubst_thin
              subgoal for op2''
                apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2') op3)"])
                apply (intro conjI)
                subgoal
                  apply (drule step_pcomp_op_R[of _ _ _ op1])
                  apply (drule step_pcomp_op_L[of _ _ _ op3])
                  apply (rule step_map_op_reassoc_map_IO_assoc)
                  apply (simp add: observation.map_id)
                  done
                subgoal
                  by (auto intro: bc_base)
                done
              done
            subgoal for op3' pa xa
              apply (elim disjE exE conjE)
              apply hypsubst_thin
              subgoal for op2''
                apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2) op3')"])
                apply (intro conjI)
                subgoal
                  apply (drule step_pcomp_op_R[of _ _ _ "pcomp_op op1 op2"])
                  apply (rule step_map_op_reassoc_map_IO_assoc)
                  apply (simp add: observation.map_id)
                  done
                subgoal
                  by (auto intro: bc_base)
                done
              done
            subgoal for op3' pa xa
              apply (elim disjE exE conjE)
              apply hypsubst_thin
              subgoal for op2''
                apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2) op3')"])
                apply (intro conjI)
                subgoal
                  apply (drule step_pcomp_op_R[of _ _ _ "pcomp_op op1 op2"])
                  apply (rule step_map_op_reassoc_map_IO_assoc)
                  apply (simp add: observation.map_id)
                  done
                subgoal
                  by (auto intro: bc_base)
                done
              done
            done
          done
        subgoal for op23 p x
          apply (elim disjE exE conjE)
          subgoal for op23'
            apply hypsubst_thin
            apply (drule step_pstep_comp_op_inv)
            apply (elim exE disjE)
            subgoal for op2' pa xa
              apply (elim disjE exE conjE)
              apply hypsubst_thin
              subgoal for op2''
                apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2') op3)"])
                apply (intro conjI)
                subgoal
                  apply (drule step_pcomp_op_R[of _ _ _ op1])
                  apply (drule step_pcomp_op_L[of _ _ _ op3])
                  apply (rule step_map_op_reassoc_map_IO_assoc)
                  apply (simp add: observation.map_id)
                  done
                subgoal
                  by (auto intro: bc_base)
                done
              done
            subgoal for op2' pa xa
              apply (elim disjE exE conjE)
              apply hypsubst_thin
              subgoal for op2''
                apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2') op3)"])
                apply (intro conjI)
                subgoal
                  apply (drule step_pcomp_op_R[of _ _ _ op1])
                  apply (drule step_pcomp_op_L[of _ _ _ op3])
                  apply (rule step_map_op_reassoc_map_IO_assoc)
                  apply (simp add: observation.map_id)
                  done
                subgoal
                  by (auto intro: bc_base)
                done
              done
            subgoal for op3' pa xa
              apply (elim disjE exE conjE)
              apply hypsubst_thin
              subgoal for op2''
                apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2) op3')"])
                apply (intro conjI)
                subgoal
                  apply (drule step_pcomp_op_R[of _ _ _ "pcomp_op op1 op2"])
                  apply (rule step_map_op_reassoc_map_IO_assoc)
                  apply (simp add: observation.map_id)
                  done
                subgoal
                  by (auto intro: bc_base)
                done
              done
            subgoal for op3' pa xa
              apply (elim disjE exE conjE)
              apply hypsubst_thin
              subgoal for op2''
                apply (rule exI[of _ "map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2) op3')"])
                apply (intro conjI)
                subgoal
                  apply (drule step_pcomp_op_R[of _ _ _ "pcomp_op op1 op2"])
                  apply (rule step_map_op_reassoc_map_IO_assoc)
                  apply (simp add: observation.map_id)
                  done
                subgoal
                  by (auto intro: bc_base)
                done
              done
            done
          done
        done
      done
    subgoal
      unfolding sim_def
      apply (intro allI impI)
      subgoal for l s'    
        apply (drule step_map_op_inv)
        apply (elim exE conjE)
        apply hypsubst_thin
        apply (drule step_pstep_comp_op_inv)
        apply (elim exE disjE)
        subgoal for io' op'' op1' p x
          apply (elim disjE exE conjE)
          subgoal for op12
            apply hypsubst_thin
            apply (drule step_pstep_comp_op_inv)
            apply (elim exE disjE)
            subgoal for op1' pa xa
              apply (elim exE conjE)
              apply hypsubst_thin
              apply (rule exI[of _ "pcomp_op op1' (pcomp_op op2 op3)"])
              apply (intro conjI)
              subgoal
                using step_map_op_reassoc_map_IO_assoc step_pcomp_op_L
                using IO.simps(10) by fastforce
              subgoal
                by (metis (mono_tags, lifting) bc_base bc_sym)
              done
            subgoal for op1' pa xa
              apply (elim exE conjE)
              apply hypsubst_thin
              apply (rule exI[of _ "pcomp_op op1' (pcomp_op op2 op3)"])
              apply (intro conjI)
              subgoal
                using step_map_op_reassoc_map_IO_assoc step_pcomp_op_L
                using IO.simps(10) by fastforce
              subgoal
                by (metis (mono_tags, lifting) bc_base bc_sym)
              done
            subgoal for op2' pa xa
              apply (elim exE conjE)
              apply hypsubst_thin
              apply (rule exI[of _ "pcomp_op op1 (pcomp_op op2' op3)"])
              apply (intro conjI)
              subgoal
                apply (drule step_pcomp_op_L[of _ _ _ op3])
                apply (drule step_pcomp_op_R[of _ _ _ op1])
                apply (simp add: observation.map_id)
                done
              subgoal
                by (metis (mono_tags, lifting) bc_base bc_sym)
              done
            subgoal for op2' pa xa
              apply (elim exE conjE)
              apply hypsubst_thin
              apply (rule exI[of _ "pcomp_op op1 (pcomp_op op2' op3)"])
              apply (intro conjI)
              subgoal
                apply (drule step_pcomp_op_L[of _ _ _ op3])
                apply (drule step_pcomp_op_R[of _ _ _ op1])
                apply (simp add: observation.map_id)
                done
              subgoal
                by (metis (mono_tags, lifting) bc_base bc_sym)
              done
            done
          done
        subgoal for io' op'' op1' p x
          apply (elim disjE exE conjE)
          subgoal for op12
            apply hypsubst_thin
            apply (drule step_pstep_comp_op_inv)
            apply (elim exE disjE)
            subgoal for op1' pa xa
              apply (elim exE conjE)
              apply hypsubst_thin
              apply (rule exI[of _ "pcomp_op op1' (pcomp_op op2 op3)"])
              apply (intro conjI)
              subgoal
                using step_map_op_reassoc_map_IO_assoc step_pcomp_op_L
                using IO.simps(10) by fastforce
              subgoal
                by (metis (mono_tags, lifting) bc_base bc_sym)
              done
            subgoal for op1' pa xa
              apply (elim exE conjE)
              apply hypsubst_thin
              apply (rule exI[of _ "pcomp_op op1' (pcomp_op op2 op3)"])
              apply (intro conjI)
              subgoal
                using step_map_op_reassoc_map_IO_assoc step_pcomp_op_L
                using IO.simps(10) by fastforce
              subgoal
                by (metis (mono_tags, lifting) bc_base bc_sym)
              done
            subgoal for op2' pa xa
              apply (elim exE conjE)
              apply hypsubst_thin
              apply (rule exI[of _ "pcomp_op op1 (pcomp_op op2' op3)"])
              apply (intro conjI)
              subgoal
                apply (drule step_pcomp_op_L[of _ _ _ op3])
                apply (drule step_pcomp_op_R[of _ _ _ op1])
                apply (simp add: observation.map_id)
                done
              subgoal
                by (metis (mono_tags, lifting) bc_base bc_sym)
              done
            subgoal for op2' pa xa
              apply (elim exE conjE)
              apply hypsubst_thin
              apply (rule exI[of _ "pcomp_op op1 (pcomp_op op2' op3)"])
              apply (intro conjI)
              subgoal
                apply (drule step_pcomp_op_L[of _ _ _ op3])
                apply (drule step_pcomp_op_R[of _ _ _ op1])
                apply (simp add: observation.map_id)
                done
              subgoal
                by (metis (mono_tags, lifting) bc_base bc_sym)
              done
            done
          done
        subgoal for io' op'' op3' p x
          apply (elim disjE exE conjE)
          subgoal for op12
            apply hypsubst_thin
            apply (rule exI[of _ "pcomp_op op1 (pcomp_op op2 op3')"])
            apply (intro conjI)
            subgoal
              apply (drule step_pcomp_op_R[of _ _ _ op2])
              apply (drule step_pcomp_op_R[of _ _ _ op1])
              apply (simp add: observation.map_id)
              done
            subgoal
              by (metis (mono_tags, lifting) bc_base bc_sym)
            done
          done
        subgoal for io' op'' op3' p x
          apply (elim disjE exE conjE)
          subgoal for op12
            apply hypsubst_thin
            apply (rule exI[of _ "pcomp_op op1 (pcomp_op op2 op3')"])
            apply (intro conjI)
            subgoal
              apply (drule step_pcomp_op_R[of _ _ _ op2])
              apply (drule step_pcomp_op_R[of _ _ _ op1])
              apply (simp add: observation.map_id)
              done
            subgoal
              by (metis (mono_tags, lifting) bc_base bc_sym)
            done
          done
        done
      done
    done
  done

lemma pcomp_op_bisim_rewrite_L:
  "bisim op1 op1' \<Longrightarrow>
   bisim (pcomp_op op1 op2) (pcomp_op op1' op2)"
  apply (coinduction arbitrary: op1 op1' op2 rule: bisim_coinduct_upto)
  subgoal for op1 op1' op2
    apply (erule bisim.cases)
    subgoal for op1 op1'
      apply hypsubst_thin
      unfolding sim_def
      apply auto
      subgoal for io op'
        apply (drule step_pstep_comp_op_inv)
        apply auto
        subgoal for op1'' p x
          apply hypsubst_thin
          apply (drule spec2)
          apply (drule mp)
          apply assumption
          apply safe
          subgoal for op1'''
            apply (rule exI[of _ "pcomp_op op1''' op2"])
            apply safe
            subgoal
              using step_pcomp_op_L observation.map_id by (metis IO.simps(9))
            subgoal
              by (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op1'' p x
          apply hypsubst_thin
          apply (drule spec2)
          apply (drule mp)
          apply assumption
          apply safe
          subgoal for op1'''
            apply (rule exI[of _ "pcomp_op op1''' op2"])
            apply safe
            subgoal
              using step_pcomp_op_L observation.map_id by fastforce
            subgoal
              by (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (rule exI[of _ "pcomp_op op1' op2'"])
          apply safe
          subgoal
            using observation.map_id by (metis IO.simps(9) step_pcomp_op_R)
          subgoal
            by (metis (mono_tags, lifting) bc_base bisim.intros sim_def)
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (rule exI[of _ "pcomp_op op1' op2'"])
          apply safe
          subgoal
            using observation.map_id step_pcomp_op_R by fastforce
          subgoal
            by (metis (mono_tags, lifting) bc_base bisim.intros sim_def)
          done
        done
      subgoal for io op'
        apply rotate_tac
        apply (drule step_pstep_comp_op_inv)
        apply auto
        subgoal for op1'' p x
          apply hypsubst_thin
          apply (drule spec2)
          apply (drule mp)
          apply assumption
          apply safe
          subgoal for op1'''
            apply (rule exI[of _ "pcomp_op op1''' op2"])
            apply safe
            subgoal
              using step_pcomp_op_L observation.map_id by (metis IO.simps(9))
            subgoal
              by (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op1'' p x
          apply hypsubst_thin
          apply (drule spec2)
          apply (drule mp)
          apply assumption
          apply safe
          subgoal for op1'''
            apply (rule exI[of _ "pcomp_op op1''' op2"])
            apply safe
            subgoal
              using step_pcomp_op_L observation.map_id by fastforce
            subgoal
              by (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (rule exI[of _ "pcomp_op op1 op2'"])
          apply safe
          subgoal
            using observation.map_id by (metis IO.simps(9) step_pcomp_op_R)
          subgoal
            by (metis (mono_tags, lifting) bc_base bisim.intros sim_def)
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (rule exI[of _ "pcomp_op op1 op2'"])
          apply safe
          subgoal
            using observation.map_id step_pcomp_op_R by fastforce
          subgoal
            by (metis (mono_tags, lifting) bc_base bisim.intros sim_def)
          done
        done
      subgoal for io op'
        apply (drule step_pstep_comp_op_inv)
        apply auto
        subgoal for op1'' p x
          apply hypsubst_thin
          apply (drule spec2)
          apply (drule mp)
          apply assumption
          apply safe
          subgoal for op1'''
            apply (rule exI[of _ "pcomp_op op1''' op2"])
            apply safe
            subgoal
              using step_pcomp_op_L observation.map_id by (metis IO.simps(9))
            subgoal
              by (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op1'' p x
          apply hypsubst_thin
          apply (drule spec2)
          apply (drule mp)
          apply assumption
          apply safe
          subgoal for op1'''
            apply (rule exI[of _ "pcomp_op op1''' op2"])
            apply safe
            subgoal
              using step_pcomp_op_L observation.map_id by fastforce
            subgoal
              by (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (rule exI[of _ "pcomp_op op1' op2'"])
          apply safe
          subgoal
            using observation.map_id by (metis IO.simps(9) step_pcomp_op_R)
          subgoal
            by (metis (mono_tags, lifting) bc_base bisim.intros sim_def)
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (rule exI[of _ "pcomp_op op1' op2'"])
          apply safe
          subgoal
            using observation.map_id step_pcomp_op_R by fastforce
          subgoal
            by (metis (mono_tags, lifting) bc_base bisim.intros sim_def)
          done
        done
      subgoal for io op'
        apply (drule step_pstep_comp_op_inv)
        apply auto
        subgoal for op1'' p x
          apply hypsubst_thin
          apply rotate_tac
          apply (drule spec2)
          apply (drule mp)
          apply assumption
          apply safe
          subgoal for op1'''
            apply (rule exI[of _ "pcomp_op op1''' op2"])
            apply safe
            subgoal
              using step_pcomp_op_L observation.map_id by (metis IO.simps(9))
            subgoal
              by (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op1'' p x
          apply hypsubst_thin
          apply rotate_tac
          apply (drule spec2)
          apply (drule mp)
          apply assumption
          apply safe
          subgoal for op1'''
            apply (rule exI[of _ "pcomp_op op1''' op2"])
            apply safe
            subgoal
              using step_pcomp_op_L observation.map_id by fastforce
            subgoal
              by (metis (mono_tags, lifting) bc_base)
            done
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (rule exI[of _ "pcomp_op op1 op2'"])
          apply safe
          subgoal
            using observation.map_id by (metis IO.simps(9) step_pcomp_op_R)
          subgoal
            by (metis (mono_tags, lifting) bc_base bisim.intros sim_def)
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (rule exI[of _ "pcomp_op op1 op2'"])
          apply safe
          subgoal
            using observation.map_id step_pcomp_op_R by fastforce
          subgoal
            by (metis (mono_tags, lifting) bc_base bisim.intros sim_def)
          done
        done
      done
    done
  done

lemma pcomp_op_bisim_rewrite_R:
  "bisim op2 op2' \<Longrightarrow>
   bisim (pcomp_op op1 op2) (pcomp_op op1 op2')"
  apply (subst (1 2) pcomp_op_commute)
  apply (drule pcomp_op_bisim_rewrite_L[of _ _ op1])
  using bisim_map_op apply auto
  done

lemma pcomp_op_bisim_rewrite:
  "bisim op1 op1' \<Longrightarrow>
   bisim op2 op2' \<Longrightarrow>
   bisim (pcomp_op op1 op2) (pcomp_op op1' op2')"
  using pcomp_op_bisim_rewrite_L pcomp_op_bisim_rewrite_R bisim_trans by blast

inductive can_read_None for wire where
  "BHD p buf = None \<Longrightarrow> can_read_None wire buf op (Read p f)"
| "can_read_None wire (BTL p buf) op (f x) \<Longrightarrow> BHD p buf = Some x \<Longrightarrow> can_read_None wire buf op (Read p f)"
| "can_read_None wire buf op op' \<Longrightarrow> can_read_None wire buf op (Write op' p x)"
| "can_read_None wire buf op op' \<Longrightarrow> op' |\<in>| ops \<Longrightarrow> can_read_None wire buf op (Choice ops)"
| "can_read_None wire buf (f x) op \<Longrightarrow> can_read_None wire buf (Read p f) op"
| "can_read_None wire (BENQ q x buf) op' op \<Longrightarrow> wire p = Some q \<Longrightarrow> can_read_None wire buf (Write op' p x) op"
| "can_read_None wire buf op' op \<Longrightarrow> wire p = None \<Longrightarrow> can_read_None wire buf (Write op' p x) op"
| "can_read_None wire buf op' op \<Longrightarrow> op' |\<in>| ops \<Longrightarrow> can_read_None wire buf (Choice ops) op"

inductive_cases can_read_None_ReadE[elim!]: "can_read_None wire buf (Read p1 f1) (Read p2 f2)"


lemma can_end_scomp_op_cp_op_False:
  "can_end (scomp_op cp_op op) \<Longrightarrow> False"
  unfolding scomp_op_def can_end_map_op can_end_comp_op_iff
  apply (erule comp_op_can_end.cases)
  subgoal
    apply hypsubst_thin
    apply (subst (asm) cp_op.code)
    apply blast
    done
  subgoal for q x buf op1' op2 p op1
    apply simp
    apply hypsubst_thin
    apply (subst (asm) cp_op.code)
    apply force
    done
  subgoal for p buf op1 op2' x op2
    apply simp
    apply hypsubst_thin
    apply (erule step_choicesE)
    apply auto
    done
  subgoal
    apply simp
    apply hypsubst_thin
    apply (subst (asm) cp_op.code)
    apply (erule step_choicesE)
    apply auto  
    apply (smt (verit) IO.distinct(1) can_end_op1_ReadE comp_op_can_end.simps stepReadE step_end_op)
    done
  done

lemma not_can_end_cp_op[simp]:
  "can_end cp_op \<Longrightarrow> False"
  apply (subst (asm) cp_op.code)
  apply (erule can_end.cases)
  apply auto
  done

lemma can_end_AW[simp]:
  "can_end AW"
  apply (coinduction)
  apply (rule disjI2)
  apply (subst AW.code)
  apply auto
  done

lemma can_end_W_AW:
  "can_end (comp_op Some buf W AW)"
  apply (coinduction arbitrary: buf)
  subgoal for buf
    apply (rule disjI2)
    apply (subst W.code)
    apply (subst AW.code)
    apply clarsimp
    apply (intro conjI impI)
    subgoal
      by auto
    subgoal
      using AW.code by auto
    done
  done

lemma can_end_op_1_no_reads:
  "inputs op = {} \<Longrightarrow>
   can_end_op1 Some op"
  apply (coinduction arbitrary: op)
  subgoal for op
    apply (cases op)
    apply auto
    done
  done



lemma step_comp_op_inv_Some_AW:
  "step_comp_op_inv Some io op buf op1 op2 \<Longrightarrow> 
   op1 = W \<Longrightarrow>
   op2 = AW \<Longrightarrow>
   io = Out (Inr 1) 42 \<and> (\<exists> buf. op = comp_op Some buf W AW)"
  apply (induct buf op1 op2 rule: step_comp_op_inv.induct)
  subgoal
    apply (subst (asm) W.code)
    apply auto
    done
  subgoal
    by (auto dest: step_AW_inv)
  subgoal
    by (auto dest: step_AW_inv)
  subgoal
    by (auto dest: step_AW_inv)
  subgoal
    by (auto dest: step_AW_inv step_W_inv)
  subgoal
    by (auto dest: step_AW_inv step_W_inv)
  subgoal
    apply simp
    apply (subst (asm) W.code)
    apply (erule step_comp_op_inv.cases)
    apply (auto split: option.splits)
    using step_comp_op_inv_end_op_not_Inr 
    using inputs_W apply blast
    apply (metis W.code step_comp_op_inv_end_op_not_Inr inputs_W)+
    done
  done

lemma map_IO_projl_Inl_projr_Inr[simp]:
  "map_IO projl projr id (map_IO Inl Inr id io) = io"
  apply (cases io)
  apply (auto simp add: observation.map_id)
  done

lemma map_op_projl_Inl_projr_In[simp]:
  "map_op projl projr (map_op Inl Inr op) = op"
  by (simp add: op.map_comp comp_def op.map_ident)

lemma
  "bisim (map_op projl projr (comp_op Some buf W AW)) AW"
  apply (coinduction arbitrary: buf rule: bisim_coinduct_upto)
  apply (intro conjI iffI)
  using can_end_AW apply blast
  apply (simp add: can_end_W_AW scomp_op_def)
  subgoal
    unfolding sim_def
    apply auto
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply clarsimp
      apply (frule step_step_comp_op_inv)
      apply hypsubst_thin
      subgoal for io op
        apply (frule step_comp_op_inv_Some_AW)
        apply simp_all
        apply (rule exI[of _ AW])
        apply auto
        subgoal
          apply (subst AW.code)
          apply (auto intro: step.intros)
          done
        subgoal
          apply (rule bc_base)
          apply auto
          done
        done
      done
    done
  subgoal for buf
    unfolding sim_def
    apply auto
    subgoal for io op'
      apply (drule step_AW_inv)
      apply simp
      apply auto
      apply hypsubst_thin
      apply (subst W.code)
      apply (subst AW.code)
      apply (auto 0 0)
      subgoal
        apply (intro conjI exI)
        apply (rule step.intros(3))
        apply (rule cinsertI2)
        apply (rule cinsertI2)
        apply simp
        apply (rule step.intros(2))
        apply (subst W.code[symmetric])
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      subgoal
        apply (intro conjI exI)
        apply (rule step.intros(3))
        apply (rule cinsertI2)
        apply simp
        apply (rule step.intros(2))
        apply (subst W.code[symmetric])
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      subgoal
        apply (intro conjI exI)
        apply (rule step.intros(3))
        apply (rule cinsertI2)
        apply simp
        apply (rule step.intros(2))
        apply (subst W.code[symmetric])
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      done
    done
  done

definition "eqT op1 op2 = (\<forall> ios. traced op1 ios \<longleftrightarrow> traced op2 ios)"

lemma 
  "traced end_op ios \<Longrightarrow> traced (scomp_op cp_op (Choice {|Read 1 (\<lambda>_. end_op), end_op|})) ios \<Longrightarrow> False"
  unfolding scomp_op_def
  apply (subst (asm) cp_op.code)
  apply (erule traced.cases)
  apply auto
  done

(*
lemma uses_input_not_can_end:
  "can_input R p op \<Longrightarrow> can_end op \<Longrightarrow> False"
  by (induct op rule: can_input.induct) auto
*)

lemma 
  "traced end_op ios \<Longrightarrow> traced (scomp_op cp_op (Read (1::1) (\<lambda>_. end_op))) ios \<Longrightarrow> False"
  unfolding scomp_op_def
  apply (subst (asm) cp_op.code)
  apply (erule traced.cases)
  apply (auto split: if_splits)
  done

lemma
  "always_uses_input p op \<Longrightarrow> eqT (scomp_op cp_op op) op"
  unfolding eqT_def 
  apply (intro allI iffI)
  defer
  subgoal for ios
    apply (coinduction arbitrary: op ios rule: traced_coinduct_upto)
    subgoal for op ios
      apply (erule traced.cases)
      subgoal for op'
        apply (erule always_uses_input.cases)
        apply auto
        apply hypsubst_thin
        unfolding scomp_op_def
        apply (auto dest: uses_input_not_can_end)
        done
      subgoal for op l op' lxs
        apply hypsubst_thin
        oops


lemma
  "traces op \<noteq> traces op' \<Longrightarrow> \<not> bisim op op'"
  using bisim_traces by blast

lemma
  "always_uses_input 1 op \<Longrightarrow> bisim (scomp_op cp_op op) op"
  apply (coinduction arbitrary: op rule: bisim_coinduct_upto)
  apply (intro conjI iffI)
  apply simp_all
  subgoal for op
    using can_end_scomp_op_cp_op_False apply blast
    done
  subgoal
    apply (erule always_uses_input.cases)
    apply (auto dest: uses_input_not_can_end)
    done
  subgoal for op
    unfolding scomp_op_def sim_def
    apply safe
    apply (drule step_map_op_inv)
    apply safe
    subgoal for l s' io' op''
      apply (drule step_step_comp_op_inv)
      oops

      find_theorems step comp_op

end
  apply (coinduction arbitrary: op)
  subgoal 
    apply simp
    apply (erule can_end.cases)
    subgoal
      apply (simp add: ranI)
      apply (rule disjI2)
      oops


end

lemma can_end_pcomp_op_Inl:
  "can_end (comp_op wire buf op1 op2) \<Longrightarrow> \<not> can_read_None wire buf op1 op2 \<Longrightarrow> \<not> can_end op2 \<Longrightarrow> can_end op1"
  apply (coinduction arbitrary: op1 op2 buf)
  subgoal for op1 op2 buf
    apply auto
    unfolding scomp_op_def
    apply (cases op1; cases op2)
    apply (auto simp: bot_cset.rep_eq cinsert.rep_eq cUnion.rep_eq cimage.rep_eq natcUNIV.rep_eq split: if_splits option.splits op.splits)


    find_theorems can_end pcomp_op


end
lemma
  "can_end (scomp_op op1 op2) \<Longrightarrow> can_end op2"






end




end

corecursive comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op" where
  "comp_op wire buf op1 op2 =
     (let comp_op' = (\<lambda>buf' op1' op2'. if \<exists>n. comp_producing wire buf op1 op2 n then comp_op wire buf' op1' op2' else end_op) in
     case (op1, op2) of
     (Choice op1s, Choice op2s) \<Rightarrow> safe_choice2 (comp_op wire buf) op1s op2s
   | (Choice op1s, Write op2' p2 x2) \<Rightarrow> safe_choice (\<lambda>op1. Write (comp_op wire buf op1 op2') (Inr p2) x2) op1s
   | (Choice op1s, Read p2 f2) \<Rightarrow> let buf' = if op1s = cempty then bend o buf else buf in if p2 \<in> ran wire
     then safe_choice_stop (comp_op' (BTL p2 buf') end_op (safe_read f2 (BHD p2 buf'))) (\<lambda>op1. comp_op wire (BTL p2 buf') op1 (safe_read f2 (BHD p2 buf'))) op1s
     else safe_choice (\<lambda>op1. Read (Inr p2) (\<lambda>y2. comp_op wire buf' op1 (f2 y2))) op1s
   | (Read p1 f1, Choice op2s) \<Rightarrow> safe_choice (\<lambda>op2. Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) op2)) op2s
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> choice2
        (Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) x2))
        (Write (Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) op2')) (Inr p2) x2)
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then Read (Inl p1) (\<lambda>y1. comp_op wire (BTL p2 buf) (f1 y1) (safe_read f2 (BHD p2 buf)))
     else choice2 (Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2))))
        (Read (Inr p2) (\<lambda>y2. Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) (f2 y2))))
   | (Write op1' p1 x1, Choice op2s) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> safe_choice (\<lambda>op2. Write (comp_op wire buf op1' op2) (Inl p1) x1) op2s
     | Some p \<Rightarrow> safe_choice_stop (comp_op' (BENQ p x1 buf) op1' end_op) (comp_op wire (BENQ p x1 buf) op1') op2s)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> choice2 (Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1)
          (Write (Write (comp_op wire buf op1' op2') (Inl p1) x1) (Inr p2) x2)
     | Some p \<Rightarrow> Write (comp_op wire (BENQ p x1 buf) op1' op2') (Inr p2) x2)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (BTL p2 buf) op1' (safe_read f2 (BHD p2 buf))) (Inl p1) x1
     | Some p \<Rightarrow> comp_op' (BTL p2 (BENQ p x1 buf)) op1' (safe_read f2 (BHD p2 (BENQ p x1 buf))))
     else (case wire p1 of
       None \<Rightarrow> choice2 (Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1)
         (Read (Inr p2) (\<lambda>y2. Write (comp_op wire buf op1' (f2 y2)) (Inl p1) x1))
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (BENQ p x1 buf) op1' (f2 y2)))
)"
  by (relation "measure (\<lambda>((wire, buf), op1, op2). THE i. comp_producing wire buf op1 op2 i)")
    (auto 0 3 simp: The_comp_producing elim: comp_producing.cases)

lemma not_comp_producing_eq_end_op: "\<forall>n. \<not> comp_producing wire buf op1 op2 n \<Longrightarrow> comp_op wire buf op1 op2 = end_op"
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
  subgoal for buf op1 op2
    apply (subst (2) comp_op.code)
    apply (auto split: op.splits if_splits option.splits simp: Let_def rel_cset_alt_def bot_cset.rep_eq intro: comp_producing.intros)
    done
  done

lemma comp_op_code[code]:
  "comp_op wire buf op1 op2 = (case (op1, op2) of
     (Choice op1s, Choice op2s) \<Rightarrow> safe_choice2 (comp_op wire buf) op1s op2s
   | (Choice op1s, Write op2' p2 x2) \<Rightarrow> safe_choice (\<lambda>op1. Write (comp_op wire buf op1 op2') (Inr p2) x2) op1s
   | (Choice op1s, Read p2 f2) \<Rightarrow> let buf' = if op1s = cempty then bend o buf else buf in if p2 \<in> ran wire
     then safe_choice (\<lambda>op1. comp_op wire (BTL p2 buf') op1 (safe_read f2 (BHD p2 buf'))) op1s
     else safe_choice (\<lambda>op1. Read (Inr p2) (\<lambda>y2. comp_op wire buf' op1 (f2 y2))) op1s
   | (Read p1 f1, Choice op2s) \<Rightarrow> safe_choice (\<lambda>op2. Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) op2)) op2s
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> choice2
        (Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) x2))
        (Write (Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) op2')) (Inr p2) x2)
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then Read (Inl p1) (\<lambda>y1. comp_op wire (BTL p2 buf) (f1 y1) (safe_read f2 (BHD p2 buf)))
     else choice2 (Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2))))
        (Read (Inr p2) (\<lambda>y2. Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) (f2 y2))))
   | (Write op1' p1 x1, Choice op2s) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> safe_choice (\<lambda>op2. Write (comp_op wire buf op1' op2) (Inl p1) x1) op2s
     | Some p \<Rightarrow> safe_choice (comp_op wire (BENQ p x1 buf) op1') op2s)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> choice2 (Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1)
          (Write (Write (comp_op wire buf op1' op2') (Inl p1) x1) (Inr p2) x2)
     | Some p \<Rightarrow> Write (comp_op wire (BENQ p x1 buf) op1' op2') (Inr p2) x2)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (BTL p2 buf) op1' (safe_read f2 (BHD p2 buf))) (Inl p1) x1
     | Some p \<Rightarrow> comp_op wire (BTL p2 (BENQ p x1 buf)) op1' (safe_read f2 (BHD p2 (BENQ p x1 buf))))
     else (case wire p1 of
       None \<Rightarrow> choice2 (Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1)
         (Read (Inr p2) (\<lambda>y2. Write (comp_op wire buf op1' (f2 y2)) (Inl p1) x1))
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (BENQ p x1 buf) op1' (f2 y2))))"
  apply (subst comp_op.code)
  apply (auto 0 4 split: op.splits option.splits simp add: Let_def intro: comp_producing.intros not_comp_producing_eq_end_op not_comp_producing_eq_end_op[symmetric])
  done
simps_of_case comp_op_simps': comp_op_code[unfolded prod.case]

simps_of_case comp_op_simps[simp]: comp_op.code[unfolded prod.case Let_def]

definition "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. BEnded)"

fun reassoc where
  "reassoc (Inl (Inl x)) = Inl x"
| "reassoc (Inl (Inr x)) = Inr (Inl x)"
| "reassoc (Inr x) = Inr (Inr x)"

lemma "pcomp_op op1 (pcomp_op op2 op3) = map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2) op3)"
  apply (coinduction arbitrary: op1 op2 op3 rule: op.coinduct_upto)
  subgoal for op1 op2 op3
    apply (cases op1; cases op2; cases op3)
    apply (auto simp: pcomp_op_def) []
    apply safe []
    apply (auto simp: pcomp_op_def) [2]
    subgoal for p1 f1 p2 f2 p3 f3
      unfolding pcomp_op_def comp_op_simps ran_empty simp_thms empty_iff if_False if_True fimage_finsert fimage_fempty
      sorry
    sorry
  find_theorems "_ \<in> {}"
end
section\<open>Inputs of comp_op\<close>

lemma inputs_comp_op2: "sub_op (Read p g) (comp_op wire buf op1 op2) d \<Longrightarrow> p \<in> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
proof (induct p \<open>comp_op wire buf op1 op2\<close> arbitrary: buf op1 op2 rule: sub_op_Read_induct)
  case (Read1 f p)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_end_op)
  then show ?case
    using Read1 by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
next
  case (Read2 p p' f x d g)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_end_op)
  then show ?case
    using Read2 by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
next
  case (Write p p' op' x d g)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_end_op)
  then show ?case
    using Write by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
qed

lemma inputs_comp_op_le2:
  "inputs (comp_op wire buf op1 op2) \<subseteq> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  using inputs_comp_op2 by (metis inputs_sub_op_Read subsetI)


lemma inputs_comp_producing:
  "p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow> 
   \<exists> n. comp_producing wire buf op1 op2 n"
  using not_comp_producing_eq_end_op by fastforce

lemma not_comp_producing_no_inputs:
  "\<forall>x. \<not> comp_producing wire buf op1 op2 x \<Longrightarrow>
   inputs (comp_op wire buf op1 op2) = {}"
  by (simp add: not_comp_producing_eq_end_op)

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
      by (metis all_not_in_conv comp_producing.intros(4) not_comp_producing_eq_end_op op.simps(37))
    subgoal for x11 x12 x2
      by (meson comp_producing.intros(12) inputs_comp_producing)
    done
  done

lemma comp_op_Read_simps_case:
  "comp_op wire buf (Read p f) op2 =
   Read (Inl p) (\<lambda> x. case op2 of
     end_op \<Rightarrow> comp_op wire buf (f x) end_op
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

lemma inputs_comp_op_arg_min_1[simp]:
  "p \<in> inputs (comp_op wire buf (f1 x) op) \<Longrightarrow>
   p \<in> inputs (comp_op wire buf (f1 (ARG_MIN (m :: _ \<Rightarrow> nat) x. p \<in> inputs (comp_op wire buf (f1 x) op))) op)"
  by (rule arg_min_natI)

lemma inputs_comp_op_arg_min_2[simp]:
  "p \<in> inputs (comp_op wire buf op (f2 y)) \<Longrightarrow>
   p \<in> inputs (comp_op wire buf op (f2 (ARG_MIN (m :: _ \<Rightarrow> nat) y. p \<in> inputs (comp_op wire buf op (f2 y)))))"
  by (rule arg_min_natI)

lemma inputs_comp_op_arg_min_3[simp]:
  "p \<in> inputs (comp_op wire buf (f1 x) (f2 y)) \<Longrightarrow>
   p \<in> inputs
         (comp_op wire buf
            (f1 (ARG_MIN (m1 :: _ \<Rightarrow> nat) x. (\<exists>xa. p \<in> inputs (comp_op wire buf (f1 x) (f2 xa)))))
            (f2 (ARG_MIN (m2 :: _ \<Rightarrow> nat) x. p \<in> inputs (comp_op wire buf
                            (f1 (ARG_MIN (m1 :: _ \<Rightarrow> nat) x. (\<exists>xa. p \<in> inputs (comp_op wire buf (f1 x) (f2 xa))))) (f2 x)))))"
  by (smt (verit, best) arg_min_natI)

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
      apply (cases "\<exists>n. comp_producing wire buf op1 op2 n"; (simp add: not_comp_producing_eq_end_op)?)
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

lemma outputs_comp_op2: "sub_op (Write op' p y) (comp_op wire buf op1 op2) d \<Longrightarrow> p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
proof (induct p \<open>comp_op wire buf op1 op2\<close> arbitrary: buf op1 op2 rule: sub_op_Write_induct)
  case (Read p p' f x op' y d)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_end_op)
  then show ?case
    using Read by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
next
  case (Write1 p p' op' x op2 y d)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_end_op)
  then show ?case
    using Write1 by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
next
  case (Write2 p op' x)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_end_op)
  then show ?case
    using Write2 by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
qed

lemma outputs_comp_op_le2:
  "outputs (comp_op wire buf op1 op2) \<subseteq> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  using outputs_comp_op2 by (metis outputs_sub_op_Write subsetI)

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
      apply (cases "\<exists>n. comp_producing wire buf op1 op2 n"; (simp add: not_comp_producing_eq_end_op)?)
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
        by (smt (z3) UnE comp_producing_outputs_comp_op empty_Diff empty_iff image_empty le_imp_less_Suc not_comp_producing_eq_end_op op.set(6) prems(1))
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
  comp_op wire buf op1 op2 = end_op \<or>
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

lemma lset_ios1_comp_op_end_op_not_visible:
  "x \<in> lset ios1 \<Longrightarrow>
   comp_op wire buf op1 op2 = end_op \<Longrightarrow>
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
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_end_op)
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_end_op)
    subgoal by (meson end_op causal.intros(10))
    subgoal by (meson end_op causal.intros(10) comp_producing.intros(4) not_comp_producing_eq_end_op)
    done
  done

lemma lset_ios2_comp_op_end_op_not_visible:
  "x \<in> lset ios2 \<Longrightarrow>
   causal wire buf ios1 ios2 \<Longrightarrow>
   comp_op wire buf op1 op2 = end_op \<Longrightarrow>
   traced op1 ios1 \<Longrightarrow>
   traced op2 ios2 \<Longrightarrow>
   \<not> visible_IO wire ((map_IO Inr Inr id) x)"
  apply (induct ios2 arbitrary: ios1 buf op1 op2 rule: lset_induct)
  subgoal for xs ios1 buf op1 op2
    apply (cases op1; cases op2)
    apply (auto split: if_splits option.splits dest: not_comp_producing_eq_end_op)+
    done
  subgoal for x' xs ios1 buf op1 op2
    apply (cases op1; cases op2)
    apply (auto split: if_splits option.splits dest: not_comp_producing_eq_end_op intro: comp_producing.intros traced.intros)
    subgoal
      by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd)
    subgoal
      by (smt (verit, best) comp_producing.intros(12) fun_upd_apply fun_upd_upd)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_end_op)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_end_op)
    subgoal
      using end_op by metis
    subgoal
      by (metis (mono_tags, opaque_lifting) end_op comp_eq_dest_lhs comp_producing.intros(9) not_comp_producing_eq_end_op)
    done
  done

lemma comp_producing_traced_cases:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   comp_op wire buf op1 op2 = end_op \<and> ios = LNil \<or>
   (\<exists> op1' op2' buf' p x. comp_op wire buf op1 op2 = Write (comp_op wire buf' op1' op2') (Inl p) x \<and> wire p = None \<and> lhd ios = Out (Inl p) x \<and> traced (Write (comp_op wire buf' op1' op2') (Inl p) x) ios) \<or>
   (\<exists> op1' op2' buf' p x. comp_op wire buf op1 op2 = Write (comp_op wire buf' op1' op2') (Inr p) x \<and> lhd ios = Out (Inr p) x \<and> traced (Write (comp_op wire buf' op1' op2') (Inr p) x) ios) \<or>
   (\<exists> p f y op1' op2' buf'. comp_op wire buf op1 op2 = Read (Inr p) (\<lambda>y. comp_op wire buf' op1' (f y)) \<and> p \<notin> ran wire \<and> lhd ios = Inp (Inr p) y \<and> traced (Read (Inr p) (\<lambda>y. comp_op wire buf' op1' (f y))) ios) \<or>
   (\<exists> p f y op1' op2' buf'. comp_op wire buf op1 op2 = Read (Inl p) (\<lambda>y. comp_op wire buf' (f y) op2') \<and> lhd ios = Inp (Inl p) y \<and> traced (Read (Inl p) (\<lambda>y. comp_op wire buf' (f y) op2')) ios) \<or>
   (\<exists> p f y op1' op2' buf' p' x. comp_op wire buf op1 op2 = Read (Inl p) (\<lambda> z. Write (comp_op wire buf' (f z) op2') (Inr p') x) \<and> lhd ios = Inp (Inl p) y \<and> lhd (ltl ios) = Out (Inr p') x \<and> traced (Read (Inl p) (\<lambda> z. Write (comp_op wire buf' (f z) op2') (Inr p') x)) ios) \<or>
   (\<exists> op1' op2' buf' p x p' y. comp_op wire buf op1 op2 = Write (Write (comp_op wire buf' op1' op2') (Inr p') y) (Inl p) x \<and> wire p = None \<and> lhd ios = Out (Inl p) x \<and> lhd (ltl ios) = Out (Inr p') y \<and> traced (Write (Write (comp_op wire buf' op1' op2') (Inr p') y) (Inl p) x) ios) \<or>
   (\<exists> p f y op1' op2' buf' p' x f'. comp_op wire buf op1 op2 = Read (Inl p) (\<lambda>y1. Read (Inr p') (\<lambda>y2. comp_op wire buf' (f y1) (f' y2))) \<and> p' \<notin> ran wire \<and> lhd ios = Inp (Inl p) y \<and> lhd (ltl ios) = Inp (Inr p') x \<and> traced (Read (Inl p) (\<lambda>y1. Read (Inr p') (\<lambda>y2. comp_op wire buf' (f y1) (f' y2)))) ios) \<or>
   (\<exists> p f y op1' op2' buf' p' x f'. comp_op wire buf op1 op2 = Write (Read (Inr p') (\<lambda>y. comp_op wire buf' op1' (f y))) (Inl p) x \<and> p' \<notin> ran wire \<and> wire p = None \<and>  lhd ios = Out (Inl p) x \<and> lhd (ltl ios) = Inp (Inr p') y \<and> traced (Write (Read (Inr p') (\<lambda>y. comp_op wire buf' op1' (f y))) (Inl p) x) ios)"
  apply (induct buf op1 op2 n arbitrary: ios rule: comp_producing.induct)
  subgoal
    by auto
  subgoal
    by (auto 10 10 simp add: btl_bend split: option.splits if_splits intro: traced.intros)
  subgoal for p1 buf op1' x1
    by (auto 10 10 intro: traced.intros)
  subgoal
    by (auto split: if_splits)
  subgoal
    by (auto 10 10 split: if_splits intro: traced.intros)
  subgoal for buf p1 f1 op2' p2 x2 ios
    apply (auto 10 10 split: if_splits  intro: traced.intros)
    done
  subgoal for buf op1' p1 x1 op2' p2 x2 ios
    by (auto 10 10 split: if_splits option.splits intro: traced.intros)
  subgoal
    by (auto 10 10 split: if_splits option.splits intro: traced.intros)
  subgoal for p2 buf f2 n ios
    by (auto 10 10 split: if_splits option.splits intro: traced.intros)
  subgoal
    apply (auto 10 10 split: if_splits option.splits intro: traced.intros)
    done
  subgoal
    by (auto 10 10 split: if_splits option.splits intro: traced.intros)
  subgoal 
    by (auto split: if_splits option.splits)
  done

lemma comp_producing_traced_cong_causalD:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   traced op1 ios1 \<Longrightarrow>
   traced op2 ios2 \<Longrightarrow>
   causal wire buf ios1 ios2 \<Longrightarrow>
   comp_op wire buf op1 op2 = end_op \<and> lfilter (visible_IO wire) (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) = LNil \<or>
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
      by (smt (verit, del_insts) end_op causal.intros(10) lalternate_LNil(2) llist.simps(12) observation.map_id tc_base)
    done
  subgoal for buf p1 f1 ios1 ios2
    apply (erule causal.cases)
    apply (auto 10 10 intro!: tc_base end_op causal.intros(10))
    done
  subgoal
    apply (erule causal.cases)
    apply (auto simp add: lmap_eq_LNil split: if_splits intro: end_op causal.intros(10) comp_producing.intros(4))
    subgoal for lxs x
      by (smt (verit) end_op causal.intros(10) lalternate_LNil(2) lmap_eq_LNil)
    subgoal for lxs x
      by (smt (verit) end_op causal.intros(10) lalternate_LNil(2) lmap_eq_LNil)
    done
  subgoal
    by (auto 10 10 intro!: tc_base end_op)
  subgoal
    apply (erule causal.cases)
    apply auto
    subgoal for lxs lxsa
      by (smt (verit, del_insts) observation.map_id tc_base tc_write)
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
      by (smt (verit, ccfv_threshold) end_op lalternate_LNil(1) lmap_eq_LNil observation.map_id tc_base)
    done
  subgoal for p2 buf f2 ios1 ios2
    apply (erule causal.cases; hypsubst_thin)
    apply simp_all
    apply auto[10]
    subgoal for p ios2
      apply (erule traced_ReadE)
      apply simp_all
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
      done
    subgoal
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply assumption
      apply (drule meta_mp)
      apply blast
      apply auto
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
      done
    done
  subgoal for ios2 p y
    apply (erule traced_ReadE)
    apply (clarsimp intro!: tc_base)
    apply (smt (z3) causal_InpInpE observation.map_id tc_base tc_read)
    done
  subgoal for ios2 p y
    apply (erule traced_WriteE traced_ReadE)
    apply (clarsimp intro!: tc_base)
    apply (erule causal.cases)
    apply auto
    subgoal by (smt (verit, del_insts) observation.map_id tc_base)
    subgoal
      by (smt (verit, del_insts) observation.map_id tc_base tc_read)
    subgoal
      by (smt (verit, del_insts) tc_base)
    done
  subgoal
    apply (elim traced_WriteE traced_ReadE)
    apply (simp split: if_splits)
    subgoal
      by (smt (verit) causal_OutInpE comp_producing.intros(12) domI domIff fun_upd_same fun_upd_upd option.inject)
    subgoal
      apply (auto 0 0)
      apply blast
      apply blast
      using comp_producing.intros(12) apply fastforce
      done
    done
  done

declare [[unify_search_bound = 100]]

corec retrace_comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow> ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> 'd observation llist \<Rightarrow> 'd observation llist \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) IO llist" where
  "retrace_comp_op wire buf op1 op2 inps1 inps2 = (
     case (op1, op2) of
     (end_op, end_op) \<Rightarrow> LNil
   | (end_op, Write op2' p2 x2) \<Rightarrow> LCons (Out (Inr p2) x2) (retrace_comp_op wire (bend o buf) end_op op2' inps1 inps2)
   | (end_op, Read p2 f2) \<Rightarrow> let buf' = bend o buf in if p2 \<in> ran wire
     then LCons (Inp (Inr p2) (BHD p2 buf')) (retrace_comp_op wire (BTL p2 buf') end_op (f2 (BHD p2 buf')) inps1 inps2)
     else LCons (Inp (Inr p2) (lhd inps2)) (retrace_comp_op wire buf' end_op (f2 (lhd inps2)) inps1 (ltl inps2))
   | (Read p1 f1, end_op) \<Rightarrow> LCons (Inp (Inl p1) (lhd inps1)) (retrace_comp_op wire buf (f1 (lhd inps1)) end_op (ltl inps1) inps2)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> LCons (Inp (Inl p1) (lhd inps1)) (LCons (Out (Inr p2) x2) (retrace_comp_op wire buf (f1 (lhd inps1)) op2' (ltl inps1) inps2))
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then LCons (Inp (Inl p1) (lhd inps1)) (LCons (Inp (Inr p2) (BHD p2 buf)) (retrace_comp_op wire (BTL p2 buf) (f1 (lhd inps1)) (f2 (BHD p2 buf)) (ltl inps1) inps2))
     else LCons (Inp (Inl p1) (lhd inps1)) (LCons (Inp (Inr p2) (lhd inps2)) (retrace_comp_op wire buf (f1 (lhd inps1)) (f2 (lhd inps2)) (ltl inps1) (ltl inps2)))
   | (Write op1' p1 x1, end_op) \<Rightarrow> LCons (Out (Inl p1) x1) (retrace_comp_op wire buf op1' end_op inps1 inps2)
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

simps_of_case retrace_comp_op_simps[simp]: retrace_comp_op.code[unfolded prod.case Let_def]

abbreviation "Inp_Inl_llist ios \<equiv> lmap (case_IO (case_sum (\<lambda> _ ob. ob) undefined) undefined) (lfilter (case_IO (case_sum \<top> \<bottom>) \<bottom>) ios)"
abbreviation "Inp_Inr_llist ios \<equiv> lmap (case_IO (case_sum undefined (\<lambda> _ ob. ob)) undefined) (lfilter (case_IO (case_sum \<bottom> \<top>) \<bottom>) ios)"

abbreviation "retrace_comp_op_ios wire buf op1 op2 ios \<equiv> retrace_comp_op wire buf op1 op2 (Inp_Inl_llist ios) (Inp_Inr_llist ios)"

abbreviation "Inl_llist ios \<equiv>
  lmap (case_IO (case_sum (\<lambda> p ob. Inp p ob) undefined) (case_sum (\<lambda> p ob. Out p ob) undefined)) (lfilter (case_IO (case_sum \<top> \<bottom>) (case_sum \<top> \<bottom>)) ios)"

abbreviation "Inr_llist ios \<equiv>
  lmap (case_IO (case_sum undefined (\<lambda> p ob. Inp p ob)) (case_sum undefined (\<lambda> p ob. Out p ob))) (lfilter (case_IO (case_sum \<bottom> \<top>) (case_sum \<bottom> \<top>)) ios)"

lemma in_retrace_comp_op_end_op_not_Inl:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = retrace_comp_op wire buf end_op op2 ios1 ios2 \<Longrightarrow>
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

lemma in_retrace_comp_op_end_op_not_Inr:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = retrace_comp_op wire buf op1 end_op ios1 ios2 \<Longrightarrow>
   case_IO (case_sum \<top> \<bottom>) (case_sum \<top> \<bottom>) x"
  apply (induct lxs arbitrary: buf op1 ios1 ios2 rule: lset_induct)
  subgoal for xs buf op1 ios1
    apply (cases op1)
    apply (auto simp add: Let_def split: if_splits IO.splits sum.splits)
    done
  subgoal for x' xs buf op1 ios1 ios2
    apply (cases op1; hypsubst)
    apply (simp_all add: Let_def split: if_splits)
    done
  done

lemma traced_comp_op_traced_1:
  "traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   traced op1 (Inl_llist (retrace_comp_op_ios wire buf op1 op2 ios))"
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
        apply (metis comp_producing.intros(12) fun_upd_same fun_upd_upd not_comp_producing_eq_end_op)
        apply simp
        apply (smt (verit, ccfv_threshold) comp_producing.intros(12) fun_upd_other not_comp_producing_eq_end_op)
        done
      subgoal
        apply auto
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
        apply (metis comp_producing.intros(4) not_comp_producing_eq_end_op)
        done
      done
    subgoal for p f
      apply hypsubst_thin
      apply (intro disjI2)
      apply (auto simp add: lmap_eq_LNil lfilter_eq_LNil split: if_splits IO.splits sum.splits dest: in_retrace_comp_op_end_op_not_Inl)
      done
    subgoal 
      apply hypsubst_thin
      apply (intro disjI2)
      apply (auto simp add: lmap_eq_LNil lfilter_eq_LNil split: if_splits IO.splits sum.splits dest: in_retrace_comp_op_end_op_not_Inl)
      done
    subgoal
      apply simp
      done
    done
  done

lemma traced_comp_op_traced_2:
  "traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   traced op2 (Inr_llist (retrace_comp_op_ios wire buf op1 op2 ios))"
  apply simp
  apply (coinduction arbitrary: op1 op2 buf ios)
  subgoal for op1 op2 buf ios
    apply (cases op1; cases op2)
    subgoal for p f p' f'
      apply hypsubst_thin
      apply (clarsimp split: sum.splits if_splits if_splits observation.splits)
      subgoal
        apply (cases "BHD p' buf")
        apply (auto 10 10)
        done        
      subgoal
        by (auto 10 10)
      done
    subgoal
      by fastforce
    subgoal
      by (auto simp add: lfilter_eq_LNil lmap_eq_LNil split: IO.splits sum.splits if_splits if_splits observation.splits dest: in_retrace_comp_op_end_op_not_Inr)
    subgoal for op p x p' f
      apply hypsubst_thin
      apply (clarsimp split: option.splits sum.splits if_splits if_splits observation.splits)
      subgoal for lxs
        apply (cases "BHD p' buf")
        apply (auto 10 10)
        done
      subgoal for lxs
        by (auto 10 10)
      subgoal for lxs
        by (metis observation.exhaust)
      subgoal for lxs
        apply (cases "BHD p' buf")
        apply (auto 10 10)
        done
      subgoal for lxs
        apply (auto elim!: chd.elims)
        apply (metis (mono_tags, lifting) end_op comp_producing.intros(12) fun_upd_same fun_upd_upd lfilter_LNil lmap_eq_LNil not_comp_producing_eq_end_op)
        apply (smt (verit) end_op comp_producing.intros(12) fun_upd_apply fun_upd_upd lfilter_LNil lmap_eq_LNil not_EOB not_comp_producing_eq_end_op)+
        done
      subgoal
        by (auto 10 10)
      done
    subgoal  
      by (auto 10 10 split: sum.splits if_splits if_splits observation.splits option.splits)
    subgoal  
      by (auto simp add: lfilter_eq_LNil lmap_eq_LNil split: IO.splits sum.splits if_splits if_splits observation.splits dest: in_retrace_comp_op_end_op_not_Inr)
    subgoal  
      apply hypsubst_thin
      apply (clarsimp split: option.splits sum.splits if_splits if_splits observation.splits)
      subgoal
        by (smt (verit) bhd.elims)
      subgoal
        apply (drule not_comp_producing_eq_end_op)
        apply (auto simp add: lmap_eq_LNil split: if_splits intro: end_op)
        apply (metis end_op lfilter_LNil lmap_eq_LNil)
        apply (smt (verit) end_op comp_apply comp_op_simps'(7) comp_op_simps(7) lfilter_LNil lmap_eq_LNil)
        done
      subgoal
        by (auto 10 10)
      done
    subgoal
      by (auto 10 10)
    subgoal
      by auto
    done
  done

lemma comp_producing_in_retrace_comp_op_eq_end_op:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   x \<in> lset (retrace_comp_op wire buf op1 op2 ios1 ios2) \<Longrightarrow>
   comp_op wire buf op1 op2 = end_op \<Longrightarrow>
   \<not> visible_IO wire x"
  apply (induct buf op1 op2 n arbitrary: ios1 ios2 rule: comp_producing.induct)
  apply (auto 10 10 split: if_splits option.splits intro: comp_producing.intros)
  done

lemma in_retrace_comp_op_eq_end_op:
  "x \<in> lset (retrace_comp_op wire buf op1 op2 ios1 ios2) \<Longrightarrow>
   comp_op wire buf op1 op2 = end_op \<Longrightarrow>
   \<not> visible_IO wire x"
  apply (subst (asm) lset_conv_lnth)
  apply safe
  subgoal for n
    apply (induct n arbitrary: buf op1 op2 ios1 ios2 rule: less_induct)
    subgoal for n' buf op1 op2 ios1 ios2
      apply (cases n')
      subgoal
        apply (cases op1; cases op2)
        apply (auto split: if_splits option.splits)
        done
      subgoal for n''
        apply (cases op1; cases op2)
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_end_op split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_end_op)
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_end_op split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_end_op)
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_end_op split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_end_op)
        subgoal
          apply (auto split: if_splits option.splits)
          subgoal
            apply (cases n'')
            apply simp
            subgoal for n'''
              using Suc_ile_eq by force
            done
          subgoal
            apply (cases n'')
            apply simp
            subgoal for n'''
              by (smt (verit, ccfv_threshold) Suc_ile_eq Extended_Nat.eSuc_mono comp_producing.intros(12) diff_Suc_1' diff_less_Suc eSuc_enat fun_upd_same fun_upd_upd lnth_Suc_LCons not_comp_producing_eq_end_op)
            done
          subgoal
            apply (cases n'')
            apply simp
            subgoal for n'''
              using Suc_ile_eq by force
            done
          subgoal
            apply (cases n'')
            apply simp
            subgoal for n'''
              by (smt (verit, best) Extended_Nat.eSuc_mono Suc_ile_eq Suc_lessD comp_producing.intros(12) eSuc_enat fun_upd_apply lessI lnth_Suc_LCons not_comp_producing_eq_end_op)
            done
          done
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_end_op split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_end_op)
        subgoal
          apply (clarsimp split: if_splits option.splits)
          subgoal
            using Suc_ile_eq by blast
          subgoal
            by (metis Suc_ile_eq comp_producing.intros(4) lessI not_comp_producing_eq_end_op)
          done
        subgoal
          apply (clarsimp split: if_splits option.splits)
          subgoal
            using Suc_ile_eq by blast
          subgoal
            by (smt (verit, best) Suc_ile_eq comp_eq_dest_lhs comp_producing.intros(9) lessI not_comp_producing_eq_end_op)
          done
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_end_op split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_end_op)
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_end_op split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_end_op)
        done
      done
    done
  done

lemma comp_producing_comp_op_visible_IO:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   traced (comp_op wire buf op1 op2) (LCons x ios) \<Longrightarrow>
   visible_IO wire x"
  apply (induct buf op1 op2 n arbitrary: ios rule: comp_producing.induct)
  apply (auto split: if_splits option.splits IO.splits sum.splits)
  done


lemma traced_visible:
  "x \<in> lset ios \<Longrightarrow>
   traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   visible_IO wire x"
  apply (subst (asm) lset_conv_lnth)
  apply safe
  subgoal for n
    apply (induct n arbitrary: buf op1 op2 ios rule: less_induct)
    subgoal for n buf op1 op2 ios
      apply (cases n)
      subgoal
        apply simp
        apply (cases "\<exists> n. comp_producing wire buf op1 op2 n")
        subgoal
          apply (elim exE)
          apply (frule comp_producing_traced_cases)
          apply assumption
          apply (elim exE disjE)
          apply auto
          done
        subgoal
          by (metis gr_implies_not_zero llength_LNil not_comp_producing_eq_end_op traced_end_opE)
        done
      subgoal for n'
        apply (cases "\<exists> n. comp_producing wire buf op1 op2 n")
        subgoal
          apply (elim exE)
          apply (frule comp_producing_traced_cases)
          apply assumption
          apply (elim exE disjE)
          apply auto
          using Suc_ile_eq apply blast+
          subgoal
            by (smt (verit, ccfv_SIG) IO.simps(6) Suc_ile_eq Suc_lessD iless_Suc_eq lessI less_Suc_eq_0_disj lnth_0 lnth_Suc_LCons old.sum.simps(6))
          subgoal
            by (smt (verit, ccfv_SIG) IO.simps(6) Suc_ile_eq Suc_lessD iless_Suc_eq lessI less_Suc_eq_0_disj lnth_0 lnth_Suc_LCons old.sum.simps(6))
          subgoal
            by (smt (verit, best) IO.simps(5) Suc_ile_eq Suc_lessD iless_Suc_eq lessI less_Suc_eq_0_disj lnth_0 lnth_Suc_LCons old.sum.simps(6))
          subgoal for n p f y op1' buf' p' xb lxs'
            by (smt (verit, best) IO.simps(5) Suc_ile_eq Suc_lessD iless_Suc_eq lessI less_Suc_eq_0_disj lnth_0 lnth_Suc_LCons old.sum.simps(6))
          done
        subgoal
          by (metis gr_implies_not_zero llength_LNil not_comp_producing_eq_end_op traced_end_opE)
        done
      done
    done
  done

lemma comp_producing_traced_in_retrace_comp_op_ios:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   x \<in> lset ios \<Longrightarrow>
   traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   \<exists> x. x \<in> lset (retrace_comp_op_ios wire buf op1 op2 ios) \<and> visible_IO wire x"
  apply (induct buf op1 op2 n arbitrary: ios rule: comp_producing.induct)
  apply (fastforce split: if_splits option.splits)+
  done      

lemma traced_in_retrace_comp_op_ios:
  "x \<in> lset ios \<Longrightarrow>
   traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   \<exists> x. x \<in> lset (retrace_comp_op_ios wire buf op1 op2 ios) \<and> visible_IO wire x"
  apply (cases "\<exists> n. comp_producing wire buf op1 op2 n")
  subgoal
    using comp_producing_traced_in_retrace_comp_op_ios
    by blast
  subgoal
    apply simp
    apply (drule not_comp_producing_eq_end_op)
    apply auto
    done
  done

lemma lhd_lalternate:
  "x \<in> lset ios1 \<Longrightarrow>
   lhd (lalternate ios1 ios2) = lhd ios1"
  apply (induct ios1 arbitrary: ios2 rule: lset_induct)
  apply (auto simp add: lalternate_LCons1)
  done

lemma Inr_llist_retrace_comp_op_ios_end_op:
  "Inr_llist (retrace_comp_op_ios wire buf op1 end_op ios) = LNil"
  apply (coinduction arbitrary: buf op1 ios)
  apply (intro impI conjI iffI)
  apply (auto split: IO.splits sum.splits)
  using in_retrace_comp_op_end_op_not_Inr apply fastforce+
  done

lemma Inl_llist_retrace_comp_op_ios_end_op:
  "Inl_llist (retrace_comp_op_ios wire buf end_op op2 ios) = LNil"
  apply (coinduction arbitrary: buf op2 ios)
  apply (intro impI conjI iffI)
  apply (auto split: IO.splits sum.splits)
  using in_retrace_comp_op_end_op_not_Inl apply fastforce+
  done

fun is_op1 where
  "is_op1 (Inp (Inl _) _) = True"
| "is_op1 (Out (Inl _) _) = True"
| "is_op1 _ = False"

fun is_op2 where
  "is_op2 (Inp (Inr _) _) = True"
| "is_op2 (Out (Inr _) _) = True"
| "is_op2 _ = False"

coinductive comp_op_alternate where
  "comp_op_alternate LNil"
| "(\<forall> x \<in> lset lxs. is_op1 x) \<Longrightarrow> comp_op_alternate lxs"
| "(\<forall> x \<in> lset lxs. is_op2 x) \<Longrightarrow> comp_op_alternate lxs"
| "comp_op_alternate lxs \<Longrightarrow> is_op1 x \<Longrightarrow> is_op2 y \<Longrightarrow> comp_op_alternate (LCons x (LCons y lxs))"

lemma retrace_comp_op_end_op1_is_op1:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = retrace_comp_op wire buf op1 end_op ios1 ios2 \<Longrightarrow>
   is_op1 x"
  apply (induct lxs arbitrary: buf op1 ios1 ios2 rule: lset_induct)
  subgoal for xs buf op1 ios1 ios2
    apply (cases op1)
    apply auto
    done
  subgoal for x' xs buf op1 ios1 ios2
    apply (cases op1)
    apply auto
    done
  done

lemma retrace_comp_op_end_op2_is_op2:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = retrace_comp_op wire buf end_op op2 ios1 ios2 \<Longrightarrow>
   is_op2 x"
  apply (induct lxs arbitrary: buf op2 ios1 ios2 rule: lset_induct)
  subgoal for xs buf op2 ios1 ios2
    apply (cases op2)
    apply (auto split: if_splits)
    done
  subgoal for x' xs buf op2 ios1 ios2
    apply (cases op2)
    apply (auto split: if_splits)
    done
  done

lemma comp_op_alternate_retrace_comp_op[simp]:
  "comp_op_alternate (retrace_comp_op wire buf op1 op2 ios1 ios2)"
  apply (coinduction arbitrary: buf op1 op2 ios1 ios2)
  subgoal for buf op1 op2 ios1 ios2
    apply (cases op1; cases op2)
    apply (auto 10 10 simp add: retrace_comp_op_end_op1_is_op1 retrace_comp_op_end_op2_is_op2 split: option.splits)
    done
  done

lemma Inr_llist_LNil[simp]:
  "\<forall>x\<in>lset ios. is_op1 x \<Longrightarrow>
   Inr_llist ios = LNil"
  apply (auto simp add: lmap_eq_LNil lfilter_eq_LNil split: IO.splits sum.splits)
  done

lemma Inr_llist_same[simp]:
  "\<forall>x\<in>lset ios. is_op2 x \<Longrightarrow>
   Inr_llist ios = lmap (case_IO (case_sum undefined (\<lambda> p ob. Inp p ob)) (case_sum undefined (\<lambda> p ob. Out p ob))) ios"
  apply (simp add: split: IO.splits sum.splits)
  apply (smt (verit, best) is_op2.simps(3) is_op2.simps(4) lfilter_id_conv)
  done

lemma Inl_llist_LNil[simp]:
  "\<forall>x\<in>lset ios. is_op2 x \<Longrightarrow>
   Inl_llist ios = LNil"
  apply (auto simp add: lmap_eq_LNil lfilter_eq_LNil split: IO.splits sum.splits)
  done

lemma Inl_llist_same[simp]:
  "\<forall>x\<in>lset ios. is_op1 x \<Longrightarrow>
   Inl_llist ios = lmap (case_IO (case_sum (\<lambda> p ob. Inp p ob) undefined) (case_sum (\<lambda> p ob. Out p ob) undefined)) ios"
  apply (simp add: split: IO.splits sum.splits)
  apply (smt (verit, best) is_op1.simps(3) is_op1.simps(4) lfilter_id_conv)
  done


lemma comp_op_alternate_lalternate:
  "comp_op_alternate lxs \<Longrightarrow>
   lalternate (lmap (map_IO Inl Inl id) (Inl_llist lxs)) (lmap (map_IO Inr Inr id) (Inr_llist lxs)) =
   lxs"
  apply (coinduction arbitrary: lxs rule: llist.coinduct_upto)
  apply (intro impI conjI iffI)
  subgoal
    unfolding lnull_def
    apply (erule comp_op_alternate.cases)
    apply (clarsimp split: if_splits)
    subgoal by (smt (verit, ccfv_threshold) IO.simps(5) IO.simps(6) is_op1.elims(1) lalternate_LNil(2) lalternate_simps(4) lfilter_id_conv llist.distinct(1) llist.exhaust_sel lmap_eq_LNil old.sum.simps(5) top2I)
    subgoal
      by (smt (z3) IO.simps(5) IO.simps(6) LNil_eq_lmap is_op2.elims(1) lalternate_LNil(1) lfilter_LNil lfilter_empty_conv lfilter_id_conv lset_lalternate2 old.sum.simps(6) top2I)
    subgoal
      by (smt (verit, del_insts) IO.simps(5) IO.simps(6) is_op1.elims(1) lalternate_LCons1 lfilter_LCons llist.distinct(1) llist.simps(13) old.sum.simps(5) top2I)
    done
  subgoal for lxs
    by (simp add: lnull_def)
  subgoal
    unfolding lnull_def
    apply (erule comp_op_alternate.cases)
    apply simp_all
    subgoal
      by (auto 0 0 simp add: neq_LNil_conv observation.map_id split: if_splits IO.splits sum.splits)
    subgoal
      by (auto 0 0 simp add: neq_LNil_conv observation.map_id split: if_splits IO.splits sum.splits)
    subgoal for lxs x y
      apply (cases x; cases y)
      apply (simp_all add: neq_LNil_conv observation.map_id split: if_splits sum.splits)
      done
    done
  subgoal for lxs
    apply (erule comp_op_alternate.cases)
    apply simp
    subgoal 
      apply (rule llist.cong_base)
      apply (auto simp add: comp_op_alternate.intros(2) llist.set_sel(2))
      done
    subgoal 
      apply (rule llist.cong_base)
      apply (auto simp add: comp_op_alternate.intros(3) llist.set_sel(2))
      done
    subgoal for lxs x y
      apply hypsubst_thin
      apply (cases x; cases y)
      subgoal for p d p' d'
        apply (cases p; cases p')
        apply (simp_all split: if_splits)
        apply (rule llist.cong_LCons)
        apply (simp add:  observation.map_id)
        apply (rule llist.cong_base)
        apply auto
        done
      subgoal for p d p' d'
        apply (cases p; cases p')
        apply (simp_all split: if_splits)
        apply (rule llist.cong_LCons)
        apply (simp add:  observation.map_id)
        apply (rule llist.cong_base)
        apply auto
        done
      subgoal for p d p' d'
        apply (cases p; cases p')
        apply (simp_all split: if_splits)
        apply (rule llist.cong_LCons)
        apply (simp add:  observation.map_id)
        apply (rule llist.cong_base)
        apply auto
        done
      subgoal for p d p' d'
        apply (cases p; cases p')
        apply (simp_all split: if_splits)
        apply (rule llist.cong_LCons)
        apply (simp add:  observation.map_id)
        apply (rule llist.cong_base)
        apply auto
        done
      done
    done
  done

lemma comp_producing_lhd_traced:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   traced (comp_op wire buf op1 op2) (LCons io ios) \<Longrightarrow> io = lhd (ldropWhile (\<lambda>x. \<not> visible_IO wire x) (retrace_comp_op_ios wire buf op1 op2 (LCons io ios)))"
  apply (induct buf op1 op2 n arbitrary: ios rule: comp_producing.induct)
  apply (fastforce simp add: lalternate_LCons1 observation.map_id split: if_splits option.splits)+
  done

lemma comp_producing_retrace_comp_op_ios_lfilter_cong:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   ios \<noteq> LNil \<Longrightarrow>
   llist.v1.congclp
    (\<lambda>llist llist'.
       \<exists>buf op1 op2 ios. llist = ios \<and> llist' = lfilter (visible_IO wire) (retrace_comp_op_ios wire buf op1 op2 ios) \<and> traced (comp_op wire buf op1 op2) ios)
      (ctl ios) (ctl (lfilter (visible_IO wire) (retrace_comp_op_ios wire buf op1 op2 ios)))"
  apply (induct buf op1 op2 n arbitrary: ios rule: comp_producing.induct)
  apply (force simp add:  observation.map_id split: if_splits option.splits intro!: llist.cong_LCons intro: llist.cong_base)+
  done

lemma traced_lfilter_visible_IO_alternate:
  "traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   ios = lfilter (visible_IO wire)
           (lalternate 
              (lmap (map_IO Inl Inl id) (Inl_llist (retrace_comp_op_ios wire buf op1 op2 ios)))
              (lmap (map_IO Inr Inr id) (Inr_llist (retrace_comp_op_ios wire buf op1 op2 ios))))"
  apply (subst comp_op_alternate_lalternate)
  using comp_op_alternate_retrace_comp_op apply blast
  apply (coinduction arbitrary: buf op1 op2 ios rule: llist.coinduct_upto)
  subgoal for buf op1 op2 ios
    apply (intro conjI impI iffI)
    subgoal
      unfolding lnull_def
      apply (cases ios)
      apply (auto 0 0 simp add: lset_lalternate lfilter_eq_LNil lmap_eq_LNil simp del: llist.simps(12) llist.simps(13))
      subgoal
        apply (drule in_retrace_comp_op_eq_end_op)
        apply (auto split: IO.splits sum.splits)
        done
      done
    subgoal
      unfolding lnull_def
      apply (cases ios)
      apply simp
      subgoal for io' ios'
        apply hypsubst_thin
        apply (simp only: lfilter_eq_LNil lmap_eq_LNil lset_lalternate lset_lfilter lset_lmap)
        apply (frule traced_in_retrace_comp_op_ios[rotated 1, where x=io'])
        apply simp
        apply (elim exE)
        subgoal for io
          apply simp
          apply (drule bspec[of _ _ io])
          subgoal
            apply (cases io)
            subgoal for p d
              apply (cases p)
              subgoal for l
                apply (simp_all add: observation.map_id)
                done
              subgoal for r
                apply (simp_all add: observation.map_id)
                done
              done
            subgoal for p d
              apply (cases p)
              subgoal for l
                apply (simp_all add: observation.map_id)
                done
              subgoal for r
                apply (simp_all add: observation.map_id)
                done
              done
            done
          apply auto
          done
        done
      done
    subgoal
      apply (cases "\<exists> n. comp_producing wire buf op1 op2 n")
      subgoal
        apply (cases ios)
        apply simp
        apply (elim exE)
        apply (drule comp_producing_lhd_traced)
        apply simp
        apply simp
        done
      subgoal
        by (metis lnull_def not_comp_producing_eq_end_op traced_end_opE)
      done
    subgoal
      apply (cases "\<exists> n. comp_producing wire buf op1 op2 n")
      subgoal
        unfolding lnull_def
        apply (elim exE)
        apply (drule comp_producing_retrace_comp_op_ios_lfilter_cong)
        apply simp
        apply simp_all
        done
      subgoal
        apply simp
        apply (metis lnull_def not_comp_producing_eq_end_op traced_end_opE)
        done
      done
    done
  done

find_theorems name: coinduct name: upto

thm traced_coinduct_upto  traced.coinduct


inductive causal_cong for R wire where
  cc_base:  "R wire buf ios1 ios2 \<Longrightarrow> causal_cong R wire buf ios1 ios2"
| cc_causal: "causal wire buf ios1 ios2 \<Longrightarrow> causal_cong R wire buf ios1 ios2"
| "causal_cong R wire (BTL p buf) ios1 ios2 \<Longrightarrow> y = BHD p buf \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal_cong R wire buf (LCons (Inp q x) ios1) (LCons (Inp p y) ios2)"
| "causal_cong R wire buf ios1 ios2 \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal_cong R wire buf (LCons (Inp q x) ios1) (LCons (Inp p y) ios2)"
| "causal_cong R wire buf ios1 ios2 \<Longrightarrow> causal_cong R wire buf (LCons (Inp q x) ios1) (LCons (Out p y) ios2)"
| "causal_cong R wire (BTL p (BENQ p' x buf)) ios1 ios2 \<Longrightarrow> y = BHD p (BENQ p' x buf) \<Longrightarrow> wire q = Some p' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal_cong R wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
| "causal_cong R wire (BENQ p' x buf) ios1 ios2 \<Longrightarrow> wire q = Some p' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal_cong R wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
| "causal_cong R wire buf ios1 ios2 \<Longrightarrow> wire q = None \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal_cong R wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
| "causal_cong R wire (BTL p buf) ios1 ios2 \<Longrightarrow> wire q = None \<Longrightarrow> y = BHD p buf \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal_cong R wire buf (LCons (Out q x) ios1) (LCons (Inp p y) ios2)"
| "causal_cong R wire buf ios1 ios2 \<Longrightarrow> wire q = None \<Longrightarrow> causal_cong R wire buf (LCons (Out q x) ios1) (LCons (Out p y) ios2)"
| "causal_cong R wire (BENQ p' x buf) ios1 ios2 \<Longrightarrow> wire q = Some p' \<Longrightarrow> causal_cong R wire buf (LCons (Out q x) ios1) (LCons (Out p y) ios2)"
| "causal_cong R wire (BTL p (bend o buf)) LNil ios2 \<Longrightarrow> y = BHD p (bend o buf) \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal_cong R wire buf LNil (LCons (Inp p y) ios2)"
| "causal_cong R wire (bend o buf) LNil ios2 \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal_cong R wire buf LNil (LCons (Inp p y) ios2)"
| "causal_cong R wire (bend o buf) LNil ios2 \<Longrightarrow> causal_cong R wire buf LNil (LCons (Out p y) ios2)"

lemma causal_cong_disj_causal[simp]:
  "(causal_cong R wire buf ios1 ios2 \<or> causal wire buf ios1 ios2) = causal_cong R wire buf ios1 ios2"
  apply (rule iffI)
  subgoal
    by (auto intro: cc_causal)
  subgoal
    apply (induct buf ios1 ios2 rule: causal_cong.induct)
    apply (auto intro: causal_cong.intros split: if_splits)
    subgoal
      using causal_cong.intros(6) by force
    subgoal
      by (force intro: causal_cong.intros split: if_splits)
    done
  done


thm causal.coinduct[where X="causal_cong R wire", where wire=wire, of buf ios1 ios2 ]

lemma bend_upd_btl[simp]:
  "(\<lambda>x. bend (if x = p then btl (buf p) else buf x)) = (\<lambda>a. if a = p then btl (bend (buf p)) else bend (buf a))"
  "(\<lambda>x. if x = p then bend (btl (buf p)) else bend (buf x)) = (\<lambda>a. if a = p then btl (bend (buf p)) else bend (buf a))"
  "(\<lambda>a. if a = p' then btl (benq x (buf p')) else if a = p' then benq x (buf p') else buf a) = (\<lambda>xa. if xa = p' then btl (benq x (buf p')) else buf xa)"
  apply auto
  apply (metis (mono_tags, opaque_lifting) btl_bend)+
  done

lemma causal_coinduct_upto:
  "R wire buf ios1 ios2 \<Longrightarrow>
  (\<And>x1 x2 x3.
    R wire x1 x2 x3 \<Longrightarrow>
    (\<exists>p ios1. (\<exists>q x. x2 = LCons (Inp q x) ios1) \<and> (\<exists>ios2 y. x3 = LCons (Inp p y) ios2 \<and> causal_cong R wire (x1(p := btl (x1 p))) ios1 ios2 \<and> y = BHD p x1 \<and> p \<in> ran wire)) \<or>
    (\<exists>ios1. (\<exists>q x. x2 = LCons (Inp q x) ios1) \<and> (\<exists>ios2 p. (\<exists>y. x3 = LCons (Inp p y) ios2) \<and> causal_cong R wire x1 ios1 ios2 \<and> p \<notin> ran wire)) \<or>
    (\<exists>ios1. (\<exists>q x. x2 = LCons (Inp q x) ios1) \<and> (\<exists>ios2. (\<exists>p y. x3 = LCons (Out p y) ios2) \<and> causal_cong R wire x1 ios1 ios2)) \<or>
    (\<exists>p p' x ios1 ios2 y q.
        x2 = LCons (Out q x) ios1 \<and>
        x3 = LCons (Inp p y) ios2 \<and> causal_cong R wire (x1(p' := benq x (x1 p'), p := btl (if p = p' then benq x (x1 p') else x1 p))) ios1 ios2 \<and> y = BHD (x1 p) (If (p = p') (benq x (x1 p'))) \<and> wire q = Some p' \<and> p \<in> ran wire) \<or>
    (\<exists>p' x ios1 ios2 q. x2 = LCons (Out q x) ios1 \<and> (\<exists>p. (\<exists>y. x3 = LCons (Inp p y) ios2) \<and> causal_cong R wire (x1(p' := benq x (x1 p'))) ios1 ios2 \<and> wire q = Some p' \<and> p \<notin> ran wire)) \<or>
    (\<exists>ios1 ios2 q. (\<exists>x. x2 = LCons (Out q x) ios1) \<and> (\<exists>p. (\<exists>y. x3 = LCons (Inp p y) ios2) \<and> causal_cong R wire x1 ios1 ios2 \<and> wire q = None \<and> p \<notin> ran wire)) \<or>
    (\<exists>p ios1 ios2 q. (\<exists>x. x2 = LCons (Out q x) ios1) \<and> (\<exists>y. x3 = LCons (Inp p y) ios2 \<and> causal_cong R wire (x1(p := btl (x1 p))) ios1 ios2 \<and> wire q = None \<and> y = BHD p x1 \<and> p \<in> ran wire)) \<or>
    (\<exists>ios1 ios2 q. (\<exists>x. x2 = LCons (Out q x) ios1) \<and> (\<exists>p y. x3 = LCons (Out p y) ios2) \<and> causal_cong R wire x1 ios1 ios2 \<and> wire q = None) \<or>
    (\<exists>p' x ios1 ios2 q. x2 = LCons (Out q x) ios1 \<and> (\<exists>p y. x3 = LCons (Out p y) ios2) \<and> causal_cong R wire (x1(p' := benq x (x1 p'))) ios1 ios2 \<and> wire q = Some p') \<or>
    x3 = LNil \<or>
    x2 = LNil \<and> (\<exists>p ios2 y. x3 = LCons (Inp p y) ios2 \<and> causal_cong R wire ((bend \<circ> x1)(p := btl (bend (x1 p)))) LNil ios2 \<and> y = BHD (x1 p) bend \<and> p \<in> ran wire) \<or>
    x2 = LNil \<and> (\<exists>ios2 p. (\<exists>y. x3 = LCons (Inp p y) ios2) \<and> causal_cong R wire (bend \<circ> x1) LNil ios2 \<and> p \<notin> ran wire) \<or> x2 = LNil \<and> (\<exists>ios2. (\<exists>p y. x3 = LCons (Out p y) ios2) \<and> causal_cong R wire (bend \<circ> x1) LNil ios2)) \<Longrightarrow>
   causal wire buf ios1 ios2"
  apply (rule causal.coinduct[where X = "causal_cong R wire", of buf ios1 ios2])
  apply (rule cc_base)
  apply assumption
  subgoal premises prems for buf' ios1' ios2'
    using prems(3) apply -
    apply (induct buf' ios1' ios2' rule: causal_cong.induct)
    apply simp_all
    subgoal for buf ios1 ios2
      using prems(2)[of buf ios1 ios2] apply simp
      apply (elim disjE conjE exE)
      apply (simp_all add: btl_bend  flip: fun_upd_apply split: if_splits)
      apply (auto simp add: fun_upd_def comp_def btl_bend intro: causal_cong.intros split: if_splits)
      done
    subgoal for buf ios1 ios2
      apply (erule causal.cases)
      apply (simp_all add: btl_bend  flip: fun_upd_apply split: if_splits)
      apply (auto simp add: btl_bend causal_buf_cong cc_causal fun_upd_def comp_def intro: causal_cong.intros split: if_splits)
      done
    subgoal
      apply (simp_all add: btl_bend  flip: fun_upd_apply split: if_splits)
      done
    subgoal
      using prems(2) apply simp
      apply (elim disjE conjE exE)
      apply (auto simp add: fun_upd_def comp_def btl_bend intro: causal_cong.intros split: if_splits)
      done
    subgoal
      using prems(2) apply simp
      apply (elim disjE conjE exE)
      apply (auto simp add: fun_upd_def comp_def btl_bend intro: causal_cong.intros split: if_splits)
      done
    subgoal
      using prems(2) apply simp
      apply (elim disjE conjE exE)
      apply (auto simp add: fun_upd_def comp_def btl_bend intro: causal_cong.intros split: if_splits)
      done
    subgoal
      using prems(2) apply simp
      apply (elim disjE conjE exE)
      apply (auto simp add: fun_upd_def comp_def btl_bend intro: causal_cong.intros split: if_splits)
      done
    subgoal
      using prems(2) apply simp
      apply (elim disjE conjE exE)
      apply (auto simp add: fun_upd_def comp_def btl_bend intro: causal_cong.intros split: if_splits)
      done
    subgoal
      using prems(2) apply simp
      apply (elim disjE conjE exE)
      apply (auto simp add: fun_upd_def comp_def btl_bend intro: causal_cong.intros split: if_splits)
      done
    subgoal
      using prems(2) apply simp
      apply (elim disjE conjE exE)
      apply (auto simp add: fun_upd_def comp_def btl_bend intro: causal_cong.intros split: if_splits)
      done
    done
  done

lemma traced_comp_op_causal:
  "traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   causal wire buf (Inl_llist (retrace_comp_op_ios wire buf op1 op2 ios)) (Inr_llist (retrace_comp_op_ios wire buf op1 op2 ios))"
  apply (coinduction arbitrary: buf op1 op2 ios)
  subgoal for buf op1 op2 ios
    apply (cases op1; cases op2)
    subgoal
      apply hypsubst_thin
      apply (simp only: comp_op_simps split: if_splits)
      subgoal
        apply (elim traced_ReadE)
        apply (intro disjI1)
        apply (simp del: llist.simps(12) llist.simps(13) lfilter.simps split: if_splits)
        apply (auto intro: cc_base)
        done
      subgoal
        apply (elim traced_ReadE)
        apply (rule disjI2)
        apply (rule disjI1)
        apply (auto intro: cc_base)
        done
      done
    subgoal
      apply hypsubst_thin
      apply (simp only: comp_op_simps split: if_splits)
      subgoal
        apply (elim traced_ReadE traced_WriteE)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (intro disjI1)
        apply (simp del: llist.simps(12) llist.simps(13) lfilter.simps split: if_splits)
        apply (auto intro: cc_base)
        done
      done
    subgoal for p f
      apply hypsubst_thin
      apply (simp only: comp_op_simps split: if_splits)
      apply (elim traced_ReadE traced_end_opE)
      apply simp
      subgoal for x lxs
        apply safe
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal for p d
          apply (cases p)
          apply simp_all
          apply (smt (z3) IO.simps(5) IO.simps(6) LNil_eq_lmap bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
          done
        subgoal for p d
          apply (cases p)
          apply simp_all
          apply (smt (z3) IO.simps(5) IO.simps(6) LNil_eq_lmap bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) old.sum.simps(5) retrace_comp_op_end_op1_is_op1)+
          done
        done
      done
    subgoal for op p x p' f
      apply hypsubst_thin
      apply (simp only: comp_op_simps split: option.splits if_splits; blast?)
      subgoal
        apply (elim traced_ReadE traced_WriteE)
        apply hypsubst_thin
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (intro disjI1)
        apply (auto intro: cc_base)
        done
      subgoal
        apply (elim traced_ReadE traced_WriteE)
        apply hypsubst_thin
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (intro disjI1)
        apply (auto intro: cc_base)
        done
      subgoal
        apply (simp split: if_splits)
        apply auto
        done
      subgoal
        apply simp
        apply auto
        subgoal
          by (smt (verit, ccfv_SIG) end_op comp_producing.intros(12) fun_upd_same fun_upd_upd lfilter_LNil lmap_eq_LNil not_comp_producing_eq_end_op)
        subgoal
          using end_op comp_producing.intros(12) fun_upd_same fun_upd_upd lfilter_LNil lmap_eq_LNil not_comp_producing_eq_end_op
          by (smt (verit, ccfv_SIG) fun_upd_other)
        done
      subgoal
        apply (simp split: if_splits)
        apply (elim traced_ReadE)
        apply auto
        done
      done
    subgoal for op p x op' p' y
      apply hypsubst_thin
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (simp only: comp_op_simps split: if_splits option.splits)
      apply (elim traced_WriteE)
      apply fastforce+
      done
    subgoal for op p x 
      apply hypsubst_thin
      apply (simp only: comp_op_simps split: if_splits option.splits)
      apply (elim traced_WriteE)
      subgoal
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
        done
      subgoal
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
        done
      subgoal
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
        done
      subgoal
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_end_op1_is_op1)
        done
      done
    subgoal for p f
      apply hypsubst_thin
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (simp only: comp_op_simps split: if_splits option.splits)
      subgoal
        apply auto
        using Inl_llist_LNil retrace_comp_op_end_op2_is_op2 apply blast
        apply (intro exI conjI)
        defer
        apply (rule refl)
        apply auto
        apply (rule sym)
        using Inl_llist_LNil retrace_comp_op_end_op2_is_op2 apply blast
        done
      subgoal
        apply auto
        subgoal using Inl_llist_LNil retrace_comp_op_end_op2_is_op2 by blast
        subgoal
          apply (rule exI[of _ end_op])
          apply (rule exI[of _ "f (BHD (buf p) bend)"])
          apply (rule exI[of _ LNil])
          apply (intro conjI)
          apply (rule sym)
          subgoal using Inl_llist_LNil retrace_comp_op_end_op2_is_op2 by blast
          subgoal
            by force
          subgoal
            apply (subst not_comp_producing_eq_end_op)
            apply safe
            subgoal for n
              unfolding not_def
              apply (drule spec[of _ "Suc n"])
              apply (rotate_tac 4)
              apply (drule mp)
              apply (rule comp_producing.intros)
              apply auto
              done
            apply (intro end_op)
            done
          done
        done
      subgoal
        apply auto
        using Inl_llist_LNil retrace_comp_op_end_op2_is_op2 apply blast
        apply (intro exI conjI)
        defer
        apply (rule refl)
        apply auto
        apply (rule sym)
        using Inl_llist_LNil retrace_comp_op_end_op2_is_op2 apply blast
        done
      done
    subgoal for op p x
      apply hypsubst_thin
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (simp only: comp_op_simps split: if_splits option.splits)
      apply auto
      using Inl_llist_LNil retrace_comp_op_end_op2_is_op2 apply blast
      apply (intro exI conjI)
      defer
      apply (rule refl)
      apply auto
      apply (rule sym)
      using Inl_llist_LNil retrace_comp_op_end_op2_is_op2 apply blast
      done
    subgoal
      apply auto
      done
    done
  done


lemma traced_comp_op:
  "traced (comp_op wire buf op1 op2) ios =
  (\<exists>ios1 ios2. traced op1 ios1 \<and> traced op2 ios2 \<and>
    ios = lfilter (visible_IO wire) (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) \<and>
    causal wire buf ios1 ios2)"
  apply (rule iffI)
  subgoal
    apply (rule exI[of _ "Inl_llist (retrace_comp_op_ios wire buf op1 op2 ios)"])
    apply (rule exI[of _ "Inr_llist (retrace_comp_op_ios wire buf op1 op2 ios)"])
    apply (intro conjI)
    apply (auto dest: traced_comp_op_traced_1 traced_comp_op_traced_2 traced_lfilter_visible_IO_alternate traced_comp_op_causal)
    done
  subgoal
    apply (elim exE conjE)
    subgoal for ios1 ios2
      apply (coinduction arbitrary: ios ios1 ios2 op1 op2 buf rule: traced_coinduct_upto)
      subgoal for ios ios1 ios2 op1 op2 buf
        apply (cases "\<exists> n. comp_producing wire buf op1 op2 n")
        subgoal
          apply (elim exE)
          apply (drule comp_producing_traced_cong_causalD)
          apply assumption+
          apply (elim exE disjE conjE)
          apply simp_all
          done
        subgoal
          apply simp
          apply (drule not_comp_producing_eq_end_op)
          apply simp
          apply (auto simp add: lfilter_eq_LNil lset_lalternate)
          subgoal
            apply (drule lset_ios1_comp_op_end_op_not_visible)
            apply assumption+
            apply auto
            done
          subgoal
            apply (drule lset_ios2_comp_op_end_op_not_visible)
            apply assumption+
            apply auto
            done
          done
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

definition "lfocus f A g B ios =
  lmap (map_IO f g id) (lfilter (case_IO (\<lambda>p _. p \<in> A) (\<lambda>p _. p \<in> B)) ios)"

abbreviation \<open>lfocusl \<equiv> lfocus projl (range Inl) projl (range Inl)\<close>
abbreviation \<open>lfocusr \<equiv> lfocus projr (range Inr) projr (range Inr)\<close>

lemma lfocus_Inl_lmap: \<open>lfocusl (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) = ios1\<close>
proof (coinduction arbitrary: ios1 ios2)
  case (Eq_llist ios1 ios2)
  then show ?case
    apply (cases ios1; cases ios2)
    apply (auto simp: lfocus_def lfilter_lfilter)
    subgoal for a
      apply (cases a)
      by auto
    subgoal for a b c
      apply (cases c)
      by auto
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b
      by (metis lalternate_LNil(2) llist.simps(12))
    subgoal for a b
      apply (cases a)
      by auto
    subgoal for a b
      apply (cases a)
      by auto
    subgoal for a b
      apply (cases a)
      by auto
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b c d
      apply (cases c)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    done
qed

lemma lfocus_Inr_lmap: \<open>lfocusr (lalternate (lmap (map_IO Inl Inl id) ios1) (lmap (map_IO Inr Inr id) ios2)) = ios2\<close>
proof (coinduction arbitrary: ios1 ios2)
  case (Eq_llist ios1 ios2)
  then show ?case
    apply (cases ios1; cases ios2)
    apply (auto simp: lfocus_def lfilter_lfilter)
    subgoal for a
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b
      by (metis lalternate_LNil(1) llist.simps(12))
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by auto
    subgoal for a b
      apply (cases a)
      by auto
    subgoal for a b c
      apply (cases c)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b c d
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b c
      apply (cases c)
      by (auto simp: observation.map_id)
    subgoal for a b
      apply (cases a)
      by (auto simp: observation.map_id)
    subgoal for a b c
      apply (cases c)
      by (auto simp: observation.map_id)
    subgoal for a b c
      apply (cases c)
      by (auto simp: observation.map_id)
    subgoal for a b c
      apply (cases c)
      by (auto simp: observation.map_id)
    done
qed

lemma visible_IO_None_True: \<open>visible_IO (\<lambda>_. None) io = True\<close>
proof (cases io)
  case (Inp p x)
  then show ?thesis
    by (cases p) auto
next
  case (Out p x)
  then show ?thesis
    by (cases p) auto
qed

lemma lfilter_visible_IO_None: \<open>lfilter (visible_IO (\<lambda>_. None)) lxs = lxs\<close>
  unfolding visible_IO_None_True by simp

lemma traced_causal_None: \<open>traced op1 lxs \<Longrightarrow> traced op2 lys \<Longrightarrow> causal (\<lambda>_. None) buf lxs lys\<close>
proof (coinduction arbitrary: lxs lys op1 op2 buf)
  case (causal lxs lys op1 op2 buf)
  then show ?case
    apply (cases lxs; cases lys; simp add: comp_def)
    by (smt (verit, del_insts) llist.distinct(1) llist.inject traced.cases)+
qed

lemma traced_pcomp_op': "traced (pcomp_op op1 op2) lxs \<longleftrightarrow>
  traced op1 (lfocusl lxs) \<and> traced op2 (lfocusr lxs) \<and>
  lxs = lalternate (lmap (map_IO Inl Inl id) (lfocusl lxs)) (lmap (map_IO Inr Inr id) (lfocusr lxs))"
  unfolding pcomp_op_def traced_comp_op lfilter_visible_IO_None
  by (auto simp: lfilter_lfilter lfocus_Inl_lmap lfocus_Inr_lmap intro: traced_causal_None)

section\<open>Sequential composition\<close>

lemma traced_inputs: "x \<in> lset lxs \<Longrightarrow> p \<in> set1_IO x \<Longrightarrow> traced op lxs \<Longrightarrow> p \<in> inputs op"
  apply (induct x lxs arbitrary: op rule: llist.set_induct)
  apply (erule traced.cases; auto)
  apply (erule traced.cases; auto)
  done

lemma traced_outputs: "x \<in> lset lxs \<Longrightarrow> p \<in> set2_IO x \<Longrightarrow> traced op lxs \<Longrightarrow> p \<in> outputs op"
  apply (induct x lxs arbitrary: op rule: llist.set_induct)
  apply (erule traced.cases; auto)
  apply (erule traced.cases; auto)
  done


lemma traced_map_op: "inj_on f (inputs op) \<Longrightarrow> inj_on g (outputs op) \<Longrightarrow>
  traced (map_op f g op) lxs \<longleftrightarrow> (\<exists>lys. traced op lys \<and> lxs = lmap (map_IO f g id) lys)"
  apply safe
  subgoal
    apply (rule exI[of _ "lmap (\<lambda>io. map_IO (the_inv_into (inputs op) f) (the_inv_into (outputs op) g) id io) lxs"] conjI)+
    apply (coinduction arbitrary: op lxs)
    subgoal for op lys
      apply (cases op)
      apply (auto simp: observation.map_ident the_inv_into_f_f image_iff traced_inputs traced_outputs
          inj_on_def cong: llist.map_cong IO.map_cong)
      apply (intro exI conjI)
      apply (rule llist.map_cong[OF refl])
      apply (rule IO.map_cong[OF refl])
      apply (rule the_inv_into_f_eq; (auto simp: inj_on_def intro!: f_the_inv_into_f)?)
      apply (metis (no_types, lifting) op.set_map(1) traced_inputs)
      apply (drule spec, erule notE, rule the_inv_into_into; auto simp: inj_on_def)
      apply (metis (no_types, lifting) op.set_map(1) traced_inputs)
      apply (rule the_inv_into_f_eq; (auto simp: inj_on_def intro!: f_the_inv_into_f)?)
      apply (metis (no_types, lifting) op.set_map(2) traced_outputs)
      apply (rule exI, rule the_inv_into_into; auto simp: inj_on_def)
      apply (metis (no_types, lifting) op.set_map(2) traced_outputs)
      apply (rule refl)
      apply assumption
      apply (intro exI conjI)
      apply (rule llist.map_cong[OF refl])
      apply (rule IO.map_cong[OF refl])
      apply (rule refl)
      apply (rule the_inv_into_f_eq; (auto simp: inj_on_def intro!: f_the_inv_into_f)?)
      apply (metis (no_types, lifting) op.set_map(2) traced_outputs)
      apply (erule notE, rule the_inv_into_into; auto simp: inj_on_def)
      apply (metis (no_types, lifting) op.set_map(2) traced_outputs)
      apply (rule refl)
      apply assumption
      done
    apply (auto simp: llist.map_comp IO.map_comp o_def op.set_map f_the_inv_into_f
        intro!: trans[OF llist.map_cong llist.map_ident, symmetric]
        trans[OF IO.map_cong IO.map_ident]
        dest: traced_inputs traced_outputs)
    done
  subgoal for lys
    apply hypsubst_thin
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (coinduction arbitrary: op lys)
    subgoal for op lys
      by (cases op) (auto 0 3 simp: observation.map_id)
    done
  done

definition "scomp_op op1 op2 = map_op projl projr (comp_op Some (\<lambda>_. BEmpty) op1 op2)"

lemma inputs_scomp_op[simp]:
  "inputs (scomp_op op1 op2) \<subseteq> inputs op1"
  unfolding scomp_op_def by (auto simp: op.set_map ran_def dest: inputs_comp_op)

lemma outputs_scomp_op[simp]:
  "outputs (scomp_op op1 op2) \<subseteq> outputs op2"
  unfolding scomp_op_def by (auto simp: op.set_map ran_def dest: outputs_comp_op)

coinductive scausal where
  "scausal (BTL p buf) ios1 ios2 \<Longrightarrow> y = BHD p buf \<Longrightarrow> scausal buf (LCons (Inp q x) ios1) (LCons (Inp p y) ios2)"
| "scausal buf ios1 ios2 \<Longrightarrow> scausal buf (LCons (Inp q x) ios1) (LCons (Out p y) ios2)"
| "scausal (BTL p (BENQ p' x buf)) ios1 ios2 \<Longrightarrow> y = BHD p (BENQ p' x buf) \<Longrightarrow> scausal buf (LCons (Out p' x) ios1) (LCons (Inp p y) ios2)"
| "scausal (BENQ p' x buf) ios1 ios2 \<Longrightarrow> scausal buf (LCons (Out p' x) ios1) (LCons (Out p y) ios2)"
| "scausal buf ios1 LNil"
| "scausal (BTL p (bend o buf)) LNil ios2 \<Longrightarrow> y = BHD p (bend o buf) \<Longrightarrow> scausal buf LNil (LCons (Inp p y) ios2)"
| "scausal (bend o buf) LNil ios2 \<Longrightarrow> scausal buf LNil (LCons (Out p y) ios2)"

lemma scausal_causal: "scausal buf ios1 ios2 \<Longrightarrow> causal Some buf ios1 ios2"
  by (coinduction arbitrary: buf ios1 ios2) (erule scausal.cases; auto simp: ran_def)

lemma causal_scausal: "causal Some buf ios1 ios2 \<Longrightarrow> scausal buf ios1 ios2"
  by (coinduction arbitrary: buf ios1 ios2) (erule causal.cases; auto simp: ran_def)

lemma causal_Some_eq_scausal: "causal Some = scausal"
  by (auto simp: fun_eq_iff causal_scausal scausal_causal)

lemma visible_IO_Some: "visible_IO Some = case_IO (\<lambda>p _. isl p) (\<lambda>p _. \<not> isl p)"
  by (auto simp: ran_def fun_eq_iff split: IO.splits sum.splits)

lemma traced_scomp_op: "traced (scomp_op op1 op2) ios \<longleftrightarrow> 
  (\<exists>ios1 ios2. traced op1 ios1 \<and> traced op2 ios2 \<and> scausal (\<lambda>_. BEmpty) ios1 ios2 \<and>
    ios = lmap (map_IO projl projr id)
        (lfilter (case_IO (\<lambda>p _. isl p) (\<lambda>p _. \<not> isl p))
          (lalternate (lmap (map_IO Inl Inl id) ios1)
            (lmap (map_IO Inr Inr id) ios2))))"
  unfolding scomp_op_def
  apply (subst traced_map_op)
  apply (auto simp add: inj_on_def op.set_map ran_def dest!: inputs_comp_op outputs_comp_op) [2]
  apply (subst traced_comp_op)
  apply (auto simp: causal_Some_eq_scausal visible_IO_Some)
  done

lemma map_IO_alt: "map_IO f g id = case_IO (Inp o f) (Out o g)"
  by (auto simp: fun_eq_iff observation.map_id split: IO.splits)

lemma lproject_lmap: 
  "lproject R S (lmap (map_IO f g id) lxs) =
   lproject (\<lambda>x y. R x (f y)) (\<lambda>x y. S x (g y)) lxs"
  unfolding lproject_def
  apply (auto simp: fun_eq_iff lfilter_lmap llist.map_comp map_IO_alt)
  apply (smt (verit) IO.case_eq_if IO.distinct(1) IO.sel(1) IO.sel(2) IO.sel(4) IO.simps(6) IO.split_sel_asm comp_apply data_def le_boolD le_boolI' lfilter_cong llist.map_cong observation.case_eq_if)
  done

lemma lproject_lfilter: "lproject R S (lfilter (case_IO (\<lambda>p _. P p) (\<lambda>p _. Q p)) lxs) = lproject (\<lambda>x y. R x y \<and> P y) (\<lambda>x y. S x y \<and> Q y) lxs"
  unfolding lproject_def lfilter_lfilter
  by (auto simp: fun_eq_iff intro!: llist.map_cong lfilter_cong split: IO.splits observation.splits)

lemma lproject_eq_lfocusl: 
  "lproject (\<lambda>x y. x = projl y \<and> isl y) (\<lambda>x y. False) lxs = lproject (=) \<bottom> (lfocusl lxs)"
  unfolding lproject_def lfocus_def
  apply (auto simp: lfilter_lmap fun_eq_iff llist.map_comp map_IO_alt lfilter_lfilter o_def)
  apply (smt (verit) IO.case_eq_if IO.distinct(1) IO.sel(1) IO.sel(2) IO.sel(4) IO.sel(5) IO.split_sel_asm data_def image_iff le_boolE le_boolI' lfilter_cong llist.map_cong observation.case_eq_if rangeI sum.collapse(1) sum.disc(1))
  done

lemma lproject_eq_lfocusr: 
  "lproject (\<lambda>x y. False) (\<lambda>x y. x = projr y \<and> \<not> isl y) lxs = lproject \<bottom> (=) (lfocusr lxs)"
  unfolding lproject_def lfocus_def
  apply (auto simp: lfilter_lmap fun_eq_iff llist.map_comp map_IO_alt lfilter_lfilter o_def)
  apply (smt (verit) IO.case_eq_if IO.disc_eq_case(1) IO.distinct(1) IO.sel(4) IO.simps(2) IO.split_sel_asm image_iff isl_def le_boolD le_boolI' lfilter_cong llist.map_cong observation.case_eq_if rangeI sum.exhaust_sel sum.simps(4))
  done

(*likely only one direction holds*)
(*
lemma "history (scomp_op op1 op2) lxs lys \<longleftrightarrow>
  (\<exists>lzs. history op1 lxs lzs \<and> history op2 lzs lys)"
  unfolding history_def traced_scomp_op
  apply safe
  subgoal for ios ios1 ios2
    apply (rule exI conjI | assumption)+
    unfolding lproject_lmap lproject_lfilter bot_fun_def bot_bool_def simp_thms
      lproject_eq_lfocusl lproject_eq_lfocusr lfocus_Inl_lmap lfocus_Inr_lmap
      apply assumption
     apply (rule refl)
    apply (rule exI conjI allI | assumption)+
    subgoal premises prems for p
      sorry
    apply (rule refl)
    done
  subgoal for lzs ios1 ios2
    apply (rule exI conjI | assumption)+
    subgoal premises prems
      using prems(4)
      sorry
    apply (rule refl conjI)+
    unfolding lproject_lmap lproject_lfilter bot_fun_def bot_bool_def simp_thms
      lproject_eq_lfocusl lproject_eq_lfocusr lfocus_Inl_lmap lfocus_Inr_lmap
     apply assumption
    apply (rule TrueI)
    done
  done
*)

end *)