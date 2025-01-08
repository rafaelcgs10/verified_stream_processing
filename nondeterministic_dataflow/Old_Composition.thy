section \<open>The composition operator\<close>

theory Old_Composition

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
  sorry

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


abbreviation "read_or_write \<equiv> Choice {| Read (1::2) (\<lambda> _. end_op), Write (Read (2::2) (\<lambda> _. end_op)) (1::1) (1::nat) |}"

lemma choices_read_or_write[simp]:
  "choices read_or_write = {| Read (1::2) (\<lambda> _. end_op), Write (Read (2::2) (\<lambda> _. end_op)) (1::1) (1::nat) |}"
  by (auto simp del: cimage_cinsert)

lemma cUnion_cinsert[simp]:
  "cUnion (cinsert x A) = cUn x (cUnion A)"
  apply (subst (3 8) cset.map_id[symmetric])
  apply fastforce
  done

lemma
  "read_or_write \<bullet> ((end_op :: (1, 1, nat) op) \<bullet> (Write end_op (1::1) 1)) ~ 
   read_or_write \<bullet> (end_op :: (1, 1, nat) op) \<bullet> (Write end_op (1::1) 1) \<Longrightarrow> False"
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
    apply simp
   apply (rule refl)
  apply (erule thin_rl)
  apply simp
  apply (elim exE conjE)
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