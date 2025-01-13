section \<open>The composition operator\<close>

theory Composition_Choices

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
  | Silent_aux "('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op"

abbreviation eval_comp_op_aux where
  "eval_comp_op_aux c aux \<equiv> (case aux of
    Read_aux p f \<Rightarrow> Read p (\<lambda>y. let (buf, op1, op2) = f y in c buf op1 op2)
  | Write_aux (buf, op1, op2) q x \<Rightarrow> Write (c buf op1 op2) q x
  | Silent_aux (buf, op1, op2) \<Rightarrow> Silent (c buf op1 op2))"

abbreviation "sound_reads wire buf \<equiv> cfilter (\<lambda> op. case op of Read p f \<Rightarrow> p \<notin> ran wire \<or> buf p \<noteq> [] | _ \<Rightarrow> True)"

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
     (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (Silent (comp_op wire (buf(p2 := btl (buf p2))) (Read p1 f1) (f2 (BHD p2 buf)))))
      else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Read p1 f1) (f2 y)))))"
  "comp_op wire buf (Read p1 f1) (Write op2 q2 x2) =
    choice2 (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Write op2 q2 x2))) (Write (comp_op wire buf (Read p1 f1) op2) (Inr q2) x2)"
  "comp_op wire buf (Read p1 f1) (Choice op2s) = 
    Choice (cinsert (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Choice op2s))) (cimage
       (case_op (\<lambda>p f. if p \<in> ran wire then Silent (comp_op wire (buf(p := btl (buf p))) (Read p1 f1) (f (BHD p buf))) else Read (Inr p) (\<lambda>x. comp_op wire buf (Read p1 f1) (f x)))
         (\<lambda>op p. Write (comp_op wire buf (Read p1 f1) op) (Inr p)) (\<lambda> op. undefined) (\<lambda>op. Silent (comp_op wire buf (Read p1 f1) op)))
       (sound_reads wire buf (cUnion (cimage choices op2s)))))"
  "comp_op wire buf (Write op1 q1 x1) (Read p2 f2) =
    Choice (cinsert (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Read p2 f2)) (Inl q1) x1
      | Some q \<Rightarrow> Silent (comp_op wire (buf(q := benq x1 (buf q))) op1 (Read p2 f2)))
      (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (Silent (comp_op wire (buf(p2 := btl (buf p2))) (Write op1 q1 x1) (f2 (BHD p2 buf)))))
        else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Write op1 q1 x1) (f2 y)))))"
  "comp_op wire buf (Write op1 q1 x1) (Write op2 q2 x2) =
    choice2 (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Write op2 q2 x2)) (Inl q1) x1
      | Some q \<Rightarrow> Silent (comp_op wire (buf(q := benq x1 (buf q))) op1 (Write op2 q2 x2)))
      (Write (comp_op wire buf (Write op1 q1 x1) op2) (Inr q2) x2)"
  "comp_op wire buf (Write op1 q1 x1) (Choice op2s) =
     Choice (cinsert (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Choice op2s)) (Inl q1) x1
      | Some q \<Rightarrow> Silent (comp_op wire (buf(q := benq x1 (buf q))) op1 (Choice op2s)))
      (cimage
       (case_op (\<lambda>p f. if p \<in> ran wire then Silent (comp_op wire (buf(p := btl (buf p))) (Write op1 q1 x1) (f (BHD p buf))) else Read (Inr p) (\<lambda>x. comp_op wire buf (Write op1 q1 x1) (f x)))
         (\<lambda>op p. Write (comp_op wire buf (Write op1 q1 x1) op) (Inr p)) (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf (Write op1 q1 x1) op)))
       (sound_reads wire buf (cUnion (cimage choices op2s)))))"
  "comp_op wire buf (Choice op1s) (Read p2 f2) =
    Choice (cUn (if p2 \<in> ran wire then (if buf p2 = [] then cempty else csingle (Silent (comp_op wire (buf(p2 := btl (buf p2))) (Choice op1s) (f2 (BHD p2 buf)))))
        else csingle (Read (Inr p2) (\<lambda>y. comp_op wire buf (Choice op1s) (f2 y)))) (cimage
       (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Read p2 f2)))
         (\<lambda>op p x. case wire p of None \<Rightarrow> Write (comp_op wire buf op (Read p2 f2)) (Inl p) x | Some q \<Rightarrow> Silent (comp_op wire (buf(q := benq x (buf q))) op (Read p2 f2))) (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf op (Read p2 f2))))
       (cUnion (cimage choices op1s))))"
  "comp_op wire buf (Choice op1s) (Write op2 q2 x2) =
    Choice (cinsert (Write (comp_op wire buf (Choice op1s) op2) (Inr q2) x2) (cimage
       (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Write op2 q2 x2)))
         (\<lambda>op p x. case wire p of None \<Rightarrow> Write (comp_op wire buf op (Write op2 q2 x2)) (Inl p) x | Some q \<Rightarrow> Silent (comp_op wire (buf(q := benq x (buf q))) op (Write op2 q2 x2))) (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf op (Write op2 q2 x2))))
       (cUnion (cimage choices op1s))))"
  "comp_op wire buf (Choice op1s) (Choice op2s) =
    Choice (cUn (cimage
             (case_op (\<lambda>p f. Read (Inl p) (\<lambda>x. comp_op wire buf (f x) (Choice op2s)))
               (\<lambda>op p x.
                   case wire p of None \<Rightarrow> Write (comp_op wire buf op (Choice op2s)) (Inl p) x
                   | Some q \<Rightarrow> Silent (comp_op wire (buf(q := benq x (buf q))) op (Choice op2s)))
               (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf op (Choice op2s))))
             (cUnion (cimage choices op1s)))
        (cimage
          (case_op
            (\<lambda>p f. if p \<in> ran wire then Silent (comp_op wire (buf(p := btl (buf p))) (Choice op1s) (f (BHD p buf)))
                   else Read (Inr p) (\<lambda>x. comp_op wire buf (Choice op1s) (f x)))
            (\<lambda>op p. Write (comp_op wire buf (Choice op1s) op) (Inr p)) (\<lambda>a. undefined) (\<lambda>op. Silent (comp_op wire buf (Choice op1s) op)))
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
      apply (smt (verit) not_Some_eq option.simps(4) step.intros(2))
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

lemma step_comp_op_R:
  "step io op2 op2' \<Longrightarrow>
   (case io of Out p x \<Rightarrow> True | Inp p x \<Rightarrow> p \<notin> ran wire | Tau \<Rightarrow> True) \<Longrightarrow>
   step (map_IO Inr Inr id io)  (comp_op wire buf op1 op2)(comp_op wire buf op1 op2')"
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
      apply (meson step.intros(1))
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
      apply (meson step.intros(2))
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
  "read_or_write \<bullet> ((end_op :: (1, 1, nat) op) \<bullet> (Write end_op (1::1) 1)) ~ read_or_write \<bullet> (end_op :: (1, 1, nat) op) \<bullet> (Write end_op (1::1) 1)"
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def scomp_op_def
  apply auto
  subgoal
    apply (intro exI conjI)
     apply (rule SC)
      apply (rule cinsertI2)
      apply (rule cinsertI2)
      apply (rule cinsertI1)
     apply (rule ST)
    apply (rule bc_bisim)
    subgoal 
      apply (coinduction rule: bisim_coinduct_upto)
      unfolding sim_def
      apply auto
      subgoal
        using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
      subgoal
        using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
      subgoal
        apply (intro exI conjI)
         apply (rule SC)
          apply (rule cinsertI2)
          apply force
         apply (rule step_map_op)
          apply (rule SW)
         apply simp
        subgoal
          using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
        done
      subgoal
        using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
      done
    done
  subgoal
    using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
  subgoal
    using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
  subgoal
    apply (intro exI conjI)
     apply (rule SC)
      apply (rule cinsertI2)
      apply (rule cinsertI2)
      apply force
     apply (rule step_map_op)
      apply (rule SW)
     apply simp
    subgoal
      using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
    done
  subgoal
    using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
  subgoal
    apply (intro exI conjI)
     apply (rule SC)
      apply (rule cinsertI1)
     apply (rule ST)
    apply (rule bc_bisim)
    apply (coinduction rule: bisim_coinduct_upto)
    unfolding sim_def
    apply auto
    subgoal
      apply (intro exI conjI)
       apply (rule SC)
        apply (rule cinsertI2)
        apply simp
        apply force
       apply (rule step_map_op)
        apply (rule SW)
       apply simp
      apply (rule bc_bisim)
      apply (coinduction rule: bisim_coinduct_upto)
      unfolding sim_def
      apply (force intro: step_map_op step.intros bc_refl)
      done
    subgoal
      using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
    subgoal
      using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
    subgoal
      using bisim_coinduct_upto by (force intro: step_map_op step.intros bc_refl)
    done
  done

lemma choices_id_op[simp]:
  "choices (id_op buf) = cinsert (Silent (id_op buf))
     (cUn (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda>x. id_op (buf(p := bulk_benq [x] (buf p))))) cUNIV)))
       (cUnion (cimage choices (cimage (\<lambda>p. Write (id_op (buf(p := btl (buf p)))) p (BHD p buf)) (cfilter (\<lambda>p. buf p \<noteq> []) cUNIV)))))"
  apply (subst id_op_code)
  apply simp
  done

lemma step_comp_op_Some_id_op_id_op:
  "step io (comp_op Some buf2 op1 op2) op \<Longrightarrow>
   op1 = id_op buf1 \<Longrightarrow>
   op2 = id_op buf3 \<Longrightarrow>
   (\<exists> p x. io = Inp (Inl p) x \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some buf2' (id_op (BENQ p x buf1')) (id_op buf3') \<and>
      buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3')) \<or>

   (\<exists> p x. io = Out (Inr p) x \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some buf2' (id_op buf1') (id_op (BTL p buf3')) \<and> BHD p buf3' = x \<and> buf3' p \<noteq> [] \<and>
     buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3')) \<or>

   (io = Tau \<and> op = comp_op Some buf2 op1 op2) \<or>
   (\<exists> p x. io = Tau \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some (BTL p buf2') (id_op buf1') (id_op (BENQ p x buf3')) \<and> BHD p buf2' = x \<and> buf2' p \<noteq> [] \<and>
     buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3')) \<or>

   (\<exists> p x. io = Tau \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some (BENQ p x buf2') (id_op (BTL p buf1')) (id_op buf3') \<and> BHD p buf1' = x \<and> buf1' p \<noteq> [] \<and>
     buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3'))"
  apply (induction io "comp_op Some buf2 op1 op2" op arbitrary: op1 op2 buf1 buf2 buf3 rule: step.induct)
  subgoal
    apply hypsubst_thin
    apply (subst (asm) comp_op_code)
    apply auto
    done
  subgoal
    apply hypsubst_thin
    apply (subst (asm) comp_op_code)
    apply auto
    done
  subgoal
    apply hypsubst_thin
    apply (subst (asm) comp_op_code)
    apply auto
    done
  subgoal for op ops io op' op1 op2 buf2 buf1 buf3
    apply hypsubst_thin
    apply (subst (asm) (7) comp_op_code)
    apply (auto 0 0)
                     apply blast+
    done
  done

lemma id_id_gen:
  "map_op projl projr (comp_op Some buf2 (id_op buf1) (id_op buf3)) ~ id_op (buf1 >> buf2 >> buf3)"
  apply (coinduction arbitrary: buf1 buf2 buf3 rule: bisim_coinduct_upto)
  subgoal for buf1 buf2 buf3
    unfolding sim_def
    apply auto
    subgoal for io op
      apply (drule step_map_op_inv)
      apply safe
      apply hypsubst_thin
      subgoal for io' op'
        apply (drule step_comp_op_Some_id_op_id_op)
          apply (rule refl)+
        apply simp
        apply (elim disjE exE conjE)
        subgoal for p x buf1' buf2' buf3'
          apply hypsubst_thin
          apply (intro conjI exI)
           apply (subst id_op_code)
           apply (rule SC[rotated])
            apply simp
            apply (rule SR)
           apply (rule cinsertI2)
           apply simp
           apply (rule disjI1)
           apply (rule image_eqI)
            apply (rule refl)
           apply simp
          apply (rule bc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply (rule ext)
          apply simp
          apply metis
          done
        subgoal for p x buf1' buf2' buf3'
          apply hypsubst_thin
          apply simp
          apply (intro conjI exI)
           apply (subst id_op_code)
           apply (rule SC[rotated])
            apply (rule SW)
           apply (rule cinsertI2)
           apply simp
           apply (rule disjI2)
           apply (rule image_eqI)
            apply force
           apply (simp add: cUNIV.rep_eq)
          apply (rule bc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply (rule ext)
          apply simp
          done
        subgoal
          apply hypsubst_thin
          apply (intro conjI exI)
           apply (subst id_op_code)
           apply (rule SC[rotated])
            apply simp
            apply (rule ST)
           apply simp
           apply (rule disjI1)
           apply (rule refl)
          apply (rule bc_base)
          apply force
          done
        subgoal for p buf1' buf2' buf3'
          apply hypsubst_thin
          apply (intro conjI exI)
           apply (subst id_op_code)
           apply (rule SC[rotated])
            apply simp
            apply (rule ST)
           apply simp
           apply (rule disjI1)
           apply (rule refl)
          apply (rule bc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply (rule ext)
          apply simp
          done
        subgoal for p buf1' buf2' buf3'
          apply hypsubst_thin
          apply (intro conjI exI)
           apply (subst id_op_code)
           apply (rule SC[rotated])
            apply simp
            apply (rule ST)
           apply simp
           apply (rule disjI1)
           apply (rule refl)
          apply (rule bc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply (rule ext)
          apply simp
          done
        done
      done
    subgoal for io op1'
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
           apply (rule SC)
            apply (simp add: Set.filter_def)
            apply (rule disjI2)
            apply simp
            apply (rule disjI1)
            apply (rule image_eqI)
             apply (rule refl)
            apply simp
            apply (rule disjI1)
            apply (intro exI)
            apply (rule refl)
           apply simp_all
          apply (rule SR)
          done
        subgoal
          apply (rule bc_sym)
          apply (rule bc_base)
          apply (intro conjI exI)
           apply simp_all
          apply (rule arg_cong[where f=id_op])
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
        apply (elim exE disjE conjE)
        subgoal
          apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op buf1) (id_op (BTL p buf3)))"])
          apply (intro conjI)
          subgoal
            apply (rule step_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
             apply (subst comp_op_code)
             apply simp
             apply (rule SC)
              apply (simp add: Set.filter_def)
              apply (rule disjI2)
              apply simp
              apply (rule disjI2)
              apply (rule image_eqI)
               apply (rule refl)
              apply (simp add: cUNIV.rep_eq)
              apply (intro conjI)
               apply (rule disjI2)
               apply (rule disjI2)
               apply (intro conjI exI)
                apply assumption
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
            apply (rule SC)
             apply simp
             apply (rule disjI2)+
             apply (rule image_eqI)
              apply (rule refl)
             apply (simp add: Set.filter_def cUNIV.rep_eq)
              apply (intro conjI)
               apply (rule disjI2)
               apply (rule disjI1)
            apply (intro conjI exI)
               apply simp_all
             apply force
            apply simp
           


end
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

end