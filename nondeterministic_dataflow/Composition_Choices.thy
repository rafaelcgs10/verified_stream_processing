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

lemma comp_op_not_Read[simp]:
  "\<not> is_Read (comp_op wire buf op1 op2)"
  by (subst comp_op_code, simp)
lemma comp_op_not_Write[simp]:
  "\<not> is_Write (comp_op wire buf op1 op2)"
  by (subst comp_op_code, simp)

section \<open>Properties of the (general) composition\<close>

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

lemma step_Tau_comp_op_L:
  "step (Out p x) op1 op1' \<Longrightarrow>
   wire p = Some q \<Longrightarrow>
   step Tau (comp_op wire buf op1 op2) (comp_op wire (BENQ q x buf) op1' op2)"
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

lemma step_comp_op_R:
  "step io op2 op2' \<Longrightarrow>
   (case io of Out p x \<Rightarrow> True | Inp p x \<Rightarrow> p \<notin> ran wire | Tau \<Rightarrow> True) \<Longrightarrow>
   step (map_IO Inr Inr id io) (comp_op wire buf op1 op2)(comp_op wire buf op1 op2')"
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

lemma step_Tau_comp_op_R:
  "step (Inp p x) op2 op2' \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow>
   buf p \<noteq> [] \<Longrightarrow>
   BHD p buf = x \<Longrightarrow>
   step Tau (comp_op wire buf op1 op2) (comp_op wire (BTL p buf) op1 op2')"
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

lemma step_comp_op_R_Out[intro]:
  "step (Out p x) op2 op2' \<Longrightarrow> step (Out (Inr p) x) (comp_op wire buf op1 op2) (comp_op wire buf op1 op2')"
  using step_comp_op_R by force

lemma step_comp_op_R_Inp[intro]:
  "step (Inp p x) op2 op2' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> step (Inp (Inr p) x) (comp_op wire buf op1 op2) (comp_op wire buf op1 op2')"
  using step_comp_op_R by fastforce

lemma step_comp_op_R_Tau[intro]:
  "step Tau op2 op2' \<Longrightarrow> step Tau (comp_op wire buf op1 op2) (comp_op wire buf op1 op2')"
  using step_comp_op_R by force

lemma step_comp_op_L_Inp[intro]:
  "step (Inp p x) op1 op1' \<Longrightarrow> step (Inp (Inl p) x) (comp_op wire buf op1 op2) (comp_op wire buf op1' op2)"
  using step_comp_op_L by force

lemma step_comp_op_L_Out[intro]:
  "step (Out p x) op1 op1' \<Longrightarrow> p \<notin> dom wire \<Longrightarrow> step (Out (Inl p) x) (comp_op wire buf op1 op2) (comp_op wire buf op1' op2)"
  using step_comp_op_L
  by (metis IO.map_id IO.simps(10) IO.simps(16))

lemma step_comp_op_L_Tau[intro]:
  "step Tau op1 op1' \<Longrightarrow> step Tau (comp_op wire buf op1 op2) (comp_op wire buf op1' op2)"
  using step_comp_op_L by force

section \<open>Parallel composition operator\<close>
no_notation Sublist.parallel (infixl "\<parallel>" 50)

definition pcomp_op (infixl "\<parallel>" 64) where
  "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. [])"

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

section \<open>Sequential composition operator\<close>
definition scomp_op (infixl "\<bullet>" 65) where
  "scomp_op op1 op2 = map_op projl projr (comp_op Some (\<lambda>_. []) op1 op2)"

subsection \<open>Congruence for strong bisim\<close>
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
              apply (simp add: fun_upd_def)
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
             apply simp
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

subsection \<open>Congruence for weak bisim (wbisim)\<close>

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
                 apply simp
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
                 apply simp
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

end