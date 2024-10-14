section \<open>The composition operator\<close>

theory Composition

imports
  Operator
begin

abbreviation "safe_choice_stop stop f ops \<equiv> (if ops = cempty then stop else Choice (cimage f ops))"
abbreviation "safe_choice f \<equiv> safe_choice_stop (f End) f"
abbreviation "safe_choice2 f op1s op2s \<equiv> (if op1s = cempty \<and> op2s = cempty then End
  else if op1s = cempty then Choice (cimage (f End) op2s)
  else if op2s = cempty then Choice (cimage (\<lambda>op1. f op1 End) op1s)
  else Choice (cimage (case_prod f) (cproduct op1s op2s)))"
abbreviation "choice2 op1 op2 \<equiv> Choice (cimage (\<lambda>b. if b then op1 else op2) (cinsert True (csingle False)))"
abbreviation "safe_read f x \<equiv> (case x of None \<Rightarrow> End | Some x \<Rightarrow> f x)"

inductive comp_producing :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow> ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> nat \<Rightarrow> bool" for wire where
  "comp_producing wire buf (Choice op1s) (Choice op2s) 0"
| "comp_producing wire buf (Read p1 f1) (Choice op2s) 0"
| "wire p1 = None \<or> op2s \<noteq> cempty \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) (Choice op2s) 0"
| "wire p1 = Some p \<Longrightarrow> comp_producing wire (BENQ p x1 buf) op1' End n \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) End (Suc n)"
| "comp_producing wire buf (Choice op1s) (Write op2' p2 x2) 0"
| "comp_producing wire buf (Read p1 f1) (Write op2' p2 x2) 0"
| "comp_producing wire buf (Write op1' p1 x1) (Write op2' p2 x2) 0"
| "p2 \<notin> ran wire \<or> op1s \<noteq> cempty \<Longrightarrow> comp_producing wire buf (Choice op1s) (Read p2 f2) 0"
| "p2 \<in> ran wire \<Longrightarrow> comp_producing wire (BTL p2 (bend o buf)) End (safe_read f2 (BHD p2 (bend o buf))) n \<Longrightarrow> comp_producing wire buf End (Read p2 f2) (Suc n)"
| "comp_producing wire buf (Read p1 f1) (Read p2 f2) 0"
| "p2 \<notin> ran wire \<or> wire p1 = None \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) 0"
| "p2 \<in> ran wire \<Longrightarrow> wire p1 = Some p \<Longrightarrow>
    comp_producing wire (BTL p2 (BENQ p x1 buf)) op1' (safe_read f2 (BHD p2 (BENQ p x1 buf))) n \<Longrightarrow>
    comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) (Suc n)"

inductive_cases comp_producing_WriteEndE: "comp_producing wire buf (Write op p x) (Choice op2s) n"
inductive_cases comp_producing_ReadEndE: "comp_producing wire buf (Read p f) (Choice op2s) n"
inductive_cases comp_producing_ReadWriteE: "comp_producing wire buf (Read p f) (Write op p' x)  n"
inductive_cases comp_producing_EndEndE: "comp_producing wire buf (Choice op1s) (Choice op2s) n"
inductive_cases comp_producing_End2E: "comp_producing wire buf op (Choice op2s) n"

lemma comp_producing_inject: "comp_producing wire buf op1 op2 i \<Longrightarrow> comp_producing wire buf op1 op2 j \<Longrightarrow> i = j"
proof (induct buf op1 op2 i arbitrary: j rule: comp_producing.induct)
  case (4 p1 p x1 buf op1' n)
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

datatype (discs_sels) ('ip1, 'ip2, 'op1, 'op2, 'd) comp_op_aux =
  Read_aux "'ip1 + 'ip2" "'d observation \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op"
| Write_aux "('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op" "'op1 + 'op2" 'd
| Base_aux "(('ip2 \<Rightarrow> 'd buf) \<times> ('ip1, 'op1, 'd) op \<times> ('ip2, 'op2, 'd) op)"

abbreviation eval_comp_op_aux where
  "eval_comp_op_aux c aux \<equiv> (case aux of
    Read_aux p f \<Rightarrow> Read p (\<lambda>y. let (buf, op1, op2) = f y in c buf op1 op2)
  | Write_aux (buf, op1, op2) q x \<Rightarrow> Write (c buf op1 op2) q x
  | Base_aux (buf, op1, op2) \<Rightarrow> c buf op1 op2)"

corec comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op" where
  "comp_op wire buf op1 op2 =
     Choice (cimage (eval_comp_op_aux (comp_op wire)) (cUn (case op1 of
       Read p f \<Rightarrow> csingle (Read_aux (Inl p) (\<lambda>y. (buf, f y, op2)))
     | Write op p x \<Rightarrow> csingle (case wire p of
         None \<Rightarrow> Write_aux (buf, op, op2) (Inl p) x
       | Some q \<Rightarrow> Base_aux (BENQ q x buf, op, op2))
     | Choice ops \<Rightarrow> cimage (\<lambda>op. Base_aux (buf, op, op2)) ops)
     (case op2 of
       Read p f \<Rightarrow> csingle (if p \<in> ran wire then Base_aux (BTL p buf, op1, safe_read f (BHD p buf))
         else Read_aux (Inr p) (\<lambda>y. (buf, op1, f y)))
     | Write op p x \<Rightarrow> csingle (Write_aux (buf, op1, op) (Inr p) x)
     | Choice ops \<Rightarrow> cimage (\<lambda>op. Base_aux (buf, op1, op)) ops)))"

lemma comp_op_code: "comp_op wire buf op1 op2 =
     Choice (cUn (case op1 of
       Read p f \<Rightarrow> csingle (Read (Inl p) (\<lambda>y. comp_op wire buf (f y) op2))
     | Write op p x \<Rightarrow> csingle (case wire p of
         None \<Rightarrow> Write (comp_op wire buf op op2) (Inl p) x
       | Some q \<Rightarrow> comp_op wire (BENQ q x buf) op op2)
     | Choice ops \<Rightarrow> cimage (\<lambda>op. comp_op wire buf op op2) ops)
     (case op2 of
       Read p f \<Rightarrow> csingle (if p \<in> ran wire then comp_op wire (BTL p buf) op1 (safe_read f (BHD p buf))
         else Read (Inr p) (\<lambda>y. comp_op wire buf op1 (f y)))
     | Write op p x \<Rightarrow> csingle (Write (comp_op wire buf op1 op) (Inr p) x)
     | Choice ops \<Rightarrow> cimage (\<lambda>op. comp_op wire buf op1 op) ops))"
  apply (subst comp_op.code)
  apply (simp add: cset.map_comp o_def cimage_cUn split: comp_op_aux.splits op.splits option.splits)
  done

lemma comp_op_simps[simp]:
  "comp_op wire buf (Read p1 f1) (Read p2 f2) =
    choice2 (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Read p2 f2)))
     (if p2 \<in> ran wire then comp_op wire (buf(p2 := btl (buf p2))) (Read p1 f1) (safe_read f2 (BHD p2 buf))
      else Read (Inr p2) (\<lambda>y. comp_op wire buf (Read p1 f1) (f2 y)))"
  "comp_op wire buf (Read p1 f1) (Write op2 q2 x2) =
    choice2 (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Write op2 q2 x2))) (Write (comp_op wire buf (Read p1 f1) op2) (Inr q2) x2)"
  "comp_op wire buf (Read p1 f1) (Choice op2s) = 
    Choice (cinsert (Read (Inl p1) (\<lambda>y. comp_op wire buf (f1 y) (Choice op2s))) (cimage (comp_op wire buf (Read p1 f1)) op2s))"
  "comp_op wire buf (Write op1 q1 x1) (Read p2 f2) =
    choice2 (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Read p2 f2)) (Inl q1) x1
      | Some q \<Rightarrow> comp_op wire (buf(q := benq x1 (buf q))) op1 (Read p2 f2))
      (if p2 \<in> ran wire then comp_op wire (buf(p2 := btl (buf p2))) (Write op1 q1 x1) (safe_read f2 (BHD p2 buf))
        else Read (Inr p2) (\<lambda>y. comp_op wire buf (Write op1 q1 x1) (f2 y)))"
  "comp_op wire buf (Write op1 q1 x1) (Write op2 q2 x2) =
    choice2 (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Write op2 q2 x2)) (Inl q1) x1
      | Some q \<Rightarrow> comp_op wire (buf(q := benq x1 (buf q))) op1 (Write op2 q2 x2))
      (Write (comp_op wire buf (Write op1 q1 x1) op2) (Inr q2) x2)"
  "comp_op wire buf (Write op1 q1 x1) (Choice op2s) =
     Choice (cinsert (case wire q1 of None \<Rightarrow> Write (comp_op wire buf op1 (Choice op2s)) (Inl q1) x1
      | Some q \<Rightarrow> comp_op wire (buf(q := benq x1 (buf q))) op1 (Choice op2s))
      (cimage (comp_op wire buf (Write op1 q1 x1)) op2s))"
  "comp_op wire buf (Choice op1s) (Read p2 f2) =
    Choice (cinsert (if p2 \<in> ran wire then comp_op wire (buf(p2 := btl (buf p2))) (Choice op1s) (safe_read f2 (BHD p2 buf))
        else Read (Inr p2) (\<lambda>y. comp_op wire buf (Choice op1s) (f2 y))) (cimage (\<lambda>op. comp_op wire buf op (Read p2 f2)) op1s))"
  "comp_op wire buf (Choice op1s) (Write op2 q2 x2) =
    Choice (cinsert (Write (comp_op wire buf (Choice op1s) op2) (Inr q2) x2) (cimage (\<lambda>op. comp_op wire buf op (Write op2 q2 x2)) op1s))"
  "comp_op wire buf (Choice op1s) (Choice op2s) =
    Choice (cUn (cimage (\<lambda>op. comp_op wire buf op (Choice op2s)) op1s)
     (cimage (comp_op wire buf (Choice op1s)) op2s))"
  by (subst comp_op_code; simp add: cinsert_commute)+

definition "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. BEnded)"

fun reassoc where
  "reassoc (Inl (Inl x)) = Inl x"
| "reassoc (Inl (Inr x)) = Inr (Inl x)"
| "reassoc (Inr x) = Inr (Inr x)"

lemma pcomp_op_commute: "pcomp_op op1 op2 = map_op (case_sum Inr Inl) (case_sum Inr Inl) (pcomp_op op2 op1)"
  apply (coinduction arbitrary: op1 op2 rule: op.coinduct_upto)
  subgoal for op1 op2
    unfolding pcomp_op_def
    by (cases op1; cases op2)
      (auto simp add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def intro!: op.cong_Read  op.cong_Write intro: op.cong_base)
  done

(*
lemma
  "stepped (comp_op wire buf op1 op2) io op' \<Longrightarrow>
   bisim op1 op1' \<Longrightarrow>
   bisim op2 op2' \<Longrightarrow>
   \<exists>t'. stepped (comp_op wire buf op1' op2') io t' \<and>
         bisim_cong (\<lambda>s t. \<exists>op1 op1' op2 op2' buf. s = comp_op wire buf op1 op2 \<and> t = comp_op wire buf op1' op2' \<and> bisim op1 op1' \<and> bisim op2 op2') op' t'"
  apply (induct "comp_op wire buf op1 op2" io op' arbitrary: buf op1 op2 op1' op2' rule: stepped.induct)
  apply (subst (asm) comp_op.code; simp)
   apply (subst (asm) comp_op.code; simp)
  subgoal premises prems for op ops l op' buf op1 op2 op1' op2'
    using prems(1,2,4-)
    apply (cases op1; cases op2; simp add: cinsert.rep_eq split: if_splits)
    apply safe
*)

lemma has_mute_Read[simp]:
  "\<not> has_mute (Read p f)"
  by auto

lemma has_mute_Write[simp]:
  "\<not> has_mute (Write op p x)"
  by auto

lemma has_mute_Choice[simp]:
  "has_mute (Choice ops) \<longleftrightarrow> ops = {||} \<or> (\<exists>op. op |\<in>| ops \<and> has_mute op)"
  by (auto)

lemma
  "bisim op1 op1' \<Longrightarrow> bisim op2 op2' \<Longrightarrow>
  has_mute (comp_op wire buf op1 op2) \<Longrightarrow> has_mute (comp_op wire buf op1' op2')"
  apply (coinduction arbitrary: op1 op1' op2 op2' buf)
  apply safe
  apply (erule notE)
  subgoal for op1 op1' op2 op2' buf
    apply (cases op1; cases op1'; cases op2; cases op2')
    apply (simp_all add: cinsert.rep_eq bot_cset.rep_eq conj_disj_distribR ex_disj_distrib cimage.rep_eq cUnion.rep_eq split: if_splits)  
    subgoal
      apply (rule disjI2, rule disjI1)
      apply (rule exI)+
      apply (rule conjI, rule refl)
      apply (rule conjI[rotated])+
        apply assumption
       apply (simp add: bisim_refl option.case_eq_if)
      apply (simp add: bisim_refl option.case_eq_if)
      done
    subgoal
      apply (rule disjI2)
      apply (simp flip: ex_cin_conv)
      apply (erule exE)
      apply (drule spec, drule mp, assumption)
      apply (rule bexI[rotated], assumption)
      apply (rule disjI1)
      apply (rule exI)+
      apply (rule conjI, rule refl)
      apply (rule conjI[rotated])+
        apply assumption
       apply (simp add: bisim_refl option.case_eq_if)
      apply (simp add: bisim_refl option.case_eq_if)
      done

lemma
  "bisim op1 op1' \<Longrightarrow>
   bisim op2 op2' \<Longrightarrow>
   bisim (comp_op wire buf op1 op2) (comp_op wire buf op1' op2')"
  apply (coinduction arbitrary: op1 op1' op2 op2' buf rule: bisim_coinduct_upto)
  subgoal for op1 op1' op2 op2' buf
    apply safe
    subgoal
      apply (coinduction arbitrary: op1 op1' op2 op2' buf)
      apply safe
      apply (erule notE)
      subgoal for op1 op1' op2 op2' buf
        apply (cases op1; cases op1'; cases op2; cases op2')
                            apply (simp_all add: cinsert.rep_eq bot_cset.rep_eq conj_disj_distribR ex_disj_distrib split: if_splits)
                            apply (rule disjI2, rule disjI1)
                            apply (rule exI)+
                            apply (rule conjI, rule refl)
                            apply (rule conjI[rotated])+
                            apply assumption
                            apply (simp add: bisim_refl option.case_eq_if)
                            apply (simp add: bisim_refl option.case_eq_if)
        sorry
      done
end
    subgoal sorry
    subgoal for io op'
      apply (cases op1; cases op1'; cases op2; cases op2')
      apply simp_all
      subgoal for p1 f1 p1' f1' p2 f2 p2' f2'
          apply (auto simp add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def split: if_splits)
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI)
          defer
          apply (rule bc_base)
          apply (intro exI conjI)
          defer
          apply (rule refl)
         


end
      apply simp_all
      subgoal for p1 f1 p1' f1' p2 f2 p2' f2'
          apply (auto simp add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def split: if_splits)
               apply hypsubst_thin
        subgoal for x
          by (auto 10 10 simp add: bisim_Read_iff intro!: bc_base intro: stepped.intros bisim_ReadI)
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule stepped.intros(3)[of "comp_op wire (buf(p2' := btl (buf p2'))) (Read p1' f1') (safe_read f2' (BHD p2' buf))"])
            apply force
           defer
          apply (rule bc_base)


end
            defer
          apply assumption

          apply (rule bc_bisim)
             apply (rule bisim.intros)
              prefer 2
              apply (intro exI conjI)
             apply assumption
            prefer 3
          


end
           apply (rule stepped.intros(3))
          prefer 2
          apply assumption
          apply (auto simp add: bisim_Read_iff rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def intro: stepped.intros bisim_ReadI)
          unfolding not_def
           apply (drule mp)


          defer
          apply (intro conjI exI bc_base)



end

lemma "bisim (pcomp_op op1 (pcomp_op op2 op3)) (map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2) op3))"
  apply (coinduction arbitrary: op1 op2 op3 rule: bisim_coinduct_upto)
  subgoal for op1 op2 op3
    unfolding pcomp_op_def
    apply (cases op1; cases op2; cases op3)
    subgoal for p1 f1 p2 f2 p3 f3
      apply safe
       apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
      subgoal for io op
        apply auto
        subgoal for op'
          apply (auto simp add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
          subgoal for x
            apply (rule exI)
            apply (intro conjI)
             apply (rule stepped.intros(3))
              apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
              apply (rule disjI2)
              apply (rule disjI1)
              apply (rule refl)
             apply (rule stepped.intros(3))
              prefer 2
              apply (rule stepped.intros(1))
             defer
             apply (rule bc_base)
             apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
            apply force
            done
          subgoal for x
            apply (rule exI)
            apply (intro conjI)
             apply (rule stepped.intros(3))
              apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
              apply (rule disjI2)
              apply (rule disjI1)
              apply (rule refl)
             apply (rule stepped.intros(3))
              apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
              apply (rule disjI1)
              apply (rule refl)
             apply (rule stepped.intros(1))
            defer
            apply (rule bc_base)


end
              apply (subst (5) comp_op_code)
            apply simp
              apply (rule bc_Choice)
              apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
              apply (intro conjI)
                 apply (rule bexI)
              apply (rule bc_refl)
                  apply (rule refl)
                 apply hypsubst_thin
            defer
        apply (rule bexI)
              apply (rule bc_refl)
                  apply (rule refl)


              apply (rule bc_base)
            apply (rule exI[of _ op1])
            apply (rule exI[of _ op2])
            apply (rule exI[of _ op3])
              apply (intro conjI)
               defer
               apply (rule refl)
              apply blast
             prefer 2
             apply simp
            apply hypsubst_thin
            apply simp


            apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
           apply (elim disjE)
              apply (rule stepped.intros(3))
            apply (auto simp add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)[1]


            subgoal
            apply (auto simp add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
              apply hypsubst_thin
              apply (rule stepped.intros(3))
              defer
              apply (rule stepped.intros(1))
            apply (auto simp add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
              

end
          defer
          subgoal
            apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
            apply (elim disjE)
            subgoal
              apply hypsubst_thin
              apply auto
            apply (rule bc_bisim)
              apply (rule bisim.intros)
              subgoal for x l s'
                apply (rule exI[of _ s'])
                apply auto
                


end
            apply simp
            done

            apply (rule stepped.intros(3))
            defer
             apply assumption
       apply (simp_all add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
            apply (elim disjE)
            subgoal
                apply auto
              apply hypsubst_thin

end
      apply (subst (1 2) comp_op_simps; simp del: comp_op_simps)
      apply (subst (1) comp_op_simps)
      apply (subst (1) comp_op_simps)
      apply (simp del: comp_op_simps)
      apply (simp del: comp_op_simps add: rel_cset_alt_def cinsert.rep_eq cimage.rep_eq sup_cset.rep_eq bot_cset.rep_eq o_def)
      apply (intro conjI)
      subgoal
      apply (rule disjI2)
           apply (rule disjI1)
           apply (rule op.cong_base)
           

end
corecursive comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op" where
  "comp_op wire buf op1 op2 =
     (let comp_op' = (\<lambda>buf' op1' op2'. if \<exists>n. comp_producing wire buf op1 op2 n then comp_op wire buf' op1' op2' else End) in
     case (op1, op2) of
     (Choice op1s, Choice op2s) \<Rightarrow> safe_choice2 (comp_op wire buf) op1s op2s
   | (Choice op1s, Write op2' p2 x2) \<Rightarrow> safe_choice (\<lambda>op1. Write (comp_op wire buf op1 op2') (Inr p2) x2) op1s
   | (Choice op1s, Read p2 f2) \<Rightarrow> let buf' = if op1s = cempty then bend o buf else buf in if p2 \<in> ran wire
     then safe_choice_stop (comp_op' (BTL p2 buf') End (safe_read f2 (BHD p2 buf'))) (\<lambda>op1. comp_op wire (BTL p2 buf') op1 (safe_read f2 (BHD p2 buf'))) op1s
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
     | Some p \<Rightarrow> safe_choice_stop (comp_op' (BENQ p x1 buf) op1' End) (comp_op wire (BENQ p x1 buf) op1') op2s)
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
  apply (auto 0 4 split: op.splits option.splits simp add: Let_def intro: comp_producing.intros not_comp_producing_eq_End not_comp_producing_eq_End[symmetric])
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
    by (fastforce simp: not_comp_producing_eq_End)
  then show ?case
    using Read1 by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
next
  case (Read2 p p' f x d g)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_End)
  then show ?case
    using Read2 by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
next
  case (Write p p' op' x d g)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_End)
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

lemma outputs_comp_op2: "sub_op (Write op' p y) (comp_op wire buf op1 op2) d \<Longrightarrow> p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
proof (induct p \<open>comp_op wire buf op1 op2\<close> arbitrary: buf op1 op2 rule: sub_op_Write_induct)
  case (Read p p' f x op' y d)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_End)
  then show ?case
    using Read by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
next
  case (Write1 p p' op' x op2 y d)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_End)
  then show ?case
    using Write1 by (induct n rule: comp_producing.induct)
      (fastforce split: if_splits option.splits simp: less_Suc_eq image_iff)+
next
  case (Write2 p op' x)
  then obtain n where \<open>comp_producing wire buf op1 op2 n\<close>
    by (fastforce simp: not_comp_producing_eq_End)
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
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal by (smt (z3) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal by (meson End causal.intros(10))
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
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal
      by (smt (verit, ccfv_SIG) comp_producing.intros(12) fun_upd_apply fun_upd_upd not_comp_producing_eq_End)
    subgoal
      using End by metis
    subgoal
      by (metis (mono_tags, opaque_lifting) End comp_eq_dest_lhs comp_producing.intros(9) not_comp_producing_eq_End)
    done
  done

lemma comp_producing_traced_cases:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   traced (comp_op wire buf op1 op2) ios \<Longrightarrow>
   comp_op wire buf op1 op2 = End \<and> ios = LNil \<or>
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
      by (smt (verit, del_insts) End causal.intros(10) lalternate_LNil(2) llist.simps(12) observation.map_id tc_base)
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
      by (smt (verit, ccfv_threshold) End lalternate_LNil(1) lmap_eq_LNil observation.map_id tc_base)
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

simps_of_case retrace_comp_op_simps[simp]: retrace_comp_op.code[unfolded prod.case Let_def]

abbreviation "Inp_Inl_llist ios \<equiv> lmap (case_IO (case_sum (\<lambda> _ ob. ob) undefined) undefined) (lfilter (case_IO (case_sum \<top> \<bottom>) \<bottom>) ios)"
abbreviation "Inp_Inr_llist ios \<equiv> lmap (case_IO (case_sum undefined (\<lambda> _ ob. ob)) undefined) (lfilter (case_IO (case_sum \<bottom> \<top>) \<bottom>) ios)"

abbreviation "retrace_comp_op_ios wire buf op1 op2 ios \<equiv> retrace_comp_op wire buf op1 op2 (Inp_Inl_llist ios) (Inp_Inr_llist ios)"

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

lemma in_retrace_comp_op_End_not_Inr:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = retrace_comp_op wire buf op1 End ios1 ios2 \<Longrightarrow>
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
      by (auto simp add: lfilter_eq_LNil lmap_eq_LNil split: IO.splits sum.splits if_splits if_splits observation.splits dest: in_retrace_comp_op_End_not_Inr)
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
        apply (metis (mono_tags, lifting) End comp_producing.intros(12) fun_upd_same fun_upd_upd lfilter_LNil lmap_eq_LNil not_comp_producing_eq_End)
             apply (smt (verit) End comp_producing.intros(12) fun_upd_apply fun_upd_upd lfilter_LNil lmap_eq_LNil not_EOB not_comp_producing_eq_End)+
        done
      subgoal
        by (auto 10 10)
      done
    subgoal  
      by (auto 10 10 split: sum.splits if_splits if_splits observation.splits option.splits)
    subgoal  
      by (auto simp add: lfilter_eq_LNil lmap_eq_LNil split: IO.splits sum.splits if_splits if_splits observation.splits dest: in_retrace_comp_op_End_not_Inr)
    subgoal  
              apply hypsubst_thin
      apply (clarsimp split: option.splits sum.splits if_splits if_splits observation.splits)
      subgoal
        by (smt (verit) bhd.elims)
      subgoal
        apply (drule not_comp_producing_eq_End)
        apply (auto simp add: lmap_eq_LNil split: if_splits intro: End)
        apply (metis End lfilter_LNil lmap_eq_LNil)
        apply (smt (verit) End comp_apply comp_op_simps'(7) comp_op_simps(7) lfilter_LNil lmap_eq_LNil)
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

lemma comp_producing_in_retrace_comp_op_eq_End:
  "comp_producing wire buf op1 op2 n \<Longrightarrow>
   x \<in> lset (retrace_comp_op wire buf op1 op2 ios1 ios2) \<Longrightarrow>
   comp_op wire buf op1 op2 = End \<Longrightarrow>
   \<not> visible_IO wire x"
  apply (induct buf op1 op2 n arbitrary: ios1 ios2 rule: comp_producing.induct)
  apply (auto 10 10 split: if_splits option.splits intro: comp_producing.intros)
  done

lemma in_retrace_comp_op_eq_End:
  "x \<in> lset (retrace_comp_op wire buf op1 op2 ios1 ios2) \<Longrightarrow>
   comp_op wire buf op1 op2 = End \<Longrightarrow>
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
          by (auto 0 0 simp add: not_comp_producing_eq_End split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_End)
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_End split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_End)
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_End split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_End)
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
              by (smt (verit, ccfv_threshold) Suc_ile_eq Extended_Nat.eSuc_mono comp_producing.intros(12) diff_Suc_1' diff_less_Suc eSuc_enat fun_upd_same fun_upd_upd lnth_Suc_LCons not_comp_producing_eq_End)
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
              by (smt (verit, best) Extended_Nat.eSuc_mono Suc_ile_eq Suc_lessD comp_producing.intros(12) eSuc_enat fun_upd_apply lessI lnth_Suc_LCons not_comp_producing_eq_End)
            done
          done
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_End split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_End)
        subgoal
          apply (clarsimp split: if_splits option.splits)
          subgoal
            using Suc_ile_eq by blast
          subgoal
            by (metis Suc_ile_eq comp_producing.intros(4) lessI not_comp_producing_eq_End)
          done
        subgoal
          apply (clarsimp split: if_splits option.splits)
          subgoal
            using Suc_ile_eq by blast
          subgoal
            by (smt (verit, best) Suc_ile_eq comp_eq_dest_lhs comp_producing.intros(9) lessI not_comp_producing_eq_End)
          done
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_End split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_End)
        subgoal
          by (auto 0 0 simp add: not_comp_producing_eq_End split: if_splits option.splits dest: comp_producing_in_retrace_comp_op_eq_End)
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
            by (metis gr_implies_not_zero llength_LNil not_comp_producing_eq_End traced_EndE)
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
            by (metis gr_implies_not_zero llength_LNil not_comp_producing_eq_End traced_EndE)
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
    apply (drule not_comp_producing_eq_End)
    apply auto
    done
  done

lemma lhd_lalternate:
  "x \<in> lset ios1 \<Longrightarrow>
   lhd (lalternate ios1 ios2) = lhd ios1"
  apply (induct ios1 arbitrary: ios2 rule: lset_induct)
   apply (auto simp add: lalternate_LCons1)
  done

lemma Inr_llist_retrace_comp_op_ios_End:
  "Inr_llist (retrace_comp_op_ios wire buf op1 End ios) = LNil"
  apply (coinduction arbitrary: buf op1 ios)
  apply (intro impI conjI iffI)
  apply (auto split: IO.splits sum.splits)
  using in_retrace_comp_op_End_not_Inr apply fastforce+
  done

lemma Inl_llist_retrace_comp_op_ios_End:
  "Inl_llist (retrace_comp_op_ios wire buf End op2 ios) = LNil"
  apply (coinduction arbitrary: buf op2 ios)
  apply (intro impI conjI iffI)
  apply (auto split: IO.splits sum.splits)
  using in_retrace_comp_op_End_not_Inl apply fastforce+
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

lemma retrace_comp_op_End1_is_op1:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = retrace_comp_op wire buf op1 End ios1 ios2 \<Longrightarrow>
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

lemma retrace_comp_op_End2_is_op2:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = retrace_comp_op wire buf End op2 ios1 ios2 \<Longrightarrow>
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
    apply (auto 10 10 simp add: retrace_comp_op_End1_is_op1 retrace_comp_op_End2_is_op2 split: option.splits)
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
        apply (drule in_retrace_comp_op_eq_End)
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
        by (metis lnull_def not_comp_producing_eq_End traced_EndE)
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
        apply (metis lnull_def not_comp_producing_eq_End traced_EndE)
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
      apply (elim traced_ReadE traced_EndE)
      apply simp
      subgoal for x lxs
        apply safe
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal for p d
          apply (cases p)
          apply simp_all
          apply (smt (z3) IO.simps(5) IO.simps(6) LNil_eq_lmap bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) old.sum.simps(5) retrace_comp_op_End1_is_op1)
          done
        subgoal for p d
          apply (cases p)
          apply simp_all
          apply (smt (z3) IO.simps(5) IO.simps(6) LNil_eq_lmap bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) old.sum.simps(5) retrace_comp_op_End1_is_op1)+
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
          by (smt (verit, ccfv_SIG) End comp_producing.intros(12) fun_upd_same fun_upd_upd lfilter_LNil lmap_eq_LNil not_comp_producing_eq_End)
        subgoal
          using End comp_producing.intros(12) fun_upd_same fun_upd_upd lfilter_LNil lmap_eq_LNil not_comp_producing_eq_End
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
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_End1_is_op1)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_End1_is_op1)
        done
      subgoal
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_End1_is_op1)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_End1_is_op1)
        done
      subgoal
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_End1_is_op1)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_End1_is_op1)
        done
      subgoal
        apply (auto 0 0 simp add: neq_LNil_conv)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_End1_is_op1)
        subgoal
          by (smt (z3) IO.simps(5) IO.simps(6) bot2E diverge_lfilter_LNil is_op1.elims(2) llist.distinct(1) lmap_eq_LNil old.sum.simps(5) retrace_comp_op_End1_is_op1)
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
        using Inl_llist_LNil retrace_comp_op_End2_is_op2 apply blast
        apply (intro exI conjI)
        defer
        apply (rule refl)
        apply auto
        apply (rule sym)
        using Inl_llist_LNil retrace_comp_op_End2_is_op2 apply blast
        done
      subgoal
        apply auto
        subgoal using Inl_llist_LNil retrace_comp_op_End2_is_op2 by blast
        subgoal
          apply (rule exI[of _ End])
          apply (rule exI[of _ "f (BHD (buf p) bend)"])
          apply (rule exI[of _ LNil])
          apply (intro conjI)
          apply (rule sym)
          subgoal using Inl_llist_LNil retrace_comp_op_End2_is_op2 by blast
          subgoal
            by force
          subgoal
            apply (subst not_comp_producing_eq_End)
            apply safe
            subgoal for n
              unfolding not_def
              apply (drule spec[of _ "Suc n"])
              apply (rotate_tac 4)
              apply (drule mp)
              apply (rule comp_producing.intros)
              apply auto
              done
            apply (intro End)
            done
          done
        done
      subgoal
        apply auto
        using Inl_llist_LNil retrace_comp_op_End2_is_op2 apply blast
        apply (intro exI conjI)
        defer
        apply (rule refl)
        apply auto
        apply (rule sym)
        using Inl_llist_LNil retrace_comp_op_End2_is_op2 apply blast
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
      using Inl_llist_LNil retrace_comp_op_End2_is_op2 apply blast
      apply (intro exI conjI)
      defer
      apply (rule refl)
      apply auto
      apply (rule sym)
      using Inl_llist_LNil retrace_comp_op_End2_is_op2 apply blast
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
          apply (drule not_comp_producing_eq_End)
          apply simp
          apply (auto simp add: lfilter_eq_LNil lset_lalternate)
          subgoal
            apply (drule lset_ios1_comp_op_End_not_visible)
                apply assumption+
            apply auto
            done
          subgoal
            apply (drule lset_ios2_comp_op_End_not_visible)
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

end