theory CSet_LList_Impl
  imports Cset_Setup
   "Coinductive.Coinductive_List"
   "HOL-Library.Code_Lazy"
   "HOL-Library.BNF_Corec"
   "HOL-Library.Simps_Case_Conv"
begin

code_lazy_type llist

lemma countable_lset[simp]: "countable (lset xs)"
  by (metis (mono_tags, opaque_lifting) countableI_type countable_image countable_subset in_lset_conv_lnth rangeI subset_iff)

context includes cset.lifting begin
lift_definition cset_of_llist :: "'a llist \<Rightarrow> 'a cset" is "lset" by simp
end

code_datatype cset_of_llist
quickcheck_generator cset constructors: cset_of_llist

lemma cempty_code[code]: "cempty = cset_of_llist LNil"
  including cset.lifting
  by transfer auto

lemma cinsert_code[code]: "cinsert x (cset_of_llist xs) = cset_of_llist (LCons x xs)"
  including cset.lifting
  by transfer auto

lemma cin_code[code]: "cin x (cset_of_llist xs) = (x \<in> lset xs)"
  including cset.lifting
  by transfer auto

class cenum =
  fixes cenum :: "'a llist"
  assumes UNIV_cenum: "UNIV = lset cenum"
    and cenum_distinct: "ldistinct cenum"
begin

subclass countable
  by standard (metis UNIV_I in_lset_conv_lnth UNIV_cenum surj_def surj_imp_inj_inv)

end

lemma cUNIV_code[code]: "(cUNIV :: 'a :: cenum cset) = cset_of_llist cenum"
  including cset.lifting
  by (transfer, rule UNIV_cenum)

context enum begin
sublocale enum_cenum: cenum "llist_of Enum.enum"
  by standard (auto simp: UNIV_enum enum_distinct)
end

instantiation bool :: cenum begin
definition cenum_bool :: "bool llist" where "cenum_bool = llist_of Enum.enum"
instance by standard (simp_all only: cenum_bool_def enum_cenum.UNIV_cenum enum_cenum.cenum_distinct)
end

instantiation nat :: cenum begin
definition "cenum_nat = iterates Suc 0"

lemma lset_iterates_Suc_ge: "x \<ge> y \<Longrightarrow> x \<in> lset (iterates Suc y)"
  by (induct "x - y" arbitrary: y) (subst iterates.code; simp)+

lemma lset_iterates_Suc_ge': "x \<in> lset (iterates Suc y) \<Longrightarrow> x \<ge> y"
  by (induct x "iterates Suc y" arbitrary: y rule: llist.set_induct)
    (subst (asm) iterates.code; force)+

lemma ldistinct_iterates_Suc: "ldistinct (iterates Suc n)"
  by (coinduction arbitrary: n) (auto dest!: lset_iterates_Suc_ge')

instance by standard (auto simp: cenum_nat_def lset_iterates_Suc_ge ldistinct_iterates_Suc)
end

corec (friend) linterleave where
  "linterleave xs ys = (case (xs, ys) of
     (LCons x xs', LCons y ys') \<Rightarrow> LCons x (LCons y (linterleave xs' ys'))
   | (LCons x xs', LNil) \<Rightarrow> LCons x xs'
   | (LNil, LCons y ys') \<Rightarrow> LCons y ys'
   | (LNil, LNil) \<Rightarrow> LNil)"
simps_of_case linterleave_simps[simp]: linterleave.code[unfolded prod.case]

lemma linterleave_LNil[simp]:
  "linterleave LNil ys = ys"
  "linterleave ys LNil = ys"
   apply (cases ys; auto)+
  done

lemma linterleave_LCons1[simp]:
  "linterleave (LCons x xs) ys = LCons x (linterleave ys xs)"
  apply (coinduction arbitrary: x xs ys rule: llist.coinduct_upto)
  subgoal for x xs ys
    apply (intro impI context_conjI)
      apply (cases ys)
       apply auto [2]
    apply (simp only: )
     apply (cases ys)
      apply auto[2]
    apply (cases xs; cases ys)
       apply (auto intro: llist.cong_intros)
    apply (metis (mono_tags, lifting) llist.cong_LCons llist.cong_base)
    done
  done

lemma lset_linterleave1:
  "x \<in> lset (linterleave xs ys) \<Longrightarrow>
   x \<in> lset xs \<union> lset ys"
  apply (induct "linterleave xs ys" arbitrary: xs ys rule: lset_induct)
  subgoal for xs' xs ys 
    apply (cases xs; cases ys)
       apply auto
    done
  subgoal for x' xs' xs ys
    apply (cases xs; cases ys)
       apply (simp split: llist.splits)
      apply auto
    apply hypsubst_thin
    using linterleave_LCons1 
    by (metis insert_iff llist.set(2))
  done

lemma lset_linterleave2:
  "x \<in> lset xs \<Longrightarrow>
   x \<in> lset (linterleave xs ys)"
  apply (induct "xs" arbitrary: ys rule: lset_induct)
   apply auto
  subgoal for x' xs ys
    apply (cases ys)
     apply (auto split: llist.splits)
    done
  done

lemma lset_linterleave3:
  "x \<in> lset ys \<Longrightarrow>
   x \<in> lset (linterleave xs ys)"
  apply (induct "ys" arbitrary: xs rule: lset_induct)
  subgoal for xs' xs
    apply (cases xs)
     apply auto
    done
  subgoal for x' xs' xs
    apply (cases xs)
     apply (auto split: llist.splits)
    done
  done

lemma lset_linterleave[simp]:
  "lset (linterleave xs ys) = lset xs \<union> lset ys"
  by (auto dest: lset_linterleave1 lset_linterleave2 lset_linterleave3)

corec lmerge where
  "lmerge xss = (case ldropWhile (\<lambda>xs. xs = LNil) xss of LNil \<Rightarrow> LNil
     | LCons xs xss \<Rightarrow> LCons (lhd xs) (linterleave (lmerge xss) (ltl xs)))"

lemma lmerge_LNil[simp]: "lmerge LNil = LNil"
  by (subst lmerge.code; auto)
lemma lmerge_LCons_LNil[simp]: "lmerge (LCons LNil xss) = lmerge xss"
  by (subst (1 2) lmerge.code; auto)
lemma lmerge_LCons_LCons[simp]: "lmerge (LCons (LCons x xs) xss) = LCons x (linterleave (lmerge xss) xs)"
  by (subst (1) lmerge.code; auto)
lemma lmerge_LCons[simp]: "lmerge (LCons xs xss) = linterleave xs (lmerge xss)"
  apply (coinduction arbitrary: xs xss rule: llist.coinduct_upto)
    apply (intro impI context_conjI)
  subgoal for xs xss
    by (cases xs) auto
  subgoal for xs xss
    by (cases xs) auto
  subgoal for xs xss
    by (cases xs) (auto intro: llist.cong_intros)
  done

(*
declare lmerge.code[code del]
declare lmerge_LNil[code] lmerge_LCons[code]
*)

coinductive linfinite where
  "linfinite xs \<Longrightarrow> linfinite (LCons x xs)"

inductive linfinite_cong for R where
  "R xs \<Longrightarrow> linfinite_cong R xs"
| "linfinite xs \<Longrightarrow> linfinite_cong R xs"
| "linfinite_cong R xs \<Longrightarrow> linfinite_cong R (LCons x xs)"

lemma linfinite_coinduct_upto:
  assumes "X xs" "(\<And>ys. X ys \<Longrightarrow> \<exists>xs x. ys = LCons x xs \<and> linfinite_cong X xs)"
  shows "linfinite xs"
  apply (rule linfinite.coinduct[of "linfinite_cong X"])
   apply (rule linfinite_cong.intros(1), rule assms(1))
  subgoal for xs
    apply (induct xs rule: linfinite_cong.induct)
      apply (auto dest!: assms(2) elim: linfinite.cases)
    done
  done

inductive_cases linfinite_LNilE[elim!]: "linfinite LNil"
inductive_cases linfinite_LConsE[elim!]: "linfinite (LCons x xs)"

lemma linfinite_linterleaveL: "linfinite xs \<Longrightarrow> linfinite (linterleave xs ys)"
  apply (coinduction arbitrary: xs ys rule: linfinite_coinduct_upto)
  subgoal for xs ys
    apply (cases xs; cases ys)
       apply (auto intro: linfinite_cong.intros)
    done
  done

lemma linfinite_linterleaveR: "linfinite ys \<Longrightarrow> linfinite (linterleave xs ys)"
  apply (coinduction arbitrary: xs ys rule: linfinite_coinduct_upto)
  subgoal for xs ys
    apply (cases xs; cases ys)
       apply (auto intro: linfinite_cong.intros)
    done
  done

lemma lfinite_imp_not_linfinite: "lfinite xs \<Longrightarrow> \<not> linfinite xs"
  by (induct xs rule: lfinite_induct) (auto simp: lnull_def neq_LNil_conv)
lemma not_lfinite_imp_linfinite: "\<not> lfinite xs \<Longrightarrow> linfinite xs"
  apply (coinduction arbitrary: xs)
  subgoal for xs
    by (cases xs) auto
  done
lemma linfinite_eq_not_lfinite: "linfinite xs \<longleftrightarrow> \<not> lfinite xs"
  using lfinite_imp_not_linfinite not_lfinite_imp_linfinite by blast
lemma linfinite_eq_llength: "linfinite xs \<longleftrightarrow> llength xs = \<infinity>"
  using lfinite_imp_not_linfinite llength_eq_infty_conv_lfinite not_lfinite_imp_linfinite by blast

lemma llength_linterleave[simp]: "llength (linterleave xs ys) = llength xs + llength ys"
  apply (cases "linfinite xs"; cases "linfinite ys")
     apply (metis linfinite_eq_llength linfinite_linterleaveL plus_enat_simps(3))
    apply (metis linfinite_eq_llength linfinite_linterleaveL plus_enat_simps(2))
   apply (metis linfinite_eq_llength linfinite_linterleaveR plus_enat_simps(3))
  apply (simp add: linfinite_eq_not_lfinite)
  apply (induct xs arbitrary: ys rule: lfinite_induct)
   apply (auto simp: lnull_def neq_LNil_conv)
  subgoal premises prems for ys xs'
    using prems(3,1,2)
    apply (induct ys arbitrary: xs' rule: lfinite_induct)
     apply (auto simp: lnull_def neq_LNil_conv add.commute iadd_Suc_right)
    done
  done

lemma lnth_linterleave_swap: 
  "lnth (linterleave xs ys) i \<notin> lset ys \<Longrightarrow> i < llength (linterleave xs ys) \<Longrightarrow>
   \<exists>j < min (Suc i) (llength xs). lnth (linterleave xs ys) i = lnth xs j"
  apply (induct i arbitrary: xs ys rule: less_induct)
  subgoal for i xs ys
    apply (cases i)
    subgoal
      apply (cases xs; cases ys; auto simp: enat_0)
      done
    subgoal for j
      apply (cases xs; cases ys; auto simp: Suc_ile_eq in_lset_conv_lnth lnth_LCons' gr0_conv_Suc less_Suc_eq_le)
      apply (smt (verit, ccfv_SIG) Suc_ile_eq add_is_0 diff_Suc_1' le_Suc_eq less_add_Suc2 not_gr_zero not_less_eq_eq plus_1_eq_Suc)
      done
    done
  done

lemma in_lset_lmergeD: "x \<in> lset (lmerge xss) \<Longrightarrow> x \<in> (\<Union>xs \<in> lset xss. lset xs)"
  unfolding in_lset_conv_lnth
  apply (erule exE conjE)+
  subgoal for n
    apply (induct n arbitrary: xss rule: less_induct)
    subgoal for n xss
      apply (cases n)
      subgoal
        apply simp
        apply (subst (asm) lmerge.code)
        apply (auto split: llist.splits)
        apply (smt (verit, ccfv_threshold) eq_LConsD ldropWhile_LCons ldropWhile_eq_LNil_iff lhd_ldropWhile lhd_ldropWhile_in_lset linterleave_LCons1 llist.exhaust_sel lmerge.code lmerge_LCons lnth_0 lset_intros(1))
        done
      subgoal for m
        apply (subst (asm) (3 4) lmerge.code)
        apply (auto split: llist.splits)
        apply hypsubst_thin
        subgoal for zs zss
          apply (cases "lnth (linterleave (lmerge zss) (ltl zs)) m \<in> lset (ltl zs)")
           apply (metis in_lset_ltlD insert_subset llist.simps(19) lset_ldropWhile_subset)
          apply (drule lnth_linterleave_swap)
           apply (auto simp: Suc_ile_eq)
          apply (metis in_lset_ldropWhileD llist.set_intros(2))
          done
        done
      done
    done
  done

lemma in_lset_lmergeI: "xs \<in> lset xss \<Longrightarrow> x \<in> lset xs \<Longrightarrow> x \<in> lset (lmerge xss)"
  by (induct xs xss rule: llist.set_induct) auto

lemma lset_lmerge[simp]: "lset (lmerge xss) = (\<Union>xs \<in> lset xss. lset xs)"
  by (auto intro: in_lset_lmergeI dest: in_lset_lmergeD)

lemma cproduct_code[code]:
  "cproduct (cset_of_llist xs) (cset_of_llist ys) = cset_of_llist (lmerge (lmap (\<lambda>x. lmap (Pair x) ys) xs))"
  unfolding cproduct_def cset_of_llist_def
  by (auto simp: acset_inverse)

(*
value "(5 :: nat, True) |\<in>| cproduct cUNIV cUNIV"
*)

value "(5 :: nat) |\<in>| cUNIV"
value "cempty :: nat cset"
value "(5 :: nat) |\<in>| cinsert 5 cempty"

end