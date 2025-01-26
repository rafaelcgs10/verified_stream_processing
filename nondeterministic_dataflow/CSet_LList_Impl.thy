theory CSet_LList_Impl
  imports Cset_Setup
   "Coinductive.Coinductive_List"
   "HOL-Library.Code_Lazy"
   "HOL-Library.BNF_Corec"
   "HOL-Library.Debug"
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

definition "cempty' (TYPE('a)) = cset_of_llist (LNil :: 'a llist)"

lemma cempty_code[code_unfold]: "(cempty :: 'a cset) = cempty'(TYPE('a))"
  including cset.lifting unfolding cempty'_def
  by transfer auto

code_thms cempty'

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
  "lmerge xss = (case ldropWhile lnull xss of LNil \<Rightarrow> LNil
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
        apply (smt (verit, ccfv_threshold) lnull_def eq_LConsD ldropWhile_LCons ldropWhile_eq_LNil_iff lhd_ldropWhile lhd_ldropWhile_in_lset linterleave_LCons1 llist.exhaust_sel lmerge.code lmerge_LCons lnth_0 lset_intros(1))
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

typedef 'a dlist = "{xs :: 'a list. distinct xs}"
  by auto

setup_lifting type_definition_dlist

lift_definition (code_dt) dsublists :: "'a dlist \<Rightarrow> 'a dlist list" is sublists
  sorry

term Rep_x'a_dlist_list_x_x_x'a_list_list
term list.sel21

lemma "Rep_isom x \<equiv>
  if dis1 x then [] else sel21 x # Rep_isom (sel22 x)"
  sorry

lemma "dsublists xs \<equiv> Rep_isom (dsublists_aux xs)"
  sorry

print_theorems
code_thms dsublists

find_theorems dsublists

quotient_type 'a cset' = "'a llist" / "\<lambda>xs ys. lset xs = lset ys"
  by (auto simp: equivp_def fun_eq_iff)

lift_definition ccUnion :: "'a cset' llist \<Rightarrow> 'a cset'" is lmerge
  sorry

print_theorems
code_thms ccUnion

lemma in_lset_lmergeI: "xs \<in> lset xss \<Longrightarrow> x \<in> lset xs \<Longrightarrow> x \<in> lset (lmerge xss)"
  by (induct xs xss rule: llist.set_induct) auto

lemma lset_lmerge[simp]: "lset (lmerge xss) = (\<Union>xs \<in> lset xss. lset xs)"
  by (auto intro: in_lset_lmergeI dest: in_lset_lmergeD)

lemma cproduct_code[code]:
  "cproduct (cset_of_llist xs) (cset_of_llist ys) = cset_of_llist (lmerge (lmap (\<lambda>x. lmap (Pair x) ys) xs))"
  unfolding cproduct_def cset_of_llist_def by auto

lemma cUn_code[code]:
  "cUn (cset_of_llist xs) (cset_of_llist ys) = cset_of_llist (linterleave xs ys)"
  unfolding sup_cset_def cset_of_llist_def by auto

lemma cUnion_not_code:
  "cUnion (cset_of_llist (lmap cset_of_llist xss)) = cset_of_llist (lmerge xss)"
  unfolding cUnion_def cset_of_llist_def by auto

quotient_type 'a cset_llist = "'a llist llist" / "\<lambda>xss yss. lmap lset xss = lmap lset yss"
  by (auto simp: equivp_def fun_eq_iff)

lift_definition cset_llist_merge :: "'a cset_llist \<Rightarrow> 'a cset" is
  "cset_of_llist o lmerge"
  apply (auto simp: cset_of_llist_def)
  apply (metis UN_E in_lset_lmergeI lset_lmap lset_lmerge)+
  done

lemma countable_ex_llist: "countable A \<Longrightarrow> \<exists>xs. lset xs = A"
  by (metis lset_LNil lset_inf_llist uncountable_def)

context includes cset.lifting begin
lift_definition wit_cset :: "'a cset \<Rightarrow> 'a llist" is
   "\<lambda>A. SOME xs. lset xs = A" .

lemma lset_wit_cset: "lset (wit_cset A) = rcset A"
  by transfer (auto dest: someI_ex[OF countable_ex_llist])

lemma wit_cset_inverse: "cset_of_llist (wit_cset A) = A"
  by transfer (auto dest: someI_ex[OF countable_ex_llist])
end

lift_definition cset_llist_of :: "'a cset llist \<Rightarrow> 'a cset_llist" is
  "lmap wit_cset" .

lift_definition CLNil :: "'a itself \<Rightarrow> 'a cset_llist" is "\<lambda>_. LNil" .

lift_definition CLCons :: "'a cset \<Rightarrow> 'a cset_llist \<Rightarrow> 'a cset_llist" is "LCons o wit_cset" by auto

lemma abs_cset_llist_inverse[simp]:
  "lmap lset (rep_cset_llist (abs_cset_llist xs)) = lmap lset xs"
  by (metis (mono_tags, lifting) Quotient3_cset_llist rep_abs_rsp)

lemma CLCons_code[code]: "CLCons (cset_of_llist xs) (abs_cset_llist xss) =
  abs_cset_llist (LCons xs xss)"
  unfolding CLCons_def cset_of_llist_def
  by (auto simp: cset_llist.abs_eq_iff lset_wit_cset)

codatatype 'a cset_llist_lazy = CLNil_Lazy | CLCons_Lazy "'a cset" "'a cset_llist"

primcorec Lazy_cset_llist where
  "Lazy_cset_llist xs = Lazy.force"
code_thms LNil LCons
code_thms Lazy_llist
find_theorems Lazy_llist
term LNil_Lazy
term LCons_Lazy

(*
free_constructors case_cset_llist for CLNil | CLCons
     apply safe
       apply transfer
  subgoal for P xs
    apply (cases xs; auto simp: lset_wit_cset)
    apply (metis cset_of_llist.rep_eq)
    done
  subgoal
    apply transfer
    apply auto
    apply (metis cin_code wit_cset_inverse)
    done
  subgoal
    apply transfer
    apply auto
    apply (metis cin_code wit_cset_inverse)
    done
  subgoal
    apply transfer
    apply auto
    done
  subgoal
    apply transfer
    apply auto
    done
  done

code_lazy_type cset_llist
print_theorems
*)

lemma cset_llist_of_code[code]:
  "cset_llist_of LNil = CLNil (TYPE('a))"
  "cset_llist_of (LCons X Xs) = CLCons X (cset_llist_of Xs)"
  by (transfer; auto)+

lemma cUnion_code[code]: "cUnion (cset_of_llist xs) = cset_llist_merge (cset_llist_of xs)"
  unfolding cset_llist_merge_def cset_of_llist_def cset_llist_of_def
  apply (auto simp: cin_def)
  apply (metis UN_E cset_llist_merge.abs_eq cset_llist_merge.rep_eq cset_of_llist.rep_eq image_eqI in_lset_lmergeI lset_lmap lset_lmerge lset_wit_cset)
  apply (smt (verit, best) UN_E cset_llist_merge.abs_eq cset_llist_merge.rep_eq cset_of_llist.rep_eq imageE in_lset_lmergeI lset_lmap lset_lmerge wit_cset_inverse)
  done

code_thms cUnion

(**)

codatatype 'a cllist = CLNil | CLCons "'a cset" "'a cllist"

primcorec cllist_of_llist :: "'a llist llist \<Rightarrow> 'a cllist" where
  "cllist_of_llist xss = (case xss of LNil \<Rightarrow> CLNil | LCons xs xss \<Rightarrow> CLCons (cset_of_llist xs) (cllist_of_llist xss))"

primcorec llist_of_cllist :: "'a cllist \<Rightarrow> 'a cset llist" where
  "llist_of_cllist Xs = (case Xs of CLNil \<Rightarrow> LNil | CLCons X Xs \<Rightarrow> LCons X (llist_of_cllist Xs))"

primcorec cllist_of_llist' :: "'a cset llist \<Rightarrow> 'a cllist" where
  "cllist_of_llist' Xs = (case Xs of LNil \<Rightarrow> CLNil | LCons X Xs \<Rightarrow> CLCons X (cllist_of_llist' Xs))"

lemma cllist_of_llist_inverse[simp]: 
  "llist_of_cllist (cllist_of_llist xs) = lmap cset_of_llist xs"
  apply (coinduction arbitrary: xs)
  apply (auto split: cllist.splits)
    apply (simp add: cllist_of_llist.code llist.case_eq_if)
   apply (simp add: cllist_of_llist.code llist.case_eq_if)
  apply (metis cllist.sel(2) cllist_of_llist.simps(4) llist.case_eq_if)
  done

lemma cllist_of_llist'_inverse[simp]: 
  "llist_of_cllist (cllist_of_llist' xs) = xs"
  apply (coinduction arbitrary: xs)
  apply (auto split: cllist.splits)
    apply (simp add: cllist_of_llist'.code llist.case_eq_if)
   apply (simp add: cllist_of_llist'.code llist.case_eq_if)
  apply (metis cllist.sel(2) cllist_of_llist'.simps(4) llist.case_eq_if)
  done

typedef 'a ccset = "UNIV :: 'a cllist set"
  by blast

setup_lifting type_definition_ccset

lift_definition ccset_of_llist :: "'a llist llist \<Rightarrow> 'a ccset" is
  cllist_of_llist .

lift_definition ccset_of_llist' :: "'a cset llist \<Rightarrow> 'a ccset" is
  cllist_of_llist' .

code_datatype ccset_of_llist

lift_definition ccUnion :: "'a ccset \<Rightarrow> 'a cset" is "cUnion o cset_of_llist o llist_of_cllist" .

lemma ccUnion_code[code]: "ccUnion (ccset_of_llist xss) = cset_of_llist (lmerge xss)"
  unfolding ccUnion_def ccset_of_llist_def
  by (auto simp: Abs_ccset_inverse cin_def cset_of_llist_def)

lemma cUnion_code[code]: "cUnion (cset_of_llist X) = ccUnion (ccset_of_llist' X)"
  unfolding cUnion_def ccUnion_def ccset_of_llist'_def
  by (auto simp: Abs_ccset_inverse)

code_thms cUnion

lemma cfilter_code[code]: "cfilter P (cset_of_llist xs) = cset_of_llist (lfilter P xs)"
  unfolding cfilter_def cset_of_llist_def by (auto simp: Set.filter_def)

lemma cimage_code[code]: "cimage f (cset_of_llist xs) = cset_of_llist (lmap f xs)"
  unfolding cimage_def cset_of_llist_def by auto

definition cis_empty :: "'a cset \<Rightarrow> bool" where "cis_empty X = (X = cempty)"

lemma cis_empty_code[code]:
  "cis_empty (cset_of_llist LNil) = True"
  "cis_empty (cset_of_llist (LCons x xs)) = False"
  unfolding cis_empty_def cset_of_llist_def by (auto simp: cin_def)

lemma eq_cempty_cis_empty[code_unfold]:
  "(X = cempty) = cis_empty X"
  "(cempty = X) = cis_empty X"
  "(X = cempty' (TYPE('a))) = cis_empty X"
  "(cempty' (TYPE('a)) = X) = cis_empty X"
  unfolding cis_empty_def cempty_code[symmetric] by auto

lemma if_Lazy_llist [code_unfold]:
   "(if c then Lazy_llist (delay (\<lambda>_. x)) else Lazy_llist (delay (\<lambda>_. y))) =
    Lazy_llist (delay (\<lambda>_. if c then x else y))"
   by(simp)

lemma case_lazy_llist_Lazy_llist [code_unfold]:
   "case_llist_lazy (Lazy_llist (delay (\<lambda>_. x))) (\<lambda>x xs. Lazy_llist (delay (\<lambda>_. f x xs))) xs =
    Lazy_llist (delay (\<lambda>_. case_llist_lazy x f xs))"
  by(simp add: Lazy_llist_def force_delay case_llist_lazy_def split: llist.split)


corec const where "const x = LCons x (const x)"
corec "from" where "from x = LCons x (from (Suc x))"

fun ltaken where
  "ltaken (Suc n) (LCons x xs) = x # ltaken n xs"
| "ltaken _ _  = []"

definition force_cset :: "nat \<Rightarrow> 'a cset \<Rightarrow> 'a cset" where
  "force_cset n xs = xs"

lemma
  force_cset_code[code]: "force_cset n (cset_of_llist xs) =
    (let _ = ltaken n xs in cset_of_llist xs)"
  by (auto simp: force_cset_def)

value "force_cset 10 (cUn (cset_of_llist (from 42)) (cset_of_llist (const 2)))"
value "force_cset 10 (cempty :: nat cset)"
value "force_cset 10 (cUNIV :: nat cset)"
value "force_cset 10 (cimage (\<lambda>x. x + 5) (cfilter (\<lambda>x. x mod 2 = 0) cUNIV :: nat cset))"
value "force_cset 10 (cproduct (cUNIV :: nat cset) (cUNIV :: nat cset))"
value "(5 :: nat, True) |\<in>| cproduct cUNIV cUNIV"
value "force_cset 10 (cUnion (cset_of_llist (lmap (cset_of_llist o from) (llist_of [1,2,3]))))"
value "force_cset 10 (cUnion (cset_of_llist (lmap (cset_of_llist o from) (from 1))))"


value "(5 :: nat) |\<in>| cUNIV"
value "5 |\<in>| (cempty :: nat cset)"
value "5 |\<in>| (cset_of_llist (llist_of []) :: nat cset)"
value "(5 :: nat) |\<in>| cinsert 5 cempty"

end