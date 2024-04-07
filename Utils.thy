theory Utils
  imports
    "HOL.Map"
    "HOL-Library.Multiset"
    "Coinductive.Coinductive_List"
begin

definition
  map_plus :: "('a \<rightharpoonup> 'b::ab_semigroup_add) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"  (infixl "+++" 100) where
  "m1 +++ m2 = (\<lambda>x. case m2 x of None \<Rightarrow> m1 x | Some y \<Rightarrow> (case m1 x of None \<Rightarrow> Some y | Some y' \<Rightarrow> Some (y + y')))"

lemma map_plus_empty[simp]: "m +++ Map.empty = m"
  by(simp add: map_plus_def)

lemma empty_map_plus[simp]: "Map.empty +++ m = m"
  by (rule ext) (simp add: map_plus_def split: option.split)

lemma map_plus_comm: "m1 +++ m2 = m2 +++ m1"
  apply (rule ext)
  apply (simp add: map_plus_def split: option.split)
  apply safe
  using add.commute by auto

lemma map_plus_assoc: "m1 +++ m2 +++ m3 = m1 +++ (m2 +++ m3)"
  apply (rule ext)
  apply (simp add: map_plus_def split: option.split)
  apply safe
  apply (simp add: ab_semigroup_add_class.add_ac(1))
  done

lemma map_plus_both_none: "(m1 +++ m2) a = None \<Longrightarrow> m1 a = None \<and> m2 a = None"
  apply (simp add: map_plus_def split: option.split)
  by (smt (verit, best) option.case_eq_if option.distinct(1))

lemma map_plus_update_to_left: "(m1 +++ m2) a = None \<Longrightarrow> (m1 +++ m2)(a \<mapsto> n) = m1(a \<mapsto> n) +++ m2"
  apply (rule ext)
  apply (simp add: map_plus_def split: option.split)
  apply safe
   apply force
  by (metis (no_types, lifting) is_none_simps(1) is_none_simps(2) option.case_eq_if)

lemma map_plus_update_to_right: "(m1 +++ m2) a = None \<Longrightarrow> (m1 +++ m2)(a \<mapsto> n) = m1 +++ m2 (a \<mapsto> n)"
  apply (rule ext)
  apply (simp add: map_plus_def split: option.split)
  apply safe
  by (metis (mono_tags, lifting) is_none_simps(1) is_none_simps(2) option.case_eq_if)

lemma count_list_remove1:
  "x \<in> set xs \<Longrightarrow> count_list (remove1 x xs) x = count_list xs x - 1"
  apply (induct xs arbitrary: x)
   apply simp
  apply simp
  apply safe
  by blast

lemma count_list_Cons_remove:
  "count_list (x # data1) x = count_list data2 x \<Longrightarrow> count_list data1 x = count_list (remove1 x data2) x"
  apply simp
  apply (subst count_list_remove1)
   apply (metis count_list_0_iff nat.simps(3))
  apply simp
  done

lemma count_list_imp_count_mset:
  "count_list data1 = count_list data2 \<Longrightarrow> count (mset data1) = count (mset data2)"
  apply (rule ext)
  subgoal for x
    apply (drule fun_cong[of _ _ x])
    apply (induct data1 arbitrary: data2 x)
     apply simp
     apply (simp add: count_list_0_iff)
    subgoal for a data1 data2 x
      apply (cases "a = x")
      subgoal
        apply hypsubst_thin
        by (smt (verit, ccfv_SIG) add_diff_cancel_right' add_mset_remove_trivial count_add_mset count_inI count_list.simps(2) count_list_0_iff count_list_remove1 count_mset_0_iff mset_remove1 multi_member_split)
      subgoal
        by simp
      done
    done
  done

lemma cons_append:
  "a # as = [a] @ as"
  by simp

lemma filter_neq_nil_iff:
  "\<exists> x \<in> set xs . P x \<Longrightarrow> filter P xs \<noteq> []"
  by (simp add: filter_empty_conv)

lemma map_neq_nil_iff:
  "xs \<noteq> [] \<Longrightarrow> map f xs \<noteq> []"
  by blast

lemma remdups_neq_nil_iff:
  "xs \<noteq> [] \<Longrightarrow> remdups xs \<noteq> []"
  using remdups_eq_nil_iff by blast

lemma not_lfinite_imp_not_lnull: "\<not> lfinite xs \<Longrightarrow> \<not> lnull xs"
  using lnull_imp_lfinite by blast

lemma drop_Suc':
  "drop (Suc n) xs = tl (drop n xs)"
  apply (induct xs arbitrary: n)
  by (simp_all add: tl_drop)

lemma last_sorted_is_Max:
  "xs \<noteq> [] \<Longrightarrow> sorted xs \<Longrightarrow> last xs = Max (set xs)"
  unfolding Max_def
  apply (induct xs)
   apply simp
  subgoal for a xs
    apply (subst List.semilattice_set.set_eq_fold)
    using Max.semilattice_set_axioms apply blast
    by (metis List.finite_set Max.semilattice_set_axioms Max.set_eq_fold Max_def fold_simps(1) last_ConsL last_ConsR last_in_set list.simps(15) max.absorb_iff2 semilattice_set.insert set_empty sorted_simps(2))
  done

lemma last_sort_is_Max:
  "xs \<noteq> [] \<Longrightarrow> last (sort xs) = Max (set xs)"
  apply (induct xs)
   apply simp
  subgoal for a xs
    using last_sorted_is_Max
    by (metis set_empty set_sort sorted_sort)
  done

lemma map_eq_set_D:
  "(map f xs = ys) \<Longrightarrow> x \<in> set ys \<Longrightarrow> (\<exists>z. x = f z \<and> z \<in> set xs)"
  apply (induct xs)
   apply simp
  apply auto
  done

lemma in_set_sort:
  "x \<in> set (sort xs) = (x \<in> set xs)"
  by force

lemma in_set_remdups:
  "x \<in> set (remdups xs) = (x \<in> set xs)"
  by force

lemma in_set_sort_remdups_map_fst:
  "x \<in> set (sort (remdups (map fst (filter (\<lambda>(t, _). t \<le> wm) data)))) \<Longrightarrow> x \<le> wm"
  apply (subst (asm) in_set_sort)
  apply (subst (asm) in_set_remdups)
  apply (simp split: prod.splits)
  apply safe
  apply simp
  done

lemma sorted_tail_gt:
  "xs = t # xs' \<Longrightarrow>
   t' \<in> set xs' \<Longrightarrow> distinct xs \<Longrightarrow> sorted xs \<Longrightarrow> t < t'"
  using strict_sorted_iff strict_sorted_simps(2) by blast

lemma LCons_in_lset: "xs = LCons x xs' \<Longrightarrow> x \<in> lset xs"
  by auto

lemma filter_ge_Max:
  "t \<ge> Max (set (map fst data)) \<Longrightarrow>
   filter (\<lambda> (t', _). t' \<le> t) data =  data"
  by (metis (no_types, lifting) List.finite_set Max.boundedE case_prod_unfold filter.simps(1) filter_True in_set_zip list.map_disc_iff nth_mem set_empty zip_map_fst_snd)

lemma mset_filter_append:
  "inr < (t::_::linorder) \<Longrightarrow>
   mset (filter (\<lambda>x. (case x of (t, _) \<Rightarrow> inr < t) \<and> (case x of (t', _) \<Rightarrow> t' \<le> t)) data @ filter (\<lambda>(t', d'). t' \<le> inr) data) =
   mset (filter (\<lambda>(t', _). t' \<le> t) data)"
  apply (induct data arbitrary: inr t)
   apply simp
  apply (simp split: prod.splits)
  apply safe
    apply force+
  done

lemma mset_filter_append_2:
  "inr < (t::_::linorder) \<Longrightarrow>
   mset (filter (\<lambda>(t', _). t' < inr \<or> t' = inr) data @ filter (\<lambda>x. (case x of (t, _) \<Rightarrow> inr < t) \<and> (case x of (t', _) \<Rightarrow> t' < t \<or> t' = t)) data) =
   mset (filter (\<lambda>(t', _). t' < t \<or> t' = t) data)"
  apply (induct data arbitrary: inr t)
   apply simp
  apply (simp split: prod.splits)
  apply safe
   apply force+
  done

lemma mset_filter_append_filter_mset:
  "filter_mset P (mset M) + filter_mset Q (mset N) = mset (filter P M @ filter Q N)"
  by simp

lemma llength_eSuc_ltl:
  "\<not> lnull xs \<Longrightarrow> llength xs = eSuc (llength (ltl xs))"
  by (simp add: enat_unfold llength_def)

lemma mset_mfilter_simp_cong[simp]:
  "{#x \<in># {#y \<in># A. Q y#}. P x#} =
   {#x \<in># A. P x \<and> Q x#}"
  using multi_count_eq by fastforce


lemma in_lset_finds_tail: "x \<in> lset xs \<Longrightarrow> \<exists> n xs'. ldrop (enat n) xs = LCons x xs'"
  by (metis in_lset_conv_lnth ldrop_enat ldropn_Suc_conv_ldropn)

lemma mset_concat:
  "mset (concat xs) = sum_list (map mset xs)"
  apply (induct xs)
   apply auto
  done

lemma sum_list_sum:
  "distinct xs \<Longrightarrow>
   set xs = A \<Longrightarrow>
   sum_list (map f xs) = sum f A"
  apply (induct xs arbitrary: A)
   apply auto
  done

lemma Sum_sum_sum_sum:
  "card B = card (set ` B) \<Longrightarrow>
   (\<Sum>x\<in> B. sum f (set x)) = sum (sum f) (set ` B)"
  by (metis card_eq_0_iff eq_card_imp_inj_on sum.empty sum.infinite sum.reindex_cong)


lemma Sum_set_sum_list_map_Sum_sum_set:
  "\<forall> x \<in> set xs . distinct x \<Longrightarrow>
   (\<Sum> x\<in>set xs . sum_list (map f x)) = (\<Sum>x\<in>set xs. sum f (set x))"
  by (meson sum.cong sum_list_sum)

lemma sum_change_fun:
  "\<forall> x \<in> A . f x = g x \<Longrightarrow>
   sum f A = sum g A"
  by force

lemma sum_sum_change_fun:
  "\<forall> x \<in> A . sum f x = sum g x \<Longrightarrow>
   sum (sum f) A = sum (sum g) A"
  using sum_change_fun by blast


lemma filter_tl:
  "\<not> P (hd A) \<Longrightarrow>
   \<forall> x \<in> set (tl A). P x \<Longrightarrow>
   filter P A = tl A"
  by (metis filter.simps(2) filter_True list.collapse tl_Nil)

lemma map_fst_filter[simp]:
  "map fst (filter (\<lambda>(t, d). P t) xs) = filter P (map fst xs)"
  by (metis (mono_tags, lifting) case_prod_unfold comp_apply filter_cong filter_map)


lemma ltake_ldropn_merge_lset:
  "lset (ltake (enat n) lxs) \<union> lset (ldropn n lxs) = lset lxs"
  by (metis enat_ord_code(4) lappend_ltake_enat_ldropn lfinite_ltake lset_lappend_lfinite)

lemma ltake_enat_0:
  "ltake (enat 0) lxs = LNil"
  by (simp add: zero_enat_def)

lemma remove_insert_eq:
  "x \<in> B \<Longrightarrow>
   A = B \<Longrightarrow>
   insert x A = B"
  by fastforce

lemma nth_via_drop':
  "drop n xs = y # ys \<Longrightarrow> xs ! n = y \<and> n < length xs"
  by (metis drop_all leI list.discI nth_via_drop)

lemma distinct_List_subseqs:
  "distinct xs \<Longrightarrow>
   distinct (List.subseqs xs)"
  apply (induct xs)
   apply simp_all
  unfolding Let_def 
  apply simp
  apply safe
   apply (simp add: distinct_map)
  using list_emb_set apply fastforce
  done

lemma filter_singleton:
  "distinct xs \<Longrightarrow> 
   P x \<Longrightarrow> 
   x \<in> set xs \<Longrightarrow>
   \<forall> y \<in> (set xs) - {x} . \<not> P y \<Longrightarrow>
   filter P xs = [x]"
  apply (induct xs arbitrary: x)
   apply auto
  done

lemma filter_Pow:
  "distinct xs \<Longrightarrow>
   filter (\<lambda>l. \<forall>l'\<in>Pow (set xs). \<not> set l \<subset> l') (subseqs xs) = [xs]"
  apply (rule filter_singleton)
     apply (simp_all add: distinct_List_subseqs)
   apply force
  apply (intro ballI)
  subgoal for y
    apply (rule bexI[of _  "set xs"])
     apply (rule psubsetI)
      apply simp_all
    subgoal
      by (metis set_nths_subset subseq_conv_nths)
    subgoal
      by (metis distinct_card in_set_subseqs subseq_same_length subseqs_distinctD)
    done
  done

lemma filter_subseqs_Pow[simp]:
  "filter (\<lambda>l. \<forall>l'\<in>set (subseqs xs). \<not> set l \<subset> set l') (subseqs xs) = filter (\<lambda>l. \<forall>l'\<in>Pow (set xs). \<not> set l \<subset> l')  (subseqs xs)"
  by (metis (no_types, lifting) PowD imageI psubset_subset_trans subseqs_powset subseqs_refl)

lemma mset_concat_sum:
  "mset (concat (map (\<lambda>t. (filter ((=) t) xs)) (remdups xs))) = sum ((\<lambda>t. mset (filter ((=) t) xs))) (set xs)"
  apply (simp add: mset_concat)
  apply (metis (mono_tags, lifting) comp_apply mset_filter sum.cong sum_code)
  done

lemma mset_concat_fst_sum:
  "mset (concat (map (\<lambda>t. (filter ((=) t \<circ> fst) xs)) (remdups (map fst xs)))) = sum ((\<lambda>t. mset (filter ((=) t \<circ> fst) xs))) (set (map fst xs))"
  apply (simp add: mset_concat)
  by (metis (mono_tags, lifting) comp_apply filter_cong list.set_map mset_filter sum.cong sum_code)

lemma mset_concat_sum_filter:
  "mset (concat (map (\<lambda>t. (filter ((=) t) xs)) (filter P (remdups xs)))) = sum ((\<lambda>t. mset (filter ((=) t) xs))) (set (filter P xs))"
  apply (simp add: mset_concat)
  by (metis (mono_tags, lifting) comp_apply mset_filter remdups_filter set_filter sum.cong sum_code)


lemma mset_concat_sum_filter_fst:
  "mset (concat (map (\<lambda>t. (filter ((=) t \<circ> fst) xs)) (filter P (remdups (map fst xs))))) = sum ((\<lambda>t. mset (filter ((=) t \<circ> fst) xs))) (set (filter P (map fst xs)))"
  apply (simp add: mset_concat)
  by (smt (z3) Collect_cong case_prod_unfold comp_apply filter_cong list.set_map map_eq_conv mset_filter remdups_filter set_filter sum_code)

lemma mset_concat_sum_filter_fst_snd:
  "mset (concat (map (\<lambda>t. map snd (filter ((=) t \<circ> fst) xs)) (filter P (remdups (map fst xs))))) = sum ((\<lambda>t. mset (map snd (filter ((=) t \<circ> fst) xs)))) (set (filter P (map fst xs)))"
  apply (simp add: mset_concat)
  by (smt (z3) Collect_cong case_prod_unfold comp_apply filter_cong list.set_map map_eq_conv mset_filter mset_map remdups_filter set_filter sum_code)


lemma mset_concat_map_filter_2[simp]:
  "concat (map (\<lambda>t. (filter (\<lambda> t'. t' = t \<and> P t') xs)) ((filter (\<lambda>t'. P t') (remdups xs)))) = concat (map (\<lambda>t. (filter ((=) t) xs)) ((filter (\<lambda>t'. P t') (remdups xs))))"
  by (smt (verit, best) filter_cong map_eq_conv mem_Collect_eq set_filter)

lemma filter_remdups_map:
  "filter P (remdups (map fst xs)) = remdups (map fst (filter (P \<circ> fst ) xs))"
  by (metis filter_map remdups_filter)

lemma mset_concat_map_filter[simp]:
  "mset (concat (map (\<lambda>t. (filter ((=) t) xs)) (remdups xs))) = mset xs"
  apply (induct xs rule: rev_induct)
   apply auto[1]
  apply (drule sym)
  apply (simp del: filter.simps filter_append add: mset_concat_sum)
  subgoal premises prems for x xs
    apply (smt (verit, ccfv_SIG) Diff_insert_absorb List.finite_set Set.set_insert add.commute add_mset_add_single empty_filter_conv insert_absorb mset.simps(1) mset_filter prems sum.cong sum.insert sum.insert_remove union_mset_add_mset_left)
    done
  done

lemma mset_concat_map_fst_filter[simp]:
  "mset (concat (map (\<lambda>t. (filter ((=) t \<circ> fst) xs)) (remdups (map fst xs)))) = mset xs"
  apply (induct xs rule: rev_induct)
   apply auto[1]
  apply (drule sym)
  apply (subst (asm) mset_concat_fst_sum)
  apply (subst  mset_concat_fst_sum)
  apply (simp del: filter.simps filter_append add: mset_concat_fst_sum)
  using Diff_insert_absorb List.finite_set Set.set_insert add.commute add_mset_add_single empty_filter_conv insert_absorb mset.simps(1) mset_filter sum.cong sum.insert sum.insert_remove union_mset_add_mset_left
  apply (smt (verit, best) case_prod_unfold finite_imageI image_iff)
  done

lemma Sum_if_true:
  "finite A \<Longrightarrow>
   a \<in> A \<Longrightarrow> 
   (\<Sum>t\<in>A. if t = a then G t else F t) = G a + (\<Sum>t\<in>A - {a}. F t)"
  apply (induct A arbitrary: a  rule: finite_induct)
   apply simp_all
  apply (intro conjI impI)
  subgoal
    by (simp add: sum.delta_remove)
  subgoal
    by (simp add: add.left_commute insert_Diff_if)
  done

lemma Sum_if_false:
  "finite A \<Longrightarrow>
   a \<notin> A \<Longrightarrow> 
   (\<Sum>t\<in>A. if t = a then G t else F t) = (\<Sum>t\<in>A - {a}. F t)"
  apply (induct A arbitrary: a  rule: finite_induct)
   apply auto
  done

lemma Sum_mset_filter_mset:
  "finite A \<Longrightarrow>
   (\<Sum>t\<in>A. {#x \<in># M. t = x#}) = {#t' \<in># M. t' \<in> A#}"
  apply (induct M arbitrary: A rule: multiset_induct)
   apply simp_all
  apply safe
  subgoal for a N A
    apply (subst Sum_if_true)
      apply assumption+
    apply (metis insert_absorb sum.insert_remove union_mset_add_mset_left)
    done
  subgoal for a N A
    apply (subst Sum_if_false)
      apply assumption+
    apply simp
    done
  done

lemma image_mset_Sum:
  "finite S \<Longrightarrow>
   image_mset g (\<Sum>t\<in>S. f t) = (\<Sum>t\<in>S. image_mset g (f t))"
  apply (induct S rule: finite_induct)
   apply auto
  done

lemma Sum_image_set_snd:
  "(\<Sum>t\<in>fst ` set xs. image_mset snd {#x \<in># mset xs. t = fst x#}) = image_mset snd (\<Sum>t\<in>set xs. filter_mset ((=) t) (mset xs))"
  apply (subst image_mset_Sum)
   apply simp
  apply (induct xs)
   apply simp
  subgoal for x xs
    apply (cases x)
    apply (simp add: split_beta sum.insert_remove split: if_splits prod.splits)
    apply (smt (z3) Diff_empty Diff_insert0 List.finite_set add_cancel_right_left empty_filter_conv filter_mset_cong finite_imageI image_insert image_mset_is_empty_iff insertCI insert_Diff mset_filter mset_zero_iff_right sum.remove)
    done
  done

lemma image_mset_minus:
  "x \<in> set xs \<Longrightarrow>
   image_mset snd {#t' \<in># {#x#}. fst t' < t#} + (image_mset snd {#t' \<in># mset xs. fst t' < t#} - image_mset snd {#t' \<in># {#x#}. fst t' < t#}) =
   image_mset snd {#t' \<in># mset xs. fst t' < t#}"
  apply simp
  done

lemma Sum_set_image_mset[simp]:
  "(\<Sum>t\<in>fst ` {x \<in> set xs. fst x < t}. image_mset snd (filter_mset ((=) t \<circ> fst) (mset xs))) =
  image_mset snd (\<Sum>t\<in>fst ` {x \<in> set xs. fst x < t}. (filter_mset ((=) t \<circ> fst) (mset xs)))"
  by (simp add: image_mset_Sum)


lemma Collect_mset_filter_mset[simp]:
  "{#t' \<in># mset xs. t' \<in>  {x \<in> set xs. P (fst x)}#} = filter_mset (P \<circ> fst) (mset xs)"
  by (metis (mono_tags, lifting) comp_apply count_mset_0_iff filter_mset_cong mem_Collect_eq not_in_iff)

lemma Collect_add_mset:
  "{#x \<in># add_mset (a, b) M. P (fst x)#} = {#x \<in># M. P (fst x)#} + {#x \<in># {#(a, b)#}. P (fst x)#}"
  apply simp
  done

lemma Sum_filter_mset_mset:
  "(\<Sum>t\<in>{x \<in> set xs. P x}. filter_mset ((=) t) (mset xs)) = {#x \<in># mset xs. P x#}"
  apply (subst Sum_mset_filter_mset)
   apply simp
  apply (metis (no_types, lifting) filter_mset_cong mem_Collect_eq set_mset_mset)
  done

lemma filter_mset_image_mset:
  "filter_mset P (image_mset f xs) = image_mset f (filter_mset (P \<circ> f) xs)"
  by (metis comp_apply filter_mset_cong image_mset_filter_mset_swap)

lemma mset_Collect_filter_mset:
  "{#x \<in># M. P (f x)#} = filter_mset (P \<circ> f) M"
  by (metis comp_apply)

lemma Sum_mset_mset_image:
  "(\<Sum>t\<in>f ` {x \<in> set_mset M. P (f x)}. {#t' \<in># M. t = f t'#}) = {#x \<in># M. P (f x)#}"
  by (auto simp: multiset_eq_iff count_sum)

lemma Sum_mset_mset_fst:
  "(\<Sum>t\<in>fst ` {x \<in> set xs. P (fst x)}. filter_mset ((=) t \<circ> fst) (mset xs)) = {#x \<in># mset xs. P (fst x)#}"
  by (auto simp: multiset_eq_iff count_sum image_iff)

lemma sum_le_sum_lt_plus_1:
  "finite A \<Longrightarrow>
   t \<in> fst ` A \<Longrightarrow>
   (\<Sum>t\<in>{t' \<in> fst ` A. t' \<le> t}. g t) = (\<Sum>t\<in>{t' \<in> fst ` A. t' < t}. g t) + g (t::_::linorder)"
  apply (subgoal_tac "{t' \<in> fst ` A. t' \<le> t} = insert t {t' \<in> fst ` A. t' < t}")
   apply clarsimp
  using add.commute apply blast
  using Collect_cong insert_Collect by auto


lemma sum_le_sum_lt_plus_2:
  "finite A \<Longrightarrow>
   (t::_::linorder) \<notin> fst ` A \<Longrightarrow>
   (\<Sum>t\<in>{t' \<in> fst ` A. t' \<le> t}. g t) = (\<Sum>t\<in>{t' \<in> fst ` A. t' < t}. g t)"
  apply (subgoal_tac "{t' \<in> fst ` A. t' \<le> t} = {t' \<in> fst ` A. t' < t}")
   apply clarsimp
  using order_less_le by blast

lemma mset_collet_lt_le_plus[simp]:
  "{#(t', _) \<in># mset xs. t' \<le> t#} = {#(t', _) \<in># mset xs. t' < t#} + {#(t', _) \<in># mset xs. t' = (t::_::linorder)#}"
  apply (induct xs)
   apply auto
  done

lemma prefix_concat:
  "prefix xs ys \<Longrightarrow> prefix (concat xs) (concat ys)"
  by (metis concat_append prefix_def)

end