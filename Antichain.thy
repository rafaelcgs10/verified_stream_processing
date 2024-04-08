theory Antichain
  imports
    "Utils"
begin

fun maximal_antichain_list where
  "maximal_antichain_list [] = []"
| "maximal_antichain_list ((wm::_::order)#xs) = (let ma = maximal_antichain_list (filter (\<lambda> t. \<not> t \<le> wm) xs) in if \<exists> wm' \<in> set ma. wm \<le> wm' then ma else wm#ma)"

abbreviation maximal_antichain_spec where
  "maximal_antichain_spec xs \<equiv> (\<forall> (x::_::order) \<in> set xs. \<not> (\<exists> y\<in>set xs. y<x \<or> x<y))"

lemma maximal_antichain_filter_D:
  "wm \<in> set (maximal_antichain_list (filter P A)) \<Longrightarrow> P wm"
  apply (induct A arbitrary: P)
   apply (auto simp add: Let_def split: if_splits)
  done

lemma maximal_antichain_distinct_aux:
  "distinct (maximal_antichain_list (filter P A))"
  apply (induct A arbitrary: P)
   apply (auto simp add: Let_def split: if_splits)
  done

lemma maximal_antichain_distinct:
  "distinct (maximal_antichain_list A)"
  using maximal_antichain_distinct_aux[where P="\<lambda> _. True" and A =A] apply simp
  done

lemma maximal_antichain_filter_aux:
  "maximal_antichain_list (filter (\<lambda>t.  P t \<and> \<not> t \<le> wm) A) = filter (\<lambda>t. \<not> t \<le> wm) (maximal_antichain_list (filter P A))"
  apply (induct A arbitrary: P )
   apply (simp_all add: Let_def split: if_splits)
  apply (intro impI allI conjI)
  subgoal
    by (smt (verit, ccfv_SIG) filter_cong)
  subgoal
    by (smt (verit, ccfv_SIG) dual_order.trans filter_cong)
  subgoal
    by (smt (verit, ccfv_SIG) dual_order.trans filter_cong filter_set member_filter)
  subgoal
    by (smt (verit, best) dual_order.trans filter_cong)
  subgoal
    by (smt (verit, ccfv_SIG) filter_cong filter_is_subset subset_code(1))
  subgoal
    by (smt (verit, ccfv_SIG) filter_cong filter_is_subset subset_code(1))
  subgoal
    by (smt (verit, ccfv_SIG) filter_cong)
  subgoal
    by (smt (verit, best) dual_order.trans filter_cong)
  done

lemma maximal_antichain_filter[simp]:
  "maximal_antichain_list (filter (\<lambda>t. \<not> t \<le> wm) A) = filter (\<lambda>t. \<not> t \<le> wm) (maximal_antichain_list A)"
  using maximal_antichain_filter_aux[where A=A and P="\<lambda> _. True"] by simp

lemma maximal_antichain_correct:
  "maximal_antichain_spec (maximal_antichain_list A)"
  apply (induct A)
   apply (auto simp add: Let_def split: if_splits)
  done

lemma maximal_antichain_tl[simp]:
  "maximal_antichain_list (filter (\<lambda> t.  \<not> t \<le> hd (maximal_antichain_list A)) A) = tl (maximal_antichain_list A)"
  apply simp
  apply (rule filter_tl)
   apply simp_all
  using maximal_antichain_distinct[of A] maximal_antichain_correct[of  A] 
  by (metis antisym_conv2 distinct.simps(2) emptyE empty_set hd_in_set list.exhaust_sel list.sel(2) list.set_sel(2))

lemma maximal_incomparable:
  "(t::_::order) \<in> set (maximal_antichain_list xs) \<Longrightarrow>
   t' \<in> set (maximal_antichain_list xs) \<Longrightarrow>
   t \<noteq> t' \<Longrightarrow>
   \<not> t < t' \<and> \<not> t' < t"
  apply (induct xs)
   apply (auto simp add: Let_def split: if_splits)
  done

(* FIXME: move me *)
lemma drop_filter_maximal_antichain:
  "(t::_::order) \<in> set hs \<Longrightarrow>
   distinct buf \<Longrightarrow>
   (drop i ((filter (\<lambda>x. \<forall>xa\<in>set buf. \<not> x < xa) buf))) =
   wm # hs \<Longrightarrow>
   t \<le> wm \<Longrightarrow> False"
  apply (induct "buf" arbitrary: i t hs wm)
   apply (simp_all split: if_splits prod.splits)
   apply (smt (verit, del_insts) distinct.simps(2) distinct_drop distinct_filter dual_order.order_iff_strict filter_set list.set_intros(1) list.set_map map_eq_set_D member_filter set_ConsD set_drop_subset set_subset_Cons subset_code(1))
  apply (smt (verit, del_insts) filter_cong fst_conv order.strict_trans2 order_less_imp_le)
  done


lemma maximal_antichain_spec_filter:
  "maximal_antichain_spec xs \<Longrightarrow>
   maximal_antichain_spec (filter P xs)"
  apply auto
  done

lemma distincit_maximal_antichain_spec_correct:
  "distinct xs \<Longrightarrow>
   maximal_antichain_spec (filter (\<lambda> x . \<not> (\<exists>y \<in> set xs. (y::_::order) > x)) xs)"
  apply (simp add: )
  done

lemma maximal_antichain_spec_tail:
  "maximal_antichain_spec (x # xs) \<Longrightarrow> maximal_antichain_spec xs"
  apply auto
  done

lemma maximal_antichain_subset[simp]:
  "set (maximal_antichain_list buf) \<subseteq> set buf"
  apply (induct buf)
   apply (auto simp add: Let_def)
  done

lemma not_in_maximal_antichain:
  "t \<in> set xs \<Longrightarrow> t \<notin> set (maximal_antichain_list xs) \<Longrightarrow>
   \<exists>t'. t' \<in> set (maximal_antichain_list xs) \<and> t < t'"
  apply (induct xs)
   apply (simp_all add:  Let_def split: if_splits)
   apply (intro allI impI conjI)
  subgoal
    by (metis order.strict_trans2 order_le_neq_trans)
  subgoal
    by (metis order_class.order_eq_iff)
  subgoal
    by (metis antisym_conv2 dual_order.trans order_less_imp_le)
  done

lemma set_maximal_antichain[simp]:
  "set (maximal_antichain_list xs) = {t \<in> set xs. \<not> (\<exists> t' \<in> set xs. t < t')}"
proof -
  have "x \<in> set xs"
    if "x \<in> set (maximal_antichain_list xs)"
    for x :: 'a
    using that 
    using maximal_antichain_subset by blast
  moreover have False
    if "x \<in> set (maximal_antichain_list xs)"
      and "xa \<in> set xs"
      and "(x::'a) < xa"
    for x :: 'a
      and xa :: 'a
    using that 
    by (meson order.strict_trans maximal_antichain_correct not_in_maximal_antichain)
  moreover have "x \<in> set (maximal_antichain_list xs)"
    if "x \<in> set xs"
      and "\<forall>xa\<in>set xs. \<not> x < xa"
    for x :: 'a
    using that 
    using calculation(1) not_in_maximal_antichain by blast
  ultimately show ?thesis
    by (auto simp add: Let_def)
qed

lemma maximal_antichain_remove:
  "t \<in> set xs \<and> t' < t \<Longrightarrow> 
   maximal_antichain_list xs = maximal_antichain_list (filter (\<lambda> t.  \<not> t \<le> t') xs)"
  apply (simp add: Let_def split:)
  by (metis (no_types, lifting) filter_True mem_Collect_eq order_le_less_trans set_maximal_antichain)

lemma in_maximal_antichain:
  "t \<in> set (maximal_antichain_list xs) \<longleftrightarrow> t \<in> set xs \<and> (\<forall> t' \<in> set xs. \<not> t' > t)"
  by simp

lemma maximal_antichain_spec_takeWhile:
  "maximal_antichain_spec A \<Longrightarrow> maximal_antichain_spec (takeWhile P A)"
  apply (induct A)
   apply (auto 2 1 simp add: )[1]
  subgoal for a A
    by (metis set_takeWhileD)
  done

lemma count_list_antichain:
  "(wm::_::order) \<in> set (filter (\<lambda>ta. \<forall>x\<in>set buf. \<not> ta < x) buf) \<Longrightarrow>
    (t < wm \<or> wm < t) \<Longrightarrow>
   count_list (filter (\<lambda>ta. \<forall>x\<in>set buf. \<not> ta < x) buf) t = 0"
  by (metis (mono_tags, lifting) count_notin filter_set member_filter)

lemma maximal_antichain_covers_all:
  "t \<in> fst ` set buf \<Longrightarrow>
   \<exists> wm \<in> set (maximal_antichain_list (map fst buf)). t \<le> wm"
proof (induct buf arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons a buf)
  then show ?case 
  proof -
    have "\<exists>x\<in>set (let ma = filter (\<lambda>t. \<not> t \<le> fst a) (maximal_antichain_list (map fst buf)) in if \<exists>x\<in>set buf. (\<forall>xa\<in>set buf. \<not> fst x < fst xa) \<and> \<not> fst x \<le> fst a \<and> fst a \<le> fst x then ma else fst a # ma). t \<le> x"
      if "\<And>t. t \<in> fst ` set buf \<Longrightarrow> \<exists>x\<in>set buf. (\<forall>xa\<in>set buf. \<not> fst x < fst xa) \<and> t \<le> fst x"
        and "\<And>t. t \<in> fst ` set buf \<Longrightarrow> \<exists>a\<in>set (maximal_antichain_list (map fst buf)). t \<le> a"
        and "t \<in> fst ` set (a # buf)"
        and "t = fst a"
      using that 
      by (smt (z3) antisym_conv2 dual_order.order_iff_strict dual_order.strict_trans dual_order.trans filter_set finite_has_maximal2 imageI image_iff list.set_intros(1) member_filter not_in_maximal_antichain set_ConsD)
    moreover have "\<exists>x\<in>set (let ma = filter (\<lambda>t. \<not> t \<le> fst a) (maximal_antichain_list (map fst buf)) in if \<exists>x\<in>set buf. (\<forall>xa\<in>set buf. \<not> fst x < fst xa) \<and> \<not> fst x \<le> fst a \<and> fst a \<le> fst x then ma else fst a # ma). t \<le> x"
      if "\<And>t. t \<in> fst ` set buf \<Longrightarrow> \<exists>x\<in>set buf. (\<forall>xa\<in>set buf. \<not> fst x < fst xa) \<and> t \<le> fst x"
        and "\<And>t. t \<in> fst ` set buf \<Longrightarrow> \<exists>a\<in>set (maximal_antichain_list (map fst buf)). t \<le> a"
        and "t \<in> fst ` set (a # buf)"
        and "t \<in> fst ` set buf"
      using that
      unfolding Let_def
      apply (simp split: if_splits; intro conjI impI allI)
      subgoal
        by (metis order.trans)
      subgoal
        by (meson order_trans)
      done
    ultimately show ?thesis
      by (metis (no_types, lifting) Cons.prems dual_order.refl list.set_map not_in_maximal_antichain order_less_imp_le)
  qed
qed


definition "maximal_antichain_set WM = {(wm::_::order) \<in> WM. \<not> (\<exists> wm' \<in> WM. wm < wm')}"
abbreviation "maximal (wm::_::order) WM \<equiv> (\<forall> wm' \<in> WM. \<not> wm < wm')"
definition "maximal_complete WM \<equiv> \<forall> (x::_::order) \<in> WM. (\<exists>y\<in>WM. maximal y WM \<and> x \<le> y)"

lemma maximal_antichain_set_simps[simp]:
  "maximal_antichain_set {} = {}"
  unfolding maximal_antichain_set_def by auto

lemma maximal_complete_maximal_antichain_set[simp]:
  "maximal_complete (maximal_antichain_set A)"
  unfolding maximal_complete_def maximal_antichain_set_def
  apply auto
  done

lemma maximal_antichain_dup_set_simps[simp]:
  "maximal_antichain_set (maximal_antichain_set WM) = maximal_antichain_set WM"
  unfolding maximal_antichain_set_def
  by auto

lemma maximal_antichain_set_more_simps[simp]:
  "maximal_antichain_set {wm \<in> A. \<not> wm \<le> wm'} = {wm \<in> maximal_antichain_set A. \<not> wm \<le> wm'}"
  "maximal_antichain_set {wm \<in> A. \<not> wm < wm'} = {wm \<in> maximal_antichain_set A. \<not> wm < wm'}"
  "maximal_antichain_set {wm \<in> A.  wm \<ge> wm'} = {wm \<in> maximal_antichain_set A. wm \<ge> wm'}"
  "maximal_antichain_set {wm \<in> A.  wm > wm'} = {wm \<in> maximal_antichain_set A. wm > wm'}"
  "maximal_antichain_set {wm' \<in> maximal_antichain_set WM. P wm'} = {wm' \<in> maximal_antichain_set WM. P wm'}"
  unfolding maximal_antichain_set_def
      apply simp_all
  subgoal
    by auto
  subgoal
    using order.trans by auto
  subgoal
    by (metis order.strict_iff_not order.trans)
  subgoal
    by (metis order.strict_trans)
  subgoal
    by blast
  done

lemma maximal_antichain_set_union[simp]:
  "{wm \<in> maximal_antichain_set A. maximal wm B} \<union> {wm \<in> maximal_antichain_set B. maximal wm A} = maximal_antichain_set (A \<union> B)"
  unfolding maximal_antichain_set_def
  apply auto
  done  

lemma maximal_antichain_set_insert:
  "maximal_antichain_set (insert (wm::_::order) WM) =
   (if \<exists> wm' \<in> WM. wm < wm' 
    then maximal_antichain_set {wm' \<in> WM. \<not> wm' < wm}
    else (
      if \<exists> wm' \<in> maximal_antichain_set WM. wm < wm' 
      then maximal_antichain_set {wm' \<in> WM. \<not> wm' < wm} 
      else insert wm (maximal_antichain_set {wm' \<in> WM. \<not> wm' < wm})))"
  unfolding maximal_antichain_set_def
  apply auto
  done

lemma maximal_complete_union_finite:
  "finite B \<Longrightarrow> maximal_complete A \<Longrightarrow> maximal_complete (A \<union> B)"
  unfolding maximal_complete_def
  apply (induct B arbitrary: A rule: finite_induct)
   apply simp_all
  apply (rule conjI)
   apply (smt (verit, ccfv_SIG) order.trans leD order_less_imp_le)
  apply (smt (verit, del_insts) order.strict_trans nless_le)
  done

lemma maximal_antichain_set_insert_absorb:
  "wm' \<in> WM \<Longrightarrow>
   wm < wm' \<Longrightarrow>
   maximal_antichain_set (insert wm WM) = maximal_antichain_set WM"
  unfolding maximal_antichain_set_def
  apply auto
  done

lemma maximal_antichain_set_insert_maximal_antichain_set:
  "maximal_antichain_set (insert wm (maximal_antichain_set WM)) =
   (if \<exists> wm' \<in> maximal_antichain_set WM. wm < wm' then maximal_antichain_set WM else insert wm (maximal_antichain_set ({wm' \<in> WM. \<not> wm' < wm})))"
  apply (subst maximal_antichain_set_insert)
  unfolding maximal_antichain_set_def
  apply auto
  done


lemma maximal_complete_insert[simp]:
  "maximal_complete WM \<Longrightarrow> maximal_complete (insert wm WM)"
  unfolding maximal_complete_def
  apply simp
  apply (rule conjI)
   apply (metis dual_order.trans order.strict_iff_not)+
  done


lemma maximal_antichain_set_is_maximal:
  "wm \<in> maximal_antichain_set WM \<Longrightarrow>
   maximal wm WM"
  unfolding maximal_antichain_set_def
  apply auto
  done



lemma maxima_antichain_invar:
  "maximal_complete WM \<Longrightarrow>
   buf2 = maximal_antichain_set WM \<Longrightarrow>
   maximal_antichain_set (insert wm buf2) = maximal_antichain_set (insert wm WM)"
  unfolding maximal_antichain_set_def maximal_complete_def
  apply simp
  apply (intro Set.equalityI subsetI)
  subgoal
    apply simp
    apply (intro conjI)
     apply force+
    done
  subgoal
    by simp
  done

lemma maximal_antichain_set_insert_maximal_antichain_set_insert[simp]:
  "maximal_complete WM \<Longrightarrow>
   maximal_antichain_set (insert wm (maximal_antichain_set WM)) = maximal_antichain_set (insert wm WM)"
  unfolding maximal_antichain_set_def maximal_complete_def
  unfolding maximal_antichain_set_def maximal_complete_def
  apply simp
  apply (intro Set.equalityI subsetI)
  subgoal
    apply simp
    apply (intro conjI)
     apply fastforce+
    done
  subgoal
    by simp
  done


lemma maximal_antichain_set_complete:
  "maximal_complete WM \<Longrightarrow>
   wm \<in> WM \<Longrightarrow>
   \<exists> wm' \<in> maximal_antichain_set WM.  wm \<le> wm'"
  unfolding maximal_antichain_set_def maximal_complete_def
  apply auto
  done

lemma maximal_antichain_set_sound:
  "wm \<in> maximal_antichain_set WM \<Longrightarrow>
   wm \<in> WM \<and> (\<exists> wm' \<in> WM.  wm' \<le> wm)"
  unfolding maximal_antichain_set_def
  apply auto
  done

lemma maximal_maximal_antichain_set[simp]:
  "maximal_complete WM \<Longrightarrow>
   maximal wm (maximal_antichain_set WM) \<longleftrightarrow> maximal wm WM"
  unfolding maximal_antichain_set_def maximal_complete_def
  apply (intro iffI)
   apply fastforce+
  done

lemma maximal_complete_maximal_antichain_set_insert[simp]:
  "maximal_complete WM \<Longrightarrow>
   maximal wm WM \<Longrightarrow>
   maximal_antichain_set (insert wm WM) = insert wm {wma \<in> maximal_antichain_set WM. \<not> wma < wm}"
  unfolding maximal_antichain_set_def maximal_complete_def
  apply auto
  done


lemma maximal_maximal_antichain_set_False[simp]:
  "\<exists>x\<in>maximal_antichain_set WM. wm < x \<Longrightarrow>
   maximal wm WM \<Longrightarrow> 
   False "
  unfolding maximal_antichain_set_def
  apply auto
  done

lemma maximal_antichain_set_subset:
  "maximal_antichain_set WM \<subseteq> WM"
  unfolding maximal_antichain_set_def
  apply auto
  done

lemma maximal_antichain_set_maximal[simp]:
  "{wm \<in> maximal_antichain_set WM. maximal wm A} = maximal_antichain_set {wm \<in> WM. maximal wm A}"
  unfolding maximal_antichain_set_def
  apply (intro Set.equalityI Set.subsetI)
  subgoal
    apply simp
    done
  subgoal
    apply simp
    apply (metis order.strict_trans)
    done
  done

lemma maximal_antichain_set_insert_to_union[simp]:
  "maximal_antichain_set {wm. wm = wm' \<and> maximal wm WM} \<union> {wm \<in> maximal_antichain_set WM. \<not> wm < wm'} = maximal_antichain_set (insert wm' WM)"
  unfolding maximal_antichain_set_def
  apply auto
  done

lemma maximal_antichain_set_union_aux:
  "maximal_antichain_set {wm. wm \<in> A \<and> \<not> wm < wm' \<and> maximal wm WM} \<union> maximal_antichain_set {wm. (wm = wm' \<or> wm \<in> WM) \<and> maximal wm A} =
   maximal_antichain_set {wm. (wm = wm' \<or> wm \<in> A) \<and> maximal wm WM} \<union> maximal_antichain_set {wm \<in> WM. \<not> wm < wm' \<and> maximal wm A}"
  unfolding maximal_antichain_set_def
  apply (intro Set.equalityI Set.subsetI)
  subgoal
    apply simp
    apply (metis order.strict_trans)
    done
  subgoal
    apply simp
    apply (metis dual_order.strict_trans)
    done
  done

lemma maximal_antichain_set_union_aux2:
  "maximal_antichain_set {wma. Watermark wma \<in> A \<and> \<not> wma < wm \<and> maximal wma WM} \<union>
    maximal_antichain_set {wma. (wma = wm \<or> wma \<in> WM) \<and> maximal wma (Watermark -` A)} =
    maximal_antichain_set {wma. (wma = wm \<or> Watermark wma \<in> A) \<and> maximal wma WM} \<union>
    maximal_antichain_set {wma \<in> WM. \<not> wma < wm \<and> maximal wma (Watermark -` A)}"
  unfolding maximal_antichain_set_def
  apply (intro Set.equalityI Set.subsetI)
  subgoal
    apply simp
    apply (metis order.strict_trans vimageI)
    done
  subgoal
    apply simp
    apply (metis (full_types) order.strict_trans vimageD)
    done
  done

lemma maximal_antichain_set_maximal_antichain_set[simp]:
  "maximal_antichain_set (maximal_antichain_set A) = maximal_antichain_set A"
  unfolding maximal_antichain_set_def
  apply (auto 2 1)
  done

lemma maximal_antichain_set_union_maximal_antichain_set[simp]:
  "maximal_complete B \<Longrightarrow> 
   maximal_antichain_set (A \<union> maximal_antichain_set B) = maximal_antichain_set (A \<union> B)"
  unfolding maximal_antichain_set_def maximal_complete_def
  apply (intro Set.equalityI Set.subsetI)
  subgoal
    apply simp
    apply (smt (verit, ccfv_threshold) Un_iff dual_order.strict_trans1 mem_Collect_eq)
    done
  subgoal
    apply simp
    apply blast
    done
  done

lemma maximal_antichain_set_single:
  "maximal_antichain_set {wma. wma = wm \<and> maximal wma WM} = (if maximal wm WM then {wm} else {})"
  unfolding maximal_antichain_set_def
  apply auto
  done

lemma maximal_antichain_set_subset_2[simp]:
  "maximal_antichain_set {wma \<in> WM''. \<not> wma < wm} = {wma \<in> maximal_antichain_set WM''. \<not> wma < wm}"
  by force

lemma set_simp:
  "{wma. (wma = wm \<or> Watermark wma \<in> A) \<and> maximal wma B} =
   {wm' \<in> insert wm (Watermark -` A). maximal wm' B}"
  apply auto
  done

lemma maximal_antichain_linorder:
  "maximal_antichain_list (xs::'t::linorder list) = (if xs = [] then [] else [Max (set xs)])"
  apply (induct xs)
   apply simp
  apply (simp add: case_prod_unfold leI null_rec(1) null_rec(2) split: if_splits)
  apply (smt (verit) List.finite_set Max.coboundedI linorder_le_cases max.absorb2 order_trans)
  done

end