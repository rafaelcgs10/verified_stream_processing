theory ListUtils

imports
  Main
  "HOL-Library.Multiset"
  "Automatic_Refinement.Misc"
begin

section \<open>Removing Duplicates\<close>

text \<open>The rmdups function and its set, distinctness, and append facts.\<close>

fun rmdups where
  "rmdups S [] = []"
| "rmdups S (x # xs) = (if x \<in> S then rmdups S xs else x # (rmdups (insert x S) xs))"

lemma set_rmdups[simp]:
  "set (rmdups S xs) = set xs - S"
  by (induct xs arbitrary: S) auto

lemma rmdups_append[simp]:
  "rmdups S (xs @ ys) = rmdups S xs @ rmdups (S \<union> set xs) ys"
  by (induct xs arbitrary: S ys) (auto simp add: insert_absorb)

section \<open>Removing the Last Occurrence and List Difference\<close>

text \<open>remove_last deletes the last occurrence of an element and list_diff
  removes one list from another, with append and membership facts.\<close>

fun remove_last where
  "remove_last x [] = []"
| "remove_last x xs = (if last xs = x then butlast xs else remove_last x (butlast xs) @ [last xs])"

lemma mset_remove_last[simp]:
  \<open>mset (remove_last x xs) = mset xs - {#x#}\<close>
proof (induction x xs rule: remove_last.induct)
  case 1
  thus ?case
    by simp
next
  case 2
  thus ?case
    using add_diff_cancel_right' append_butlast_last_id diff_union_single_conv list.simps(3) mset.simps(1,2)
      mset_append remove_last.elims
    by (smt (verit) diff_zero insert_DiffM insert_noteq_member minus_add_mset_if_not_in_lhs single_subset_iff subset_mset.add_diff_assoc2)
qed

lemma set_remove_lastD:
  \<open>y \<in> set (remove_last x xs) \<Longrightarrow> y \<in> set xs\<close>
  using in_diffD mset_remove_last set_mset_mset by metis

fun list_diff where
  "list_diff ys [] = ys"
| "list_diff ys (x # xs) = list_diff (remove_last x ys) xs"

lemma mset_list_diff[simp]:
  \<open>mset (list_diff ys xs) = mset ys - mset xs\<close>
  by (induction ys xs rule: list_diff.induct) simp_all

lemma list_diff_Nil[simp]:
  \<open>list_diff xs xs = []\<close>
  using mset_list_diff Multiset.diff_cancel mset_zero_iff by metis

lemma remove_last_not_Nil:
  "x \<notin> set xs \<Longrightarrow> remove_last x xs = xs"
  apply (induct xs rule: rev_induct)
  apply clarsimp
  subgoal for x' xs'
    apply simp
    apply (cases xs'; clarsimp)
    done
  done

lemma remove_last_in_set_Cons:
  "x \<in> set xs \<Longrightarrow> remove_last x (x' # xs) = x' # remove_last x xs"
  apply (induct xs rule: rev_induct)
  apply simp
  subgoal for x xs'
    apply (cases xs')
    subgoal
      by simp
    subgoal
      by fastforce
    done
  done

lemma remove_last_not_in_set_Cons:
  "x \<notin> set xs \<Longrightarrow> remove_last x (x # xs) = xs"
  apply (induct xs rule: rev_induct)
  apply simp
  subgoal for x xs'
    apply (cases xs')
    subgoal
      by simp
    subgoal
      by fastforce
    done
  done

lemma remove_last_append_if:
  "remove_last x (xs @ ys) = (if x \<in> set ys then xs @ remove_last x ys else remove_last x xs @ ys)"
  apply (induct xs arbitrary: ys rule: rev_induct)
  apply (clarsimp simp add: remove_last_not_Nil split: if_splits)
  subgoal premises prems for x' xs ys
    apply auto
    subgoal
      apply (subst prems(1))
      apply (simp del: remove_last.simps)
      apply (subst remove_last_in_set_Cons)
      apply auto
      done
    subgoal
      apply (subst prems(1))
      apply (clarsimp simp del: remove_last.simps)
      apply (intro conjI impI)
      subgoal
        apply (subst remove_last_not_in_set_Cons)
        using prems(1) apply auto
        done
      subgoal
        apply (subst prems(1))
        apply auto
        done
      done
    done
  done



lemma remove_last_append_in_set:
  "a \<in> set ys \<Longrightarrow>
   remove_last a (xs @ ys) = xs @ remove_last a ys"
  by (simp add: remove_last_append_if)

lemma remove_last_append_not_in_set:
  "a \<notin> set ys \<Longrightarrow>
   remove_last a (xs @ ys) = remove_last a xs @  ys"
  by (simp add: remove_last_append_if)

lemma list_diff_append[simp]:
  "list_diff zs (xs @ ys) = list_diff (list_diff zs xs) ys"
  apply (induct xs arbitrary: zs ys)
  apply simp_all
  done

lemma in_set_list_diffD:
  "x \<in> set (list_diff xs ys) \<Longrightarrow> x \<in> set xs"
  by (induct xs ys arbitrary: xs rule: list_diff.induct)
    (auto dest: set_remove_lastD)

lemma not_in_set_list_diff_same_count:
  "count (mset xs) y = count (mset ys) y \<Longrightarrow>
   y \<in> set (list_diff xs ys) \<Longrightarrow> False"
  apply (induct xs ys arbitrary: xs rule: list_diff.induct)
   apply clarsimp
  apply force
  done

lemma in_set_list_diffI[intro]:
  "x \<in> set xs \<Longrightarrow> x \<notin> set ys \<Longrightarrow> x \<in> set (list_diff xs ys)"
    apply (induct xs ys arbitrary: xs rule: list_diff.induct)
  apply clarsimp+
  subgoal premises prems for y xs ys
    apply (rule prems(1))
    using prems(2-) apply -
    apply (metis (no_types, lifting) in_set_conv_decomp remove_last_append_in_set remove_last_append_not_in_set remove_last_in_set_Cons set_ConsD)
    done
  done

lemma set_list_diff_filter[simp]:
  "set (list_diff xs (filter P xs)) = {x \<in> set xs. \<not> P x}"
  apply (induct "filter P xs" arbitrary: xs rule: rev_induct)
   apply (simp add: List.empty_filter_conv basic_trans_rules(24) subsetI)
  subgoal premises prems for x xs' xs''
    apply (auto dest: in_set_list_diffD)
    subgoal
      apply (drule not_in_set_list_diff_same_count[rotated])
       apply auto
      done
    done
  done


section \<open>Filtering and Searching\<close>

text \<open>Facts about filter, find, and counting on lists.\<close>

lemma filter_filter_True1_pair:
  "(\<forall> (x, y) \<in> set xs. Q y) \<Longrightarrow>
   filter (\<lambda>(x, y). Q y \<and> P y) xs = filter (P o snd) xs"
  by (smt (verit, ccfv_threshold) comp_apply filter_cong split_beta)

lemma filter_filter_pair_alt:
  "filter (\<lambda>(x, y). Q y \<and> P y) xs = filter (\<lambda> (x, y). P y) (filter (Q o snd) xs)"
  by (simp add: split_def)


lemma filter_snd_alt:
  "filter (\<lambda>x. P (snd x)) xs = filter (P o snd) xs"
  by (smt (verit, ccfv_threshold) comp_apply filter_cong split_beta)

lemma projl_fst:
  "(\<lambda>x. projl (fst x)) = fst o (\<lambda> (x, t). (projl x, t))"
  by auto

lemma filter_filter_commute_pair:
  "filter (\<lambda> (d, t). P t) (filter (\<lambda> (d, t). Q t) xs) = filter (\<lambda> (d, t). Q t) (filter (\<lambda> (d, t). P t) xs)"
  apply simp
  apply (rule filter_cong)
   apply auto
  done

lemma map_fst_filter_snd:
  "map (\<lambda>(x, y). (f x, y)) (filter (\<lambda>x. P (snd x)) xs) = filter (\<lambda>x. P (snd x)) (map (\<lambda>(x, y). (f x, y)) xs)"
  by (induct xs)
    auto

lemma find_None_if:
  "(\<forall> x\<in>set xs. \<not> P x) \<Longrightarrow>
   find P xs = None"
  by (metis find_None_iff2)

lemma count_list_gt_0[simp]:
  "0 < count_list xs x \<longleftrightarrow> x \<in> set xs"
  by (induct xs) auto

lemma find_SomeD':
  "find P xs = Some x \<Longrightarrow> P x \<and> x\<in>set xs"
  by (auto dest: find_SomeD)
lemma find_SomeD'':
  "Some x = find P xs \<Longrightarrow> P x \<and> x\<in>set xs"
  using find_SomeD' by metis


lemma find_Some_singleton:
  "{x \<in> set xs . P x} = {x} \<Longrightarrow>
   find P xs = Some x"
  apply (induct xs)
   apply simp_all
  apply (auto 0 0 simp add:)
   apply blast
  apply (smt (verit, best) Collect_cong)
  done

lemma filter_not_emptyI:
  "\<exists> x \<in> set xs. P x \<Longrightarrow>
   filter P xs \<noteq> []"
  by (metis List.empty_filter_conv)


section \<open>Sums and Mapped Filters\<close>

text \<open>Strict monotonicity of list sums and distribution of map over
  filters.\<close>

lemma sum_list_strict_mono_ex1:
  fixes xs :: \<open>'a list\<close>
    and f g :: \<open>'a \<Rightarrow> nat\<close>
  assumes le: \<open>\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x\<close>
    and strict: \<open>\<exists>x\<in>set xs. f x < g x\<close>
  shows \<open>sum_list (map f xs) < sum_list (map g xs)\<close>
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have le_a: \<open>f a \<le> g a\<close>
    using Cons.prems(1) by simp
  have le_tail: \<open>\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x\<close>
    using Cons.prems(1) by simp
  have tail_le: \<open>sum_list (map f xs) \<le> sum_list (map g xs)\<close>
    using le_tail
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons b ys)
    have head_le: \<open>f b \<le> g b\<close>
      using Cons.prems by simp
    have tail_le': \<open>sum_list (map f ys) \<le> sum_list (map g ys)\<close>
      using Cons.hyps Cons.prems by simp
    show ?case
      using head_le tail_le' by simp
  qed

  from Cons.prems(2) consider (head) \<open>f a < g a\<close> | (tail) \<open>\<exists>x\<in>set xs. f x < g x\<close>
    by auto
  then show ?case
  proof cases
    case head
    then show ?thesis
      using tail_le by simp
  next
    case tail
    have tail_strict: \<open>sum_list (map f xs) < sum_list (map g xs)\<close>
      using Cons.hyps[OF le_tail tail] .
    then show ?thesis
      using le_a by simp
  qed
qed


lemma fold_min_Min:
  fixes a :: "'a::linorder"
  shows "fold min xs a = Min (insert a (set xs))"
  by (metis Min.set_eq_fold list.simps(15))

lemma fold_min_le_base:
  fixes a :: "'a::linorder"
  shows "fold min xs a \<le> a"
  unfolding fold_min_Min by (intro Min_le) auto

lemma fold_min_le_mem:
  fixes a :: "'a::linorder"
  assumes "b \<in> set xs"
  shows "fold min xs a \<le> b"
  unfolding fold_min_Min using assms by (intro Min_le) auto

definition union_with where
  \<open>union_with f g h x = f (g x) (h x)\<close>

fun unions_with where
  \<open>unions_with f [] = undefined\<close>
| \<open>unions_with f (g # gs) = foldl (union_with f) g gs\<close>

primrec list_span where
  \<open>list_span _ [] = ([], [])\<close>
| \<open>list_span P (x # xs) =
    (if P x then let (ys, zs) = list_span P xs in (x # ys, zs) else ([], x # xs))\<close>

lemma list_span_length_le:
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length ys \<le> length xs\<close>
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length zs \<le> length xs\<close>
  by (induction xs arbitrary: ys zs) (auto split: if_splits prod.splits)

function group_by where
  \<open>group_by _ [] = []\<close>
| \<open>group_by f (x # xs) = (let (ys, zs) = list_span (f x) xs in (x # ys) # group_by f zs)\<close>
  by pat_completeness auto
termination by (lexicographic_order simp add: list_span_length_le)

definition insort_union where
  \<open>insort_union = fold insort_insert\<close>




lemma list_diff_append_mset_cancel:
  assumes \<open>mset zs = mset ys\<close>
  shows \<open>list_diff (xs @ zs) ys = xs\<close>
  using assms
proof (induct ys arbitrary: zs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then have y_in: \<open>y \<in> set zs\<close>
    using mset_eq_setD by fastforce
  have mset_zs: \<open>mset (remove_last y zs) = mset ys\<close>
    using Cons.prems by simp
  show ?case
    using Cons.hyps[OF mset_zs] y_in
    by (simp add: remove_last_append_in_set)
qed

lemma list_diff_append_cancel_right:
  \<open>list_diff (xs @ ys) ys = xs\<close>
  by (rule list_diff_append_mset_cancel) simp
end
