theory ListUtils

imports
  Main
  "HOL-Library.Multiset"

begin

(* FIXME: move me *)
fun rmdups where
  "rmdups S [] = []"
| "rmdups S (x # xs) = (if x \<in> S then rmdups S xs else x # (rmdups (insert x S) xs))"

lemma set_rmdups[simp]:
  "set (rmdups S xs) = set xs - S"
  by (induct xs arbitrary: S) auto

lemma rmdups_rmdups[simp]:
  "rmdups S1 (rmdups S2 xs) = rmdups (S1 \<union> S2) xs"
  by (induct xs arbitrary: S1 S2) (auto simp add: insert_absorb)

lemma rmdups_append[simp]:
  "rmdups S (xs @ ys) = rmdups S xs @ rmdups (S \<union> set xs) ys"
  by (induct xs arbitrary: S ys) (auto simp add: insert_absorb)

lemma rmdups_cong:
  "A \<inter> set xs = B \<inter> set xs \<Longrightarrow>
   rmdups A xs = rmdups B xs"
  oops

lemma rmdups_NilI:
  "(set xs \<subseteq> A \<and> xs \<noteq> []) \<or> xs = [] \<Longrightarrow>
   rmdups A xs = []"
  apply (induct xs arbitrary: A)
   apply simp_all
  done

lemma rmdups_insert_NilI:
  "(set xs = {a} \<and> xs \<noteq> []) \<or> xs = [] \<Longrightarrow>
   rmdups (insert a A) xs = []"
  oops


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

lemma remove_last_append_singleton[simp]:
  "remove_last x (xs @ [x]) = xs"
  apply (induct x "xs @ [x]" rule: remove_last.induct)
  apply simp_all
  apply (metis append.right_neutral distinct.simps(2) distinct_singleton list.set_intros(1) remove_last_append_if remove_last_not_in_set_Cons)
  done

lemma remove_last_append_diff_singleton:
  "x \<noteq> y \<Longrightarrow> remove_last y (xs @ [x]) = remove_last y xs @ [x]"
  apply (induct y "xs @ [x]" rule: remove_last.induct)
  apply simp_all
  apply (subst remove_last_append_if)
  apply simp
  done

lemma remove_last_Cons_if:
  "remove_last a (a # xs) = (if a \<in> set xs then a # remove_last a xs else xs)"
  apply (induct xs rule: rev_induct)
  subgoal
    apply (simp del: remove_last.simps)
    apply (subst remove_last.simps)
    apply (simp del: remove_last.simps)
    done
  subgoal for x xs'
    apply (auto simp del: remove_last.simps split: if_splits)
    subgoal
      apply (subst remove_last.simps)
      apply (clarsimp simp del: remove_last.simps split: if_splits)
      done
    subgoal
      apply (subst remove_last.simps)
      apply (clarsimp simp del: remove_last.simps simp add: remove_last_append_diff_singleton split: if_splits)
      done
    subgoal
      apply (subst remove_last.simps)
      apply (clarsimp simp del: remove_last.simps split: if_splits)
      done
    subgoal
      apply (subst remove_last.simps)
      apply (clarsimp simp del: remove_last.simps simp add: remove_last_append_diff_singleton split: if_splits)
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

lemma list_diff_same_sufix:
  "mset ys = mset zs \<Longrightarrow>
   list_diff (xs @ zs) ys = xs"
  oops

lemma list_diff_append[simp]:
  "list_diff zs (xs @ ys) = list_diff (list_diff zs xs) ys"
  apply (induct xs arbitrary: zs ys)
  apply simp_all
  done

lemma list_diff_append_append:
  "mset zs1 = mset zs2 \<Longrightarrow>
   list_diff (xs @ zs1) (zs2 @ ys) = list_diff xs ys"
  oops

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

end
