theory ZmsetUtils

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.BNA_Operators
  Zero_Cyc_Check

begin

(* -------------------------------------------------------------------------- *)
(* to_zmset: list to zmultiset conversion                                     *)
(* -------------------------------------------------------------------------- *)

section \<open>From Lists to Signed Multisets\<close>

text \<open>to_zmset converts a list of positive updates into a signed multiset.\<close>

fun to_zmset where
  "to_zmset [] = {#}\<^sub>z"
| "to_zmset (x # xs) = to_zmset xs + {# x #}\<^sub>z"

lemma to_zmset_correct[code,simp]:
  "zmset_of (mset xs) = to_zmset xs"
  by (induct xs) auto

lemma to_zmset_nenneg[simp]:
  "zcount (to_zmset xs) t \<ge> 0"
  by (metis to_zmset_correct zcount_zmset_of_nonneg)

lemma neg_neg_multiset:
  "- (A :: _ zmultiset) - B = - (A + B)"
  by (metis add.commute diff_minus_eq_add minus_diff_eq)


lemma to_zmset_append[simp]:
  "to_zmset (xs @ ys) = to_zmset xs + to_zmset ys"
  by (induct xs arbitrary: ys rule: to_zmset.induct)
    auto


lemma add_zmset_to_zmset:
  "add_zmset x (to_zmset xs) = to_zmset (x # xs)"
  by auto

lemma to_zmset_map:
  "to_zmset (map f xs) = {#f x. x \<in>#\<^sub>z to_zmset xs#}"
  by (induct xs) auto

lemma to_zmset_filter:
  "to_zmset (filter P xs) = filter_zmset P (to_zmset xs)"
  by (induct xs) auto

lemma to_zmset_empty[simp]:
  "to_zmset xs = {#}\<^sub>z \<longleftrightarrow> xs = []"
  apply (induct xs)
   apply (simp_all flip: to_zmset_correct)
  by (metis add_zmset_to_zmset list.simps(2) mset_pos_empty mset_zero_iff to_zmset_correct zmset_of_inverse)


lemma zmset_of_replicate_mset[simp]:
  "zmset_of (replicate_mset m t) = to_zmset (replicate m t)"
  by (induct m) auto

lemma zcount_to_zmset:
  "zcount (to_zmset xs) = count_list xs"
  by (induct xs)
   auto

lemma set_zmset_to_zmset[simp]:
  "set_zmset (to_zmset xs) = set xs"
  unfolding set_zmset_def
  apply (induct xs)
   apply simp_all
  apply (smt (verit) Collect_cong insert_compr to_zmset_nenneg)
  done


(* -------------------------------------------------------------------------- *)
(* del_zmset                                                                  *)
(* -------------------------------------------------------------------------- *)

section \<open>Adding and Deleting Elements\<close>

text \<open>del_zmset and its interplay with add_zmset.\<close>

lift_definition del_zmset :: "'a \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" is
  "\<lambda>x (Mp, Mn). (Mp, add_mset x Mn)"
  by (auto simp: equiv_zmset_def)

lemma zcount_del_zmset[simp]:
  "zcount (del_zmset b A) a = (if b = a then zcount A a - 1 else zcount A a)"
  by transfer auto




(* -------------------------------------------------------------------------- *)
(* Equality instances                                                         *)
(* -------------------------------------------------------------------------- *)

section \<open>Executable Equality\<close>

text \<open>Equality instance for signed multisets.\<close>

instantiation zmultiset :: (equal) equal
begin
definition
  "equal_zmultiset A B = zequal A B"
instance
  apply standard
  subgoal for f1 f2
    unfolding equal_zmultiset_def zequal_equal
    apply auto
    done
  done
end


(* -------------------------------------------------------------------------- *)
(* zmset: (location * timestamp * multiplicity) list to zmultiset             *)
(* -------------------------------------------------------------------------- *)

section \<open>Signed Multisets of Update Lists\<close>

text \<open>The zmset of a list of signed updates and its zcount arithmetic.\<close>

fun zmset where
  "zmset [] = {#}\<^sub>z"
| "zmset ((x, d) # xs) = update_zmultiset (zmset xs) x d"

lemma update_zmultiset_plus[simp]:
  "update_zmultiset (A + B) x n = update_zmultiset A x n + B"
  apply transfer
  apply (auto simp: equiv_zmset_def)
  subgoal for A B A' B'
    apply (auto simp add: multiset_eq_iff split: if_splits)
    done
  done

lemma zmset_append[simp]:
  "zmset (xs @ ys) = zmset xs + zmset ys"
  apply (induct xs arbitrary: ys)
   apply auto
  done



lemma zmset_concat:
  "zmset (concat xs) = sum_list (map zmset xs)"
  by (induct xs) auto

lemma update_zmultiset_plus_comm:
  "update_zmultiset A x n + B = A + update_zmultiset B x n"
  apply transfer
  apply (auto simp: equiv_zmset_def)
  subgoal for A B A' B'
    apply (auto simp add: multiset_eq_iff split: if_splits)
    done
  done

lemma zmset_neg_alt[simp]:
  "zmset (map (\<lambda>x. (fst (snd x), - snd (snd x))) xs) = - zmset (map snd xs)"
  apply (induct xs)
   apply clarsimp+
  apply (metis Executable.update_zmultiset_plus add_eq_0_iff update_zmultiset_plus_comm update_zmultiset_simps(1))
  done


(* -------------------------------------------------------------------------- *)
(* zcount / zmset counting lemmas                                             *)
(* -------------------------------------------------------------------------- *)

lemma zcount_zmset_ge_0I:
  "(\<forall> (x, m) \<in> set xs. 0 \<le> m) \<Longrightarrow>
   zcount (zmset xs) t \<ge> 0"
  by (induct xs)
    (auto simp add: zcount_update_zmultiset)

lemma zcount_zmset_le_0I:
  "(\<forall> (x, m) \<in> set xs. x = t \<longrightarrow> 0 \<ge> m) \<Longrightarrow>
   zcount (zmset xs) t \<le> 0"
  by (induct xs)
    (auto simp add: zcount_update_zmultiset)


lemma gt_0_zcount_msetD:
  "0 < zcount (zmset (map snd (filter ((=) p \<circ> fst) xs))) t \<Longrightarrow>
   \<exists> m. (p, t, m) \<in> set xs \<and> 0 < m"
  apply (induct xs)
   apply (auto simp add: zcount_update_zmultiset  split: if_splits)
  subgoal for x xs'
    apply (cases "0 < zcount (zmset (map snd (filter ((=) p \<circ> fst) xs'))) t")
     apply auto
    done
  done

lemma zcount_zmset_gt_0I:
  "(\<forall> (x, m) \<in> set xs. 0 \<le> m) \<Longrightarrow>
   (t, m) \<in> set xs \<Longrightarrow>
   0 < m \<Longrightarrow>
   zcount (zmset xs) t > 0"
  apply (induct xs)
   apply (clarsimp simp add: zcount_update_zmultiset split: prod.splits)+
  apply (smt (verit, best) case_prodI2 zcount_zmset_ge_0I)
  done

lemma zmset_emptyI:
  "xs = [] \<Longrightarrow> zmset xs = {#}\<^sub>z"
  by auto


(* -------------------------------------------------------------------------- *)
(* Aggregation lemmas over zmset                                              *)
(* -------------------------------------------------------------------------- *)


lemma sum_list_zmset:
  "(\<Sum>x\<leftarrow>xs. zmset (f x)) = (zmset (concat (map f xs)))"
  apply (induct xs)
   apply auto
  done

lemma zmset_map_filter_aux[simp]:
  "finite S \<Longrightarrow>
   nid \<in> S \<Longrightarrow>
  (\<Sum>x\<in>S. zmset (map snd (filter (\<lambda>xa. nid = x) (filter (\<lambda>xa. p = fst xa) (xs x))))) = zmset (map snd (filter (\<lambda>x. p = fst x) (xs nid)))"
  apply (induct S rule: finite_induct)
   apply auto
  subgoal
    apply (rule comm_monoid_add_class.sum.neutral)
    apply clarsimp
    apply (rule zmset_emptyI)
    apply (auto simp add: filter_empty_conv)
    done
  subgoal
    by (metis (mono_tags, lifting) arith_extra_simps(12) diff_zero filter_False list.map(1) zmset.simps(1))
  done

lemma sum_zmset_neg[simp]:
  "(\<Sum>x\<in>S. - zmset (xs x)) = - (\<Sum>x\<in>S. zmset (xs x))"
  by (metis (mono_tags, lifting) add_eq_0_iff sum.distrib sum.not_neutral_contains_not_neutral)

lemma zmset_map_filter[simp]:
  "finite S \<Longrightarrow>
   nid \<in> S \<Longrightarrow>
   (\<Sum>x\<in>S. zmset (map snd ((filter (\<lambda>xa. nid = x \<and> p = fst xa) (xs x))))) =
   zmset (map snd (filter (\<lambda>x. p = fst x) (xs nid)))"
  by (subst conj.commute) (auto simp flip: filter_filter)

lemma zmset_map_one[simp]:
  "zmset (map (\<lambda> x. (f x, 1)) xs) = to_zmset (map f xs)"
  apply (induction xs)
   apply clarsimp+
  using update_zmultiset_one(2) apply fastforce
  done

lemma zmset_map_minus_one[simp]:
  "zmset (map (\<lambda> x. (f x, -1)) xs) = - to_zmset (map f xs)"
  apply (induction xs)
   apply clarsimp+
  apply (metis add_zmset_add_single neg_neg_multiset update_zmultiset_one(1))
  done

lemma sum_list_filter[simp]:
  "distinct nids \<Longrightarrow>
   nid \<in> set nids \<Longrightarrow>
   g [] = {#}\<^sub>z \<Longrightarrow>
   (\<Sum>x\<leftarrow>nids. g (map f (filter (\<lambda>xa. nid = x) (xs x)))) = g (map f (xs nid))"
  apply (induct nids)
   apply clarsimp+
  apply (elim disjE)
  subgoal for nids'
    by (smt (verit, best) List.empty_filter_conv filter_id_conv group_cancel.rule0 list.simps(8) sum.not_neutral_contains_not_neutral sum_list_distinct_conv_sum_set)
  subgoal for nid' nids'
    by (metis (mono_tags, lifting) add_cancel_right_left filter_empty_conv list.map(1))
  done

lemma set_zmset_zmset_of_mset_set[simp]:
  "finite S \<Longrightarrow>
   set_zmset (zmset_of (mset_set S)) = S"
  unfolding set_zmset_def
  by clarsimp

lemma image_zmset_empty_if:
  "M = {#}\<^sub>z \<Longrightarrow>
   image_zmset f M = {#}\<^sub>z"
  by simp
lemma zmset_of_empty_if:
  "M = {#} \<Longrightarrow>
   zmset_of M = {#}\<^sub>z"
  by simp
lemma mset_set_empty_if:
  "M = {} \<Longrightarrow>
   mset_set M = {#}"
  by simp


lemma pos_zcount_image_zmset_inj: 
  "0 < zcount M t \<Longrightarrow>inj f \<Longrightarrow>  0 < zcount (image_zmset f M) (f t)"
  apply transfer
  subgoal for M t f
    apply (induct M)
    subgoal for Mp Mn
      apply simp
      apply (metis basic_trans_rules(22) count_image_mset_ge_count count_image_mset_inj)
      done
    done
  done


lemma to_zmset_BULK_BENQ[simp]:
  "to_zmset ((xs >> ys) p) = to_zmset (xs p) + to_zmset (ys p)"
  unfolding BULK_BENQ_def
  by auto

lemma zcount_zmset_gt_0_set_Ex:
  "0 < zcount (zmset xs) x \<Longrightarrow> \<exists> m. (x, m) \<in> set xs \<and> m > 0"
  apply (induct xs)
   apply clarsimp+
  apply (smt (verit, ccfv_SIG) zcount_update_zmultiset)
  done

lemma zcount_zimageD:
  "zcount {#f t. t \<in>#\<^sub>z A#} t > 0 \<Longrightarrow>
   (\<exists> t'. zcount A t' > 0 \<and> t = f t')"
  apply transfer
  apply clarsimp
  apply (metis count_image_mset_lt_imp_lt)
  done
lemma zcount_to_zmset_gt_0[simp]:
  "zcount (to_zmset xs) t > 0 \<longleftrightarrow> t \<in> set xs"
  by (induct xs) (simp_all add: to_zmset_nenneg)

lemma in_frontier_minusI:
  "t \<in>\<^sub>A frontier A \<Longrightarrow>
   t \<noteq> t' \<Longrightarrow>
   t \<in>\<^sub>A frontier (A - {#t'#}\<^sub>z)"
  apply transfer'
  unfolding minimal_antichain_def
  apply auto
  done

lemma sum_subtractf_zmultiset:
  "finite A \<Longrightarrow>
   (\<Sum>x\<in>A. f x - g x) = sum (f :: 'b \<Rightarrow> 'a zmultiset) A - sum g A"
  apply (induct A rule: finite_induct)
   apply simp_all
  apply (metis (no_types, lifting) add_diff_eq diff_add_zmset uminus_add_add_uminus)
  done
end
