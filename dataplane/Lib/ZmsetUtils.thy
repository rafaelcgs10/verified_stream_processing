theory ZmsetUtils

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.BNA_Operators
  Zero_Cyc_Check

begin

(* -------------------------------------------------------------------------- *)
(* to_zmset: list to zmultiset conversion                                     *)
(* -------------------------------------------------------------------------- *)

section ‹From Lists to Signed Multisets›

text ‹to_zmset converts a list of positive updates into a signed multiset.›

fun to_zmset where
  "to_zmset [] = {#}⇩z"
| "to_zmset (x # xs) = to_zmset xs + {# x #}⇩z"

lemma to_zmset_correct[code,simp]:
  "zmset_of (mset xs) = to_zmset xs"
  by (induct xs) auto

lemma to_zmset_nenneg[simp]:
  "zcount (to_zmset xs) t ≥ 0"
  by (metis to_zmset_correct zcount_zmset_of_nonneg)

lemma neg_neg_multiset:
  "- (A :: _ zmultiset) - B = - (A + B)"
  by (metis add.commute diff_minus_eq_add minus_diff_eq)

lemma add_zmset_neg:
  "add_zmset a (- M) = (add_zmset a {#}⇩z) - M"
  by simp

lemma to_zmset_append[simp]:
  "to_zmset (xs @ ys) = to_zmset xs + to_zmset ys"
  by (induct xs arbitrary: ys rule: to_zmset.induct)
    auto

lemma add_zmset_neg_add_zmset_if:
  "add_zmset a (- (add_zmset b M)) = (if a = b then - M else - (add_zmset b (M - {# a #}⇩z)))"
  apply (auto split: if_splits)
   apply (metis add_zmset_diff_bothsides add_zmset_neg verit_minus_simplify(3))
  apply (metis arith_simps(56) diff_add_zmset_swap minus_diff_eq)
  done

lemma add_zmset_to_zmset:
  "add_zmset x (to_zmset xs) = to_zmset (x # xs)"
  by auto

lemma to_zmset_tl[simp]:
  "xs ≠ [] ⟹
   to_zmset (tl xs) = to_zmset xs - {# hd xs #}⇩z"
  by (induct xs)
    auto

lemma to_zmset_map:
  "to_zmset (map f xs) = {#f x. x ∈#⇩z to_zmset xs#}"
  by (induct xs) auto

lemma to_zmset_filter:
  "to_zmset (filter P xs) = filter_zmset P (to_zmset xs)"
  by (induct xs) auto

lemma to_zmset_empty[simp]:
  "to_zmset xs = {#}⇩z ⟷ xs = []"
  apply (induct xs)
   apply (simp_all flip: to_zmset_correct)
  by (metis add_zmset_to_zmset list.simps(2) mset_pos_empty mset_zero_iff to_zmset_correct zmset_of_inverse)

lemma add_zmset_minus_to_zmset_if:
  "add_zmset x (- to_zmset xs) = (if x ∈ set xs then - to_zmset (remove1 x xs) else - to_zmset xs + {# x #}⇩z)"
  apply (induct xs)
  apply (auto simp add: add_zmset_neg_add_zmset_if)
  apply (metis add_zmset_neg minus_diff_eq verit_eq_simplify(25))
  done

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

section ‹Adding and Deleting Elements›

text ‹del_zmset and its interplay with add_zmset.›

lift_definition del_zmset :: "'a ⇒ 'a zmultiset ⇒ 'a zmultiset" is
  "λx (Mp, Mn). (Mp, add_mset x Mn)"
  by (auto simp: equiv_zmset_def)

lemma zcount_del_zmset[simp]:
  "zcount (del_zmset b A) a = (if b = a then zcount A a - 1 else zcount A a)"
  by transfer auto

lemma uminus_add_zmset: "- add_zmset z M = del_zmset z (- M)"
  by (auto simp: zmultiset_eq_iff)

lemma add_del_zmset: "add_zmset x (del_zmset y M) = (if x = y then M else del_zmset y (add_zmset x M))"
  by (auto simp: zmultiset_eq_iff)

lemma del_zmset_commute[simp]:
  "del_zmset a (del_zmset b M) = del_zmset b (del_zmset a M)"
  by (auto simp: zmultiset_eq_iff)

lemma zmset_in_add_zmset[simp]:
  "a ∈#⇩z add_zmset b M ⟷ a ≠ b ∧ a ∈#⇩z M ∨ a = b ∧ zcount M a ≠ -1"
  apply transfer
  apply auto
  done


(* -------------------------------------------------------------------------- *)
(* Equality instances                                                         *)
(* -------------------------------------------------------------------------- *)

section ‹Executable Equality›

text ‹Equality instance for signed multisets.›

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

section ‹Signed Multisets of Update Lists›

text ‹The zmset of a list of signed updates and its zcount arithmetic.›

fun zmset where
  "zmset [] = {#}⇩z"
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

lemma minus_zmset:
  "- zmset ys = zmset (map (λ(x, m). (x, - m)) ys)"
  apply (induct ys rule: rev_induct)
   apply clarsimp+
  apply (smt (verit, del_insts) Executable.update_zmultiset_plus ZmsetUtils.update_zmultiset_plus add.commute add.inverse_distrib_swap add_cancel_left_left minus_unique)
  done

lemma zmset_minus:
  "zmset xs - zmset ys = zmset (xs @ map (λ (x, m). (x, -m)) ys)"
  apply (induct xs arbitrary: ys)
   apply (clarsimp simp add: minus_zmset)+
  apply (metis add_uminus_conv_diff minus_zmset)
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

lemma zmset_map_neg[simp]:
  "zmset (map (λ (t, m). (t, - m)) xs) = - zmset xs"
  apply (induct xs)
   apply clarsimp+
  apply (metis Executable.update_zmultiset_plus add_eq_0_iff update_zmultiset_plus_comm update_zmultiset_simps(1))
  done

lemma zmset_map_alt[simp]:
  "zmset (map (λx. (fst (snd x), snd (snd x))) xs) = zmset (map snd xs)"
  apply (induct xs)
   apply clarsimp+
  done

lemma zmset_neg_alt[simp]:
  "zmset (map (λx. (fst (snd x), - snd (snd x))) xs) = - zmset (map snd xs)"
  apply (induct xs)
   apply clarsimp+
  apply (metis Executable.update_zmultiset_plus add_eq_0_iff update_zmultiset_plus_comm update_zmultiset_simps(1))
  done


(* -------------------------------------------------------------------------- *)
(* zcount / zmset counting lemmas                                             *)
(* -------------------------------------------------------------------------- *)

lemma zcount_zmset_ge_0I:
  "(∀ (x, m) ∈ set xs. 0 ≤ m) ⟹
   zcount (zmset xs) t ≥ 0"
  by (induct xs)
    (auto simp add: zcount_update_zmultiset)

lemma zcount_zmset_le_0I:
  "(∀ (x, m) ∈ set xs. x = t ⟶ 0 ≥ m) ⟹
   zcount (zmset xs) t ≤ 0"
  by (induct xs)
    (auto simp add: zcount_update_zmultiset)

lemma zcount_zmset_eq_0I:
  "(∀ (t', m) ∈ set xs. t' ≠ t) ⟹
   zcount (zmset xs) t = 0"
  by (induct xs)
    (auto simp add: zcount_update_zmultiset)

lemma gt_0_zcount_msetD:
  "0 < zcount (zmset (map snd (filter ((=) p ∘ fst) xs))) t ⟹
   ∃ m. (p, t, m) ∈ set xs ∧ 0 < m"
  apply (induct xs)
   apply (auto simp add: zcount_update_zmultiset  split: if_splits)
  subgoal for x xs'
    apply (cases "0 < zcount (zmset (map snd (filter ((=) p ∘ fst) xs'))) t")
     apply auto
    done
  done

lemma zcount_zmset_gt_0I:
  "(∀ (x, m) ∈ set xs. 0 ≤ m) ⟹
   (t, m) ∈ set xs ⟹
   0 < m ⟹
   zcount (zmset xs) t > 0"
  apply (induct xs)
   apply (clarsimp simp add: zcount_update_zmultiset split: prod.splits)+
  apply (smt (verit, best) case_prodI2 zcount_zmset_ge_0I)
  done

lemma zmset_replicate[simp]:
  "zmset (replicate n (x, m)) = update_zmultiset {#}⇩z x (n * m)"
  by (induct n)
    (auto simp add: Groups.add_ac(2) distrib_right)

lemma zmset_emptyI:
  "xs = [] ⟹ zmset xs = {#}⇩z"
  by auto


(* -------------------------------------------------------------------------- *)
(* Aggregation lemmas over zmset                                              *)
(* -------------------------------------------------------------------------- *)

lemma sum_list_zmset:
  "(∑x←xs. zmset (f x)) = (zmset (concat (map f xs)))"
  apply (induct xs)
   apply auto
  done


lemma zmset_map_filter_aux[simp]:
  "finite S ⟹
   nid ∈ S ⟹
  (∑x∈S. zmset (map snd (filter (λxa. nid = x) (filter (λxa. p = fst xa) (xs x))))) = zmset (map snd (filter (λx. p = fst x) (xs nid)))"
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
  "(∑x∈S. - zmset (xs x)) = - (∑x∈S. zmset (xs x))"
  by (metis (mono_tags, lifting) add_eq_0_iff sum.distrib sum.not_neutral_contains_not_neutral)

lemma zmset_map_filter[simp]:
  "finite S ⟹
   nid ∈ S ⟹
   (∑x∈S. zmset (map snd ((filter (λxa. nid = x ∧ p = fst xa) (xs x))))) =
   zmset (map snd (filter (λx. p = fst x) (xs nid)))"
  by (subst conj.commute) (auto simp flip: filter_filter)

lemma zmset_map_one[simp]:
  "zmset (map (λ x. (f x, 1)) xs) = to_zmset (map f xs)"
  apply (induction xs)
   apply clarsimp+
  using update_zmultiset_one(2) apply fastforce
  done

lemma zmset_map_minus_one[simp]:
  "zmset (map (λ x. (f x, -1)) xs) = - to_zmset (map f xs)"
  apply (induction xs)
   apply clarsimp+
  apply (metis add_zmset_add_single neg_neg_multiset update_zmultiset_one(1))
  done

lemma sum_list_zmset_emptyI[intro]:
  "(∀ nid ∈ set nids. xs nid = []) ⟹
   (∑x←nids. zmset (map snd (xs x))) = {#}⇩z"
  apply (induct nids)
   apply auto
  done

lemma sum_list_filter[simp]:
  "distinct nids ⟹
   nid ∈ set nids ⟹
   g [] = {#}⇩z ⟹
   (∑x←nids. g (map f (filter (λxa. nid = x) (xs x)))) = g (map f (xs nid))"
  apply (induct nids)
   apply clarsimp+
  apply (elim disjE)
  subgoal for nids'
    by (smt (verit, best) List.empty_filter_conv filter_id_conv group_cancel.rule0 list.simps(8) sum.not_neutral_contains_not_neutral sum_list_distinct_conv_sum_set)
  subgoal for nid' nids'
    by (metis (mono_tags, lifting) add_cancel_right_left filter_empty_conv list.map(1))
  done

lemma set_zmset_zmset_of_mset_set[simp]:
  "finite S ⟹
   set_zmset (zmset_of (mset_set S)) = S"
  unfolding set_zmset_def
  by clarsimp

lemma image_zmset_empty_if:
  "M = {#}⇩z ⟹
   image_zmset f M = {#}⇩z"
  by simp
lemma zmset_of_empty_if:
  "M = {#} ⟹
   zmset_of M = {#}⇩z"
  by simp
lemma mset_set_empty_if:
  "M = {} ⟹
   mset_set M = {#}"
  by simp


lemma pos_zcount_image_zmset_inj: 
  "0 < zcount M t ⟹inj f ⟹  0 < zcount (image_zmset f M) (f t)"
  apply transfer
  subgoal for M t f
    apply (induct M)
    subgoal for Mp Mn
      apply simp
      apply (metis basic_trans_rules(22) count_image_mset_ge_count count_image_mset_inj)
      done
    done
  done

lemma to_zmset_concat:
  "to_zmset (concat xs) = sum_list (map to_zmset xs)"
  by (induct xs) auto

lemma zcount_image_zmset_image_zmset[simp]:
  "zcount (Auxiliary.image_zmset f (Auxiliary.image_zmset g (M t))) t = zcount {#f (g xa). xa ∈#⇩z M t#} t"
  apply transfer
  apply (auto simp add: split_beta)
  done

lemma to_zmset_BULK_BENQ[simp]:
  "to_zmset ((xs >> ys) p) = to_zmset (xs p) + to_zmset (ys p)"
  unfolding BULK_BENQ_def
  by auto

lemma zcount_zmset_gt_0_set_Ex:
  "0 < zcount (zmset xs) x ⟹ ∃ m. (x, m) ∈ set xs ∧ m > 0"
  apply (induct xs)
   apply clarsimp+
  apply (smt (verit, ccfv_SIG) zcount_update_zmultiset)
  done

lemma zcount_zimageD:
  "zcount {#f t. t ∈#⇩z A#} t > 0 ⟹
   (∃ t'. zcount A t' > 0 ∧ t = f t')"
  apply transfer
  apply clarsimp
  apply (metis count_image_mset_lt_imp_lt)
  done
lemma zcount_to_zmset_gt_0[simp]:
  "zcount (to_zmset xs) t > 0 ⟷ t ∈ set xs"
  by (induct xs) (simp_all add: to_zmset_nenneg)
lemma sum_le_0I:
  "finite A ⟹ (∀ x∈A. f x ≤ (0 :: int)) ⟹ (∑x∈A. f x)≤ 0"
  apply (induct A rule: finite_induct)
   apply simp_all
  done

lemma in_frontier_minusI:
  "t ∈⇩A frontier A ⟹
   t ≠ t' ⟹
   t ∈⇩A frontier (A - {#t'#}⇩z)"
  apply transfer'
  unfolding minimal_antichain_def
  apply auto
  done

lemma sum_subtractf_zmultiset:
  "finite A ⟹
   (∑x∈A. f x - g x) = sum (f :: 'b ⇒ 'a zmultiset) A - sum g A"
  apply (induct A rule: finite_induct)
   apply simp_all
  apply (metis (no_types, lifting) add_diff_eq diff_add_zmset uminus_add_add_uminus)
  done
end
