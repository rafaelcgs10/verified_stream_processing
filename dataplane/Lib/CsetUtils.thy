theory CsetUtils

imports
  ListUtils
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.CSet_LList_Impl
  Containers.Collection_Order

begin

section ‹Element Extraction and Cardinality›

text ‹Lifted operations for choosing elements and counting a cset.›

context includes cset.lifting begin
lift_definition cthe_elem :: "'m cset ⇒ 'm" is Set.the_elem .
lift_definition csome_elem :: "'m cset ⇒ 'm" is some_elem .
lift_definition ccard :: "'m cset ⇒ nat" is card .
lift_definition cinfinite :: "'m cset ⇒ bool" is Finite_Set.infinite.
end

lemma ccard_eq_0_iff[simp]:
  "(ccard A = 0) = (A = {||} ∨ cinfinite A)"
  unfolding ccard_def cinfinite_def
  by fastforce

section ‹From Lists and Lazy Lists›

text ‹Building csets from finite lists and lazy lists, with simp rules
  for the constructors.›

lemma cset_of_llist_llist_of_append[simp]:
  "cset_of_llist (llist_of (xs @ ys)) = cUn (cset_of_llist (llist_of xs)) (cset_of_llist (llist_of ys))"
  unfolding cset_of_llist_def
  apply (clarsimp simp flip: cin.rep_eq)
  apply (subst sup_cset.abs_eq)
    apply (simp_all add: countable_finite eq_onp_same_args)
  done

lemma in_cset_of_llist_llist_of[simp]:
  "x |∈| cset_of_llist (llist_of xs) ⟷ x ∈ set xs"
  using cin_code by force

lemma csubset_eq_cset_of_llist:
  "csubset_eq (cset_of_llist lxs) S ⟷ (∀ x ∈ lset lxs. x |∈| S)"
  using cin_code by fastforce


definition "cset_from_list = cset_of_llist o llist_of"

lemma cset_from_list_Nil[simp]:
  "cset_from_list [] = {||}"
  unfolding cset_of_llist_def cset_from_list_def
  by (clarsimp simp flip: cin.rep_eq bot_cset_def)

lemma cset_from_list_Cons[simp]:
  "cset_from_list (x # xs) = cinsert x (cset_from_list xs)"
  unfolding cset_from_list_def
  apply (clarsimp simp flip: cin.rep_eq)
  apply (metis cinsert_code)
  done

lemma cset_from_list_append[simp]:
  "cset_from_list (xs @ ys) = cUn (cset_from_list xs) (cset_from_list ys)"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done

lemma cset_from_list_map[simp]:
  "cset_from_list (map f xs) = (f |`| (cset_from_list xs))"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done

lemma cset_from_list_concat[simp]:
  "cset_from_list (concat xs) = cUnion (cset_from_list |`| (cset_from_list xs))"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  apply (meson in_cset_of_llist_llist_of rev_cBexI)
  done

lemma cset_from_list_rmdups[simp]:
  "cset_from_list (remdups xs) = cset_from_list xs"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done

lemma cset_from_list_filter[simp]:
  "cset_from_list (filter p xs) = cfilter p (cset_from_list xs)"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done

lemma rcset_cset_from_list[simp]:
  "rcset (cset_from_list xs) = set xs"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done

lemma in_cset_from_list[simp]:
  "x |∈| (cset_from_list xs) ⟷ x ∈ set xs"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done

lemma in_cimage_cset_from_list[simp]:
  "x |∈| (f |`| (cset_from_list xs)) ⟷ x ∈ f ` set xs"
  unfolding cset_from_list_def
  apply (auto simp flip: cin.rep_eq)
  done

lemma cset_of_llist_lshift[simp]:
  "cset_of_llist (xs @@- lxs) = cUn (cset_of_llist lxs) (cset_from_list xs)"
  apply (induct xs arbitrary: lxs)
  apply simp
  subgoal
    apply clarsimp
    apply (metis cinsert_code)
    done
  done

section ‹Filtering and Unions›

text ‹cfilter and cUnion distribution facts.›

lemma snd_cfilter[simp]:
  "snd |`| cfilter (λ(d, t). P t) S = cfilter P (snd |`| S)"
  by (force simp add: image_iff split_beta simp flip: cin.rep_eq)

lemma cimage_cfilter_clean:
  "(∀ x. x |∈| S ⟶ Q x ⟷ P x) ⟹
   (λt. F t (Q t)) |`| cfilter P S =
   ((λt. F t True) |`| cfilter P S)"
  by force

lemma cset_cfilter_split:
  "S = cUn (cfilter P S) (cfilter (Not o P) S)"
  by auto

lemma cUnion_cUn_distrib[simp]:
  "cUnion (cUn A B) = cUn (cUnion A) (cUnion B)"
  apply transfer
  apply (auto simp add:  cin.rep_eq)
  done

lemma cfilter_cinsert:
  "cfilter P (cinsert a A) = (if P a then cinsert a (cfilter P A) else cfilter P A)"
  by force

end
