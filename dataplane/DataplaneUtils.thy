theory DataplaneUtils

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.BNA_Operators
  Propagation_Extras.Executable
  Zero_Cyc_Check 
  Locations
begin 

abbreviation "isr x \<equiv> \<not> (isl x)"

lemma ldropWhile_LConsD:
  "ldropWhile P lxs = LCons x lxs' \<Longrightarrow>
   \<not> P x"
  by (metis lhd_ldropWhile llist.disc(2) llist.sel(1) lnull_ldropWhile)

lemma arg_cong3:
  "a = b \<Longrightarrow> c = d \<Longrightarrow> e = g \<Longrightarrow> f a c e = f b d g"
  by fast

lemma arg_cong4:
  "a = b \<Longrightarrow> c = d \<Longrightarrow> e = g \<Longrightarrow> h = i \<Longrightarrow> f a c e h  = f b d g i"
  by fast

lemma rel_set_image:
  "rel_set R (f ` A) B \<longleftrightarrow> rel_set (\<lambda> x. R (f x)) A B"
  "rel_set S A (g ` B) \<longleftrightarrow> rel_set (\<lambda> x y. S x (g y)) A B"
  unfolding rel_set_def
  apply auto
  done

lemma rel_set_reflI:
  "(\<And>x. x \<in> A \<Longrightarrow> R x x) \<Longrightarrow> rel_set R A A"
  unfolding rel_set_def
  apply auto
  done


lemma lhd_concat_ldropWhile:
  "lfinite (ltakeWhile ((=) []) lxs) \<Longrightarrow>
   \<exists> xs lxs'. ldropWhile ((=) []) lxs = LCons (x # xs) lxs' \<Longrightarrow>
   lhd (lconcat lxs) = x"
  apply (induct "ltakeWhile ((=) []) lxs"  arbitrary: lxs rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct split: prod.splits)
    apply (smt (z3) ldropWhile_LNil ldropWhile_simps(2) lhd_LCons lhd_lconcat llist.map_disc_iff llist.map_sel(1) llist_of.simps(2) lnull_def not_lnull_conv)
    done
  subgoal for lxs
    apply (cases lxs; simp split: if_splits)
    done
  done

lemma lhd_concat_ldropWhile_alt:
  "lfinite (ltakeWhile ((=) []) lxs) \<Longrightarrow>
   \<not> lnull (ldropWhile ((=) []) lxs) \<Longrightarrow>
   lhd (lconcat lxs) = hd (lhd (ldropWhile ((=) []) lxs))"
  apply (induct "ltakeWhile ((=) []) lxs"  arbitrary: lxs rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct split: prod.splits)
    apply (smt (z3) Coinductive_List_Auxiliary.lconcat_eq_LNil Coinductive_List_Auxiliary.lconcat_simps(1) lconcat_correct lhd_concat_ldropWhile lhd_ldropWhile list.collapse llist.collapse(2) lnull_imp_lfinite lnull_ldropWhile lset_LNil
        lset_eq_empty ltakeWhile_eq_LNil_iff)
    done
  subgoal for lxs
    apply (cases lxs; simp split: if_splits)
    done
  done

lemma lhd_lconcat_lmap_zip:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   lhd (lconcat (lmap (\<lambda>(xs, t). map (\<lambda>n. (n, t)) xs) (lzip inps (iterates Suc i)))) = (x, i + (the_enat (llength (ltakeWhile ((=) []) inps))))"
  apply (induct "ltakeWhile ((=) []) inps"  arbitrary: inps i rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct lnull_def split: prod.splits)
    apply (smt (z3) case_prod_conv iterates_lmap lappend_code(1) lappend_ltakeWhile_ldropWhile lhd_LCons lhd_lconcat lhd_llist_of list.map_disc_iff list.map_sel(1) llist.distinct(1) llist.map_disc_iff llist.map_sel(1) llist_of.simps(2)
        llist_of_eq_LNil_conv lzip.ctr(1) lzip.disc_iff(2) lzip.sel(1) lzip_eq_LNil_conv)
    done
  subgoal for lxs i
    apply (cases lxs; simp split: if_splits)
    subgoal for x lxs'
      apply (drule meta_spec[of _ lxs'])
      apply (drule meta_spec[of _ "Suc i"])
      apply simp
      apply (subst iterates.code)
      apply simp
      apply (metis eSuc_enat lfinite_llength_enat the_enat.simps)
      done
    done
  done

lemma ltl_lconcat_lmap_zip:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   ltl (lconcat (lmap (\<lambda>z. case z of (xs, t) \<Rightarrow> map (\<lambda>n. (n, t)) xs) (lzip inps (iterates Suc i)))) =
   Coinductive_List_Auxiliary.lconcat (lmap (\<lambda>z. case z of (xs, t) \<Rightarrow> map (\<lambda>n. (n, t)) xs) (lzip (LCons xs inps') (iterates Suc (i + (the_enat (llength (ltakeWhile ((=) []) inps)))))))"
  apply (induct "ltakeWhile ((=) []) inps"  arbitrary: inps i rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct lnull_def split: prod.splits)
    apply (subst ltl_lconcat)
    apply simp_all
    apply (metis (lifting) ldropWhile_LNil llist.distinct(1) lnull_def)
    apply (smt (z3) case_prod_conv ldropWhile_LNil list.map_disc_iff llist.distinct(1) llist.map_disc_iff llist.map_sel(1) llist_of.simps(1) llist_of_inject lnull_def lnull_iterates ltakeWhile_eq_LNil_iff lzip.sel(1)
        lzip_eq_LNil_conv)
    apply (smt (z3) lappend_code(1) lappend_ltakeWhile_ldropWhile lconcat_LCons lhd_LCons lhd_LCons_ltl lhd_lzip list.sel(3) llist.disc(2) llist.map_disc_iff llist.map_sel(1) lnull_iterates ltl_llist_of ltl_lmap ltl_lzip ltl_simps(2)
        lzip.disc(2) map_tl prod.simps(2))
    done
  subgoal for lxs i
    apply (cases lxs; simp split: if_splits)
    subgoal for x lxs'
      apply (drule meta_spec[of _ lxs'])
      apply (drule meta_spec[of _ "Suc i"])
      apply simp
      apply (subst the_enat_eSuc)
      using llength_eq_infty_conv_lfinite apply blast
      apply simp
      apply (subst iterates.code)
      apply simp
      done
    done
  done

fun to_zmset where
  "to_zmset [] = {#}\<^sub>z"
| "to_zmset (x # xs) = to_zmset xs + {# x #}\<^sub>z"

lemma to_zmset_correct[code,simp]:
  "zmset_of (mset xs) = to_zmset xs"
  by (induct xs) auto

lemma neg_neg_multiset:
  "- (A :: _ zmultiset) - B = - (A + B)"
  by (metis add.commute diff_minus_eq_add minus_diff_eq)

lemma add_zmset_neg:
  "add_zmset a (- M) = (add_zmset a {#}\<^sub>z) - M"
  by simp

lemma add_zmset_neg_add_zmset_if:
  "add_zmset a (- (add_zmset b M)) = (if a = b then - M else - (add_zmset b (M - {# a #}\<^sub>z)))"
  apply (auto split: if_splits)
   apply (metis add_zmset_diff_bothsides add_zmset_neg verit_minus_simplify(3))
  apply (metis arith_simps(56) diff_add_zmset_swap minus_diff_eq)
  done

lemma add_zmset_to_zmset:
  "add_zmset x (to_zmset xs) = to_zmset (x # xs)"
  by auto

lemma add_zmset_minus_to_zmset_if:
  "add_zmset x (- to_zmset xs) = (if x \<in> set xs then - to_zmset (remove1 x xs) else - to_zmset xs + {# x #}\<^sub>z)"
  apply (induct xs)
  apply (auto simp add: add_zmset_neg_add_zmset_if)
  apply (metis add_zmset_neg minus_diff_eq verit_eq_simplify(25))
  done

lemma set_antichain_antichain_singleton[simp]:
  "set_antichain (antichain {a}) = {a}"
  apply (subst antichain_inverse)
  apply (auto simp: incomparable_def)
  done


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

definition "antichain_equal A1 A2 = (is_empty_antichain (filter_antichain (\<lambda> x. x \<notin>\<^sub>A A2) A1) \<and> is_empty_antichain (filter_antichain (\<lambda> x. x \<notin>\<^sub>A A1) A2))"

lemma equal_antichain_equal:
  "antichain_equal A1 A2 \<longleftrightarrow> A1 = A2"
  unfolding antichain_equal_def
  apply auto
  apply (metis Set.is_empty_def ac_eq_iff filter_antichain.rep_eq is_empty_antichain.rep_eq member_antichain.rep_eq member_filter)
   apply (metis (lifting) ac_eq_iff filter_antichain.rep_eq is_empty_antichain_simp mem_antichain_nonempty member_antichain.rep_eq member_filter)+
  done

instantiation antichain :: (order) equal
begin
definition
  "equal_antichain = antichain_equal"
instance 
  apply standard
  subgoal for f1 f2
    unfolding equal_antichain_def
    apply (subst equal_antichain_equal)
    apply auto
    done
  done
end

lemma antichain_empty:
  "antichain {} = {}\<^sub>A"
  unfolding empty_antichain_def
  by auto

lemma frontier_negs[simp]:
  "frontier (- {# a #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a, b #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a, b, c #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a, b, c, d #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a, b, c, d, e #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a  :: _ :: {equal,order}, b, c, d, e, f #}\<^sub>z ) = {}\<^sub>A"
  unfolding frontier_def minimal_antichain_def
  by (simp add: antichain_empty)+



lift_definition del_zmset :: "'a \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" is
  "\<lambda>x (Mp, Mn). (Mp, add_mset x Mn)"
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
  "a \<in>#\<^sub>z add_zmset b M \<longleftrightarrow> a \<noteq> b \<and> a \<in>#\<^sub>z M \<or> a = b \<and> zcount M a \<noteq> -1"
  apply transfer
  apply auto
  done


instantiation prod :: (defaults, type) defaults
begin
definition defaults_prod where "defaults_prod = defaults \<times> defaults"
instance
proof qed
end


end