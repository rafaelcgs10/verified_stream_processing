theory DataplaneUtils

imports
  ZmsetUtils

begin

abbreviation "isr x ≡ ¬ (isl x)"

lemma ldropWhile_LConsD:
  "ldropWhile P lxs = LCons x lxs' ⟹
   ¬ P x"
  by (metis lhd_ldropWhile llist.disc(2) llist.sel(1) lnull_ldropWhile)

lemma arg_cong3:
  "a = b ⟹ c = d ⟹ e = g ⟹ f a c e = f b d g"
  by fast

lemma arg_cong4:
  "a = b ⟹ c = d ⟹ e = g ⟹ h = i ⟹ f a c e h  = f b d g i"
  by fast

lemma arg_cong5:
  "a = b ⟹ c = d ⟹ e = g ⟹ h = i ⟹ j = k ⟹ f a c e h j  = f b d g i k"
  by fast

lemma lmap_lshift[simp]:
  "lmap f (xs @@- lxs) = map f xs @@- lmap f lxs"
  by (metis lappend_llist_of lmap_lappend_distrib lmap_llist_of)

lemma lfinite_lshift[simp]:
  "lfinite (xs @@- lxs) = lfinite lxs"
  by (metis lappend_llist_of lfinite_lappend lfinite_llist_of)

lemma list_of_lshift:
  "lfinite lxs ⟹
   list_of (xs @@- lxs) = xs @ list_of lxs"
  apply (induct xs arbitrary: lxs)
   apply (simp_all add: list_of_LCons_conv split: if_splits)
  done

lemma rel_set_image:
  "rel_set R (f ` A) B ⟷ rel_set (λ x. R (f x)) A B"
  "rel_set S A (g ` B) ⟷ rel_set (λ x y. S x (g y)) A B"
  unfolding rel_set_def
  apply auto
  done

lemma rel_set_reflI:
  "(⋀x. x ∈ A ⟹ R x x) ⟹ rel_set R A A"
  unfolding rel_set_def
  apply auto
  done

lemma BAPPEND_BENQ_BHD'[simp]:
  "buf1 p ≠ [] ⟹ BHD p buf1 = x ⟹ (BTL p buf1) >> (BENQ p x buf2) = buf1 >> buf2"
  unfolding BULK_BENQ_def BTL_def BENQ_def BHD_def by force

lemma BHD_map[simp]:
  "buf p ≠ [] ⟹
   BHD p (λx. map f (buf x)) = f (BHD p buf)"
  unfolding BHD_def
  apply (auto simp add: hd_map)
  done


lemma lhd_concat_ldropWhile:
  "lfinite (ltakeWhile ((=) []) lxs) ⟹
   ∃ xs lxs'. ldropWhile ((=) []) lxs = LCons (x # xs) lxs' ⟹
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
  "lfinite (ltakeWhile ((=) []) lxs) ⟹
   ¬ lnull (ldropWhile ((=) []) lxs) ⟹
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
  "lfinite (ltakeWhile ((=) []) inps) ⟹
   ldropWhile ((=) []) inps = LCons (x # xs) inps' ⟹
   lhd (lconcat (lmap (λ(xs, t). map (λn. (n, t)) xs) (lzip inps (iterates Suc i)))) = (x, i + (the_enat (llength (ltakeWhile ((=) []) inps))))"
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
  "lfinite (ltakeWhile ((=) []) inps) ⟹
   ldropWhile ((=) []) inps = LCons (x # xs) inps' ⟹
   ltl (lconcat (lmap (λz. case z of (xs, t) ⇒ map (λn. (n, t)) xs) (lzip inps (iterates Suc i)))) =
   Coinductive_List_Auxiliary.lconcat (lmap (λz. case z of (xs, t) ⇒ map (λn. (n, t)) xs) (lzip (LCons xs inps') (iterates Suc (i + (the_enat (llength (ltakeWhile ((=) []) inps)))))))"
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

instantiation prod :: (defaults, type) defaults
begin
definition defaults_prod where "defaults_prod = defaults × defaults"
instance
proof qed
end

lemma cfilter_cinsert:
  "cfilter P (cinsert a A) = (if P a then cinsert a (cfilter P A) else cfilter P A)"
  by force

end
