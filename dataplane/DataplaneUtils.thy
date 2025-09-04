theory DataplaneUtils

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.BNA_Operators
  Propagation_Extras.Executable
  Zero_Cyc_Check 
  Locations
begin 

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

end