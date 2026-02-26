theory Progress

imports
  General
  Dataplane.Timely_Stream
  Dataplane.MyProduct_Instances
  Dataplane.AntichainOrder
begin

declare cin.rep_eq[simp del]
declare enum_class.enum_UNIV[simp] enum_class.enum_distinct[simp]

lemma change_multiplicities_extract_prog_extract_progress[simp]:
  "nid \<in> set xs \<Longrightarrow>
   distinct xs \<Longrightarrow>
   st = snd (obtain_progress (os nid)) \<Longrightarrow>
   (change_multiplicities su (extract_prog xs nt (os(nid := fst (obtain_progress (os nid))))) (change_multiplicities su (extract_progress nid nt st) c)) =
   (change_multiplicities su (extract_prog xs nt os) c)"
  apply (induct xs arbitrary: c rule: rev_induct)
   apply simp_all
  subgoal for nid' xs
    apply (elim disjE)
    subgoal
      apply clarsimp
      apply hypsubst_thin
      unfolding extract_prog_def obtain_progress_def extract_progress_def
      apply (simp add: map_concat split_beta)
      apply (smt (verit) change_multiplicities_append_alt change_multiplicities_comm map_eq_conv)
      done
    subgoal
      apply clarsimp
      apply hypsubst_thin
      unfolding extract_prog_def obtain_progress_def extract_progress_def
      apply (auto simp add: change_multiplicities_append_alt map_concat split_beta)
      done
    done
  done


lemma c_imp_change_multiplicities[simp]:
  "c_imp (change_multiplicities su xs c) = c_imp c"
  apply (induct xs arbitrary: c)
   apply simp
  apply (auto split: if_splits prod.splits simp add: change_multiplicities_simp_alt update_zmultiset_plus_comm) 
  done

lemma frontier_add_le_l:
  "frontier A \<le> X \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> X"
  using frontier_below_eq_frontier_plus_pos order_trans_rules(23) by blast
lemma frontier_add_le_r:
  "frontier B \<le> X \<Longrightarrow>
   (\<forall> t. zcount A t \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> X"
  using frontier_below_eq_frontier_plus_pos order_trans_rules(23) by (metis Groups.add_ac(2))

lemma frontier_sum_le_one:
  "finite S \<Longrightarrow>
   loc \<in> S \<Longrightarrow>
   frontier (f loc) \<le> X \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   frontier (\<Sum>loc\<in>S. f loc) \<le> X"
  by (induct S  rule: finite_induct)
   (auto simp add: frontier_add_le_l frontier_add_le_r sum_nonneg zcount_sum)

lemma frontier_sum_le_one_alt:
  "finite S \<Longrightarrow>
   (\<forall> l \<in> S - {l1}. frontier (f l) = frontier (g l)) \<Longrightarrow>
   \<not> frontier (f l1) \<le> frontier (g l1) \<Longrightarrow>
   l1 \<noteq> l2 \<Longrightarrow>
   frontier (f l2) \<le> frontier (g l1) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (g l) t \<ge> 0) \<Longrightarrow>
   frontier (\<Sum>loc\<in>S. f loc) \<le> frontier (\<Sum>loc\<in>S. g loc)"
  oops

lemma le_frontier_frontier_less_equal:
  "\<forall> t \<in> fst ` set A. frontier_less_equal F t \<Longrightarrow>
   F \<le> frontier (zmset A)"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply auto
  subgoal for t
    apply transfer
    apply (auto simp add: zcount_zmset minimal_antichain_def)
    by (smt (verit, del_insts) case_prod_beta filter_empty_conv list.map(1) sum_list_simps(1))
  done

lemma frontier_le_minus_gen2:
  "X \<le> frontier B \<Longrightarrow>
   (\<forall> t. zcount C t \<ge> 0) \<Longrightarrow>
   X \<le> frontier (B - C)"
  by (meson dual_order.trans frontier_below_eq_frontier_minus)

lemma
  "frontier X \<le> frontier A \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount A t \<ge> 0) \<Longrightarrow>
   (\<forall> t t'. zcount X t > 0\<longrightarrow> zcount B t' > 0 \<longrightarrow> \<not> t < t' \<and> \<not> t' < t) \<Longrightarrow>
   (\<forall> t t'. zcount A t > 0 \<longrightarrow> zcount B t' > 0 \<longrightarrow> \<not> t < t' \<and> \<not> t' < t) \<Longrightarrow>
   frontier X \<le> frontier (A + B)"
  unfolding less_eq_antichain_def
  apply transfer'
  apply (auto simp add:  minimal_antichain_def)
  oops

lemma sorried:
  "finite S \<Longrightarrow>
   (\<forall> a\<in>S. \<forall> t. zcount (f a) t \<ge> 0) \<Longrightarrow>
   a \<in> S \<Longrightarrow>
   ft \<in>\<^sub>A frontier (f a) \<Longrightarrow>
   frontier_less_equal x ft \<Longrightarrow>
   f a \<noteq> {#}\<^sub>z \<Longrightarrow>
   (\<forall> a\<in>S. \<forall>b\<in>S. \<forall> t t'. zcount (f a) t > 0 \<longrightarrow> zcount (f b) t' > 0 \<longrightarrow> \<not> t < t' \<and> \<not> t' < t) \<Longrightarrow>
   x \<le> frontier (sum f S)"
  apply (induct S rule: finite_induct)
   apply simp_all
  subgoal for x' F
    apply auto
    subgoal 
      apply hypsubst_thin
      oops

lemma sorried:
  "finite S \<Longrightarrow>
   finite S' \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   (\<forall> l \<in> S'. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   (\<forall> l \<in> S. \<exists> l' \<in> S'. frontier (f l) \<le>  frontier (f l')) \<Longrightarrow>
   frontier (\<Sum>loc\<in>S. f loc) \<le> frontier (\<Sum>loc\<in>S'. f loc)"
  oops

lemma frontier_le_image_gen:
  "frontier M \<le> frontier M' \<Longrightarrow>
   (\<forall> t. zcount M' t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   s \<le> s' \<Longrightarrow>
   frontier {#t -+- s. t \<in>#\<^sub>z M#} \<le> frontier {#t -+- s'. t \<in>#\<^sub>z M'#}"
  unfolding less_eq_antichain_def
  apply clarsimp
  apply (metis dataflow_topology_from_tree.results_in_mono_raw in_frontier_zmset_image)
  done

lemma
  "finite S \<Longrightarrow>
   incomparable S \<Longrightarrow>
   A = antichain S \<Longrightarrow>
   ft \<in>#\<^sub>z (\<Sum>s\<in>S. {#t -+- s#}\<^sub>z) \<Longrightarrow> \<exists>s. s \<in>\<^sub>A A \<and> ft = t -+- s"
  oops

lemma sum_zmset:
  "finite S \<Longrightarrow>
   (\<Sum>s\<in>S. {#t -+- s#}\<^sub>z) = zmset_of (mset_set (((-+-) t) ` S))"
  apply (induct S rule: finite_induct)
   apply simp_all
  subgoal for x S
    by (metis (no_types, lifting) add_left_imp_eq finite_imageI imageE mset_set.insert zmset_of_add_mset)
  done

lemma frontier_le_subset[simp]:
  "frontier A \<le> frontier (zmset_of (mset_set {t' \<in> set_antichain (frontier A). P t'}))"
  unfolding less_eq_antichain_def
  apply auto
  apply transfer'
  apply (auto simp add: minimal_antichain_def)
  done

lemma frontier_less_equal_change_multiplicities_ge_0:
  assumes D: "dataflow_topology su (-+-)"
  shows 
    "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (ifrontier su (+) c l) t \<and> m \<ge> 0) \<Longrightarrow>
   ifrontier su (+) c l \<le> ifrontier su (+) (change_multiplicities su A c) l"
  apply (induct A arbitrary: c l rule: rev_induct)
   apply simp
  subgoal premises prems for a A c l
    using prems(2-) apply -
    apply clarsimp
    subgoal for l2 t m
      apply hypsubst_thin
      apply (subst change_multiplicities_comm)
      apply (subst change_multiplicities_append)
      apply (rule order.trans[rotated])
       apply (rule prems(1))
       apply simp_all
      subgoal
        apply clarsimp
        subgoal for l' t' m'
          apply (drule bspec)
           apply assumption
          apply clarsimp
          apply (rule frontier_less_equal_le_trans)
           apply assumption
          subgoal premises prems2
            using prems2(4) apply -
            apply (rule ifrontier_le_all_le[OF D])
            unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D]
            apply (clarsimp simp add: c_pts_change_multiplicities comp_def)
            apply (rule frontier_below_eq_frontier_plus_pos)
            using prems2(2) apply (simp add: zcount_update_zmultiset)
            done
          done
        done
      subgoal premises prems2
        using prems2(2,3) apply -
        unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D]
        apply (clarsimp simp add: c_pts_change_multiplicities comp_def)
        apply (drule frontier_less_equal_sumE)
         apply simp_all
        apply clarsimp
        apply (drule frontier_less_equal_sumE)
         apply simp_all
        apply clarsimp
        subgoal for l3 s'
          unfolding frontier_less_equal_iff2
          apply clarsimp
          subgoal for ft
            apply (subst (asm) in_frontier_zmset_image)
             apply simp_all
            apply clarsimp
            subgoal for ft'
              apply hypsubst_thin
              apply (cases "zcount (c_pts c l2) t + m > 0")
              subgoal
                apply (subst (1) comm_monoid_add_class.sum.subset_diff[where B="{l2,l3}"])
                  apply simp_all
                apply (subst (3) comm_monoid_add_class.sum.subset_diff[where B="{l2,l3}"])
                  apply simp_all
                apply (rule frontier_add_add_le)
                   apply (simp_all add: zcount_sum sum_nonneg)
                apply (cases "l2 = l3")
                subgoal
                  apply simp
                  apply (rule frontier_sum_le)
                    apply (simp_all add: zcount_sum sum_nonneg)
                  apply clarsimp
                  apply (rule frontier_le_image)
                    apply (simp_all add: zcount_sum sum_nonneg)
                  subgoal
                    by (smt (verit) D Timely_Infrastructure.update_zmultiset_plus add.commute add_empty_zmultiset(2) dataflow_topology.results_in_zero dataflow_topology_from_tree.results_in_mono_raw in_frontier_addD le_iff_add
                        less_eq_antichain_def zcount_union zcount_update_zmultiset)
                      (* slow but ok *)
                  done
                subgoal
                  apply simp
                  apply (cases "frontier_less_equal (frontier (c_pts c l2)) t")
                  subgoal
                    apply (rule frontier_add_add_le)
                       apply (simp_all add: zcount_sum sum_nonneg)
                    apply (rule frontier_sum_le)
                      apply (simp_all add: zcount_sum sum_nonneg)
                    apply clarsimp
                    apply (rule frontier_le_image)
                      apply (simp_all add: zcount_sum sum_nonneg)
                    apply (smt (verit, ccfv_threshold) frontier_below_eq_frontier_plus_pos frontier_less_equal_add_frontier_le_alt group_cancel.rule0 zcount_empty zcount_ne_zero_iff zcount_update_zmultiset)
                    done
                  subgoal
                    apply (subst set_antichain_frontier_add_update_zmultiset_le)
                      apply simp_all
                    apply (subst mset_set.insert)
                      apply simp_all
                    using frontier_less_equal_zcount_pos member_frontier_pos_zmset set_antichain1 apply blast
                    apply (subst add_zmset_add_single)
                    apply (simp only:  comm_monoid_add_class.sum.distrib)
                    apply (subst add.assoc)
                    apply (subst (7) add.commute)
                    apply (simp flip: add.assoc)
                    apply (rule frontier_less_equal_add_frontier_le_alt)
                    subgoal
                      apply auto
                      subgoal for ft
                        apply (rule frontier_less_equal_addI)
                          apply (simp_all add: zcount_sum sum_nonneg)
                        apply (rule disjI2)
                        apply (subst frontier_less_equal_frontier_sum_iff)
                          apply (simp_all add: zcount_sum sum_nonneg)
                        apply (subgoal_tac "\<exists> s. s \<in>\<^sub>A graph.path_weight su l2 l \<and> ft = t -+- s")
                        subgoal
                          apply clarsimp
                          subgoal for s''
                            apply (clarsimp simp flip: member_antichain.rep_eq)
                            apply (drule graph.path_weight_elem_trans[rotated, of s'])
                              apply assumption
                            subgoal
                              apply (rule dataflow_topology.axioms(1))
                              using D apply assumption
                              done
                            apply clarsimp
                            subgoal for u
                              apply (rule bexI[rotated])
                               apply (clarsimp simp flip: member_antichain.rep_eq)
                               apply assumption
                              unfolding frontier_less_equal_iff2
                              apply clarsimp
                              apply (rule exI[of _ "ft' -+- u"])
                              apply (auto simp add: in_frontier_zmset_image)
                              apply (smt (verit, del_insts) Groups.add_ac(2) add_le_imp_le_right add_mono_thms_linordered_semiring(1) group_cancel.add2)
                              done
                            done
                          done
                        subgoal
                          apply (subst (asm) sum_zmset)
                           apply simp_all
                          apply (clarsimp simp flip: member_antichain.rep_eq)
                          done
                        done
                      done
                    apply (rule frontier_add_add_le)
                       apply (simp_all add: zcount_sum sum_nonneg)
                    subgoal
                      apply (rule frontier_sum_le)
                        apply (simp_all add: zcount_sum sum_nonneg)
                      apply clarsimp
                      apply (rule frontier_le_image_gen)
                         apply (simp_all add: zcount_sum sum_nonneg)
                      done
                    done
                  done
                done
              subgoal
                apply (rule frontier_sum_le)
                  apply (simp_all add: zcount_sum sum_nonneg)
                apply (rule frontier_sum_le)
                  apply (simp_all add: zcount_sum sum_nonneg)
                apply clarsimp
                apply (rule frontier_le_image)
                  apply (simp_all add: frontier_add_update_zmultiset_not_le zcount_sum sum_nonneg)
                done
              done
            done
          done
        done
      done
    done
  done

lemma frontier_less_equal_change_multiplicities_lt_0:
  assumes D: "dataflow_topology su (-+-)"
  shows 
    "(\<forall> (l, t, m) \<in> set A. m < 0) \<Longrightarrow>
   ifrontier su (+) c l \<le> ifrontier su (+) (change_multiplicities su A c) l"
apply (induct A arbitrary: c l rule: rev_induct)
   apply simp
  subgoal premises prems for a A c l
    using prems(2-) apply -
    apply clarsimp
    subgoal for l2 t m
      apply hypsubst_thin
      apply (subst change_multiplicities_comm)
      apply (subst change_multiplicities_append)
      apply (rule order.trans[rotated])
       apply (rule prems(1))
       apply simp_all
      subgoal premises prems2
        using prems2(2-) apply -
        unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D]
        apply (clarsimp simp add: c_pts_change_multiplicities comp_def)
        apply (rule frontier_sum_le)
          apply (simp_all add: zcount_sum sum_nonneg)
                apply (rule frontier_sum_le)
          apply (simp_all add: zcount_sum sum_nonneg)
        apply clarsimp
                apply (rule frontier_le_image)
          apply (simp_all add: zcount_update_zmultiset frontier_add_update_zmultiset_not_le zcount_sum sum_nonneg)
        done
      done
    done
  done

lemma frontier_less_equal_change_multiplicities:
  assumes D: "dataflow_topology su (-+-)"
  shows 
    "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (ifrontier su (+) c l) t) \<Longrightarrow>
   ifrontier su (+) c l \<le> ifrontier su (+) (change_multiplicities su A c) l"
  apply (subgoal_tac "change_multiplicities su A c = change_multiplicities su (filter (\<lambda> (l, t, m). m < 0) A) (change_multiplicities su (filter (\<lambda> (l, t, m). m \<ge> 0) A) c)")
  subgoal premises prems
    apply (subst prems(2))
    apply (rule order.trans)
    apply (rule frontier_less_equal_change_multiplicities_ge_0[OF D, where A="filter (\<lambda>(l, t, m). m \<ge> 0) A"])
    using prems(1)
     apply simp
    apply force
    apply (rule order.trans)
    apply (rule frontier_less_equal_change_multiplicities_lt_0[OF D, where A="filter (\<lambda>(l, t, m). m < 0) A"])
     apply simp_all
    done
  subgoal premises prems
    apply (induct A rule: rev_induct)
     apply auto
    apply (smt (verit, best) change_multiplicities_append change_multiplicities_comm)+
    done
  done

lemma dataplane_tracker_inv_progress:
  "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   dataflow_topology (summ sg) (-+-) \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   st = snd (obtain_progress (os nid)) \<Longrightarrow>
   dataplane_tracker_inv (os(nid := fst (obtain_progress (os nid)))) cbufs (sg\<lparr>pt_tr := change_multiplicities (summ sg) (extract_progress nid (subgraph.nxt sg) st) (pt_tr sg)\<rparr>)"
 unfolding dataplane_tracker_inv_def
  apply (elim conjE exE)
  apply simp
  apply hypsubst_thin
  subgoal for c c' cgs chns caps
    apply (rule exI[of _ caps])
    apply (intro conjI)
    apply simp_all
    subgoal premises prems
      using prems(3) apply -
      unfolding Src_caps_inv_def obtain_progress_def
      apply auto
      done
    subgoal premises prems
      using prems(6) apply -     
      unfolding front_inv_def obtain_progress_def
      apply auto
      done
    subgoal premises prems
      using prems(7) apply -     
      unfolding imp_front_inv_def
      apply clarsimp
      subgoal for l
        apply (drule spec[of _ l])
        apply (rule order.trans)
         apply assumption
        apply (rule frontier_less_equal_change_multiplicities)
        using prems(1) apply assumption
        using prems(11) apply -
        unfolding changes_above_impl_inv_def extract_prog_def
        apply auto
        done
      done
    subgoal premises prems
      using prems(8) apply -  
      unfolding chnls_imp_front_inv_def
      sorry
    subgoal premises prems
      using prems(9) apply -  
      unfolding change_deltas_inv_def obtain_progress_def
      apply auto
      done
    subgoal premises prems
      using prems(10) apply - 
      sorry
    subgoal premises prems
      using prems(11,12) apply - 


      find_theorems c_imp change_multiplicities


end