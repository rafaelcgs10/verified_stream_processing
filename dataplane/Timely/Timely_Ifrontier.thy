theory Timely_Ifrontier

imports
  Timely_Progress
  "../Lib/AntichainOrder"
begin

section \<open>Implied-Frontier Reasoning\<close>

abbreviation "ifrontier \<equiv> dataflow_topology.implied_frontier_alt"

lemma frontier_less_equal_ifrontierI:
  "dataflow_topology su (-+-) \<Longrightarrow>
   t' \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (frontier (c_pts c l)) t \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') (t + t')"
  apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_less_equal_sumI[where l=l])
     apply simp_all
   apply (simp add: sum_nonneg zcount_sum)
  apply (rule frontier_less_equal_sumI[of _ _ t'])
     apply simp_all
  unfolding frontier_less_equal_iff2
  apply clarsimp
  subgoal for t''
    apply (rule exI[of _ "t'' + t'"])
    apply clarsimp
    apply (rule in_frontierI)
     apply auto
     apply (metis frontier_idempotent in_frontier_iff pos_zcount_image_zmset zmset_of_mset_set_ge_zero)
    apply (metis (no_types, lifting) add_less_cancel_right dataflow_topology_from_tree.in_frontier_least frontier_idempotent pos_image_zmset_obtain_pre zmset_of_mset_set_ge_zero)
    done
  done

lemma in_frontier_zmset_image:
  "(\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   t \<in>\<^sub>A frontier {#t -+- s. t \<in>#\<^sub>z M#} \<longleftrightarrow> (\<exists> t'. t = t' -+- s \<and> t' \<in>\<^sub>A frontier M)"
  apply transfer
  apply (auto simp add: minimal_antichain_def)
    apply (metis (no_types, lifting) add_strict_right_mono pos_image_zmset_obtain_pre pos_zcount_image_zmset)
   apply (meson pos_zcount_image_zmset)
  apply (metis add_less_cancel_right pos_image_zmset_obtain_pre)
  done

lemma frontier_less_equal_ifrontierE:
  "frontier_less_equal (ifrontier su (-+-) c l') t \<Longrightarrow> 
   dataflow_topology su (-+-) \<Longrightarrow>
   \<exists> l s t'. s \<in>\<^sub>A graph.path_weight su l l' \<and> frontier_less_equal (frontier (c_pts c l)) t' \<and> t = t' + s"
  apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply simp_all
  apply (drule frontier_less_equal_sumE)
   apply clarsimp+
  apply (drule frontier_less_equal_sumE)
   apply clarsimp+
  subgoal for l s
    apply (rule exI[of _ l])
    apply (rule exI[of _ s])
    apply (intro conjI)
    using member_antichain.rep_eq apply blast
    subgoal premises prems
      using prems(3) apply -
      unfolding frontier_less_equal_iff2
      apply (clarsimp simp add: in_frontier_zmset_image)
      apply (metis add.commute add.left_commute dataflow_topology_from_tree.le_plus(2) less_eqE)
      done
    done
  done


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

lemma sum_zmset:
  "finite S \<Longrightarrow>
   (\<Sum>s\<in>S. {#t -+- s#}\<^sub>z) = zmset_of (mset_set (((-+-) t) ` S))"
  apply (induct S rule: finite_induct)
   apply simp_all
  subgoal for x S
    by (metis (no_types, lifting) add_left_imp_eq finite_imageI imageE mset_set.insert zmset_of_add_mset)
  done


lemma frontier_less_equal_ifrontier_trans:
  "dataflow_topology su (-+-) \<Longrightarrow>
   t' \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) t \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') (t -+- t')"
  apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (drule frontier_less_equal_ifrontierE)
   apply assumption
  apply clarsimp+
  subgoal for l' s t''
    apply (frule Graph.graph.path_weight_elem_trans[rotated, of s])
      apply assumption+
    using dataflow_topology.axioms(1) apply blast
    apply clarsimp
    subgoal for u
      apply (rule frontier_less_equal_sumI[of _ _ l'])
         apply (simp_all add: sum_nonneg zcount_sum)
      apply (rule frontier_less_equal_sumI[of _ _ u])
         apply (simp_all add: sum_nonneg zcount_sum)
      unfolding frontier_less_equal_iff2
      apply (clarsimp simp add: in_frontier_zmset_image)
      apply (metis dataflow_topology_from_tree.plus_mono group_cancel.add1)
      done
    done
  done

lemma frontier_less_equal_ifrontier_trans_alt2:
  "dataflow_topology su (-+-) \<Longrightarrow>
   s \<in>\<^sub>A graph.path_weight su l l' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l) t \<Longrightarrow>
   t -+- s \<le> t' \<Longrightarrow>
   frontier_less_equal (ifrontier su (-+-) c l') t'"
  using frontier_less_equal_ifrontier_trans frontier_less_equal_trans by blast


lemma frontier_le_image:
  "frontier M \<le> frontier M' \<Longrightarrow>
   (\<forall> t. zcount M' t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   frontier {#t -+- s. t \<in>#\<^sub>z M#} \<le> frontier {#t -+- s. t \<in>#\<^sub>z M'#}"
  unfolding less_eq_antichain_def
  apply clarsimp
  apply (metis add.commute add_left_mono in_frontier_zmset_image)
  done

lemma ifrontier_le_all_le:
  "dataflow_topology su (-+-) \<Longrightarrow>
   (\<forall> l' t'. t' \<in>\<^sub>A graph.path_weight su l' l \<longrightarrow> frontier (c_pts c l') \<le> frontier (c_pts c' l')) \<Longrightarrow>
   ifrontier su (-+-) c l \<le> ifrontier su (-+-) c' l"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_sum_le)
    apply simp_all
  subgoal
    apply (intro allI)
    apply (rule frontier_sum_le)
      apply simp_all
    subgoal for loc'
      apply (intro ballI)
      subgoal for s
        apply (drule spec[of _ loc'])
        apply (drule mp)
        using set_antichain1 apply blast
        apply (rule frontier_le_image)
          apply simp_all
        done
      done
    done
  subgoal
    by (simp add: sum_nonneg zcount_sum)
  done

lemma ifrontier_eq_all_le:
  "dataflow_topology su (-+-) \<Longrightarrow>
   (\<forall> l' t'. t' \<in>\<^sub>A graph.path_weight su l' l \<longrightarrow> frontier (c_pts c l') = frontier (c_pts c' l')) \<Longrightarrow>
   ifrontier su (-+-) c l = ifrontier su (-+-) c' l"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
   apply assumption
  apply (rule frontier_sum_eq)
     apply (simp_all add: sum_nonneg zcount_sum)
  apply (metis dataflow_topology_from_tree.elems_eq_sum_eq member_antichain.rep_eq)
  done

section \<open>Lemmas for ifrontier\<close>
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
                    by (smt (verit) D update_zmultiset_plus add.commute add_empty_zmultiset(2) dataflow_topology.results_in_zero dataflow_topology_from_tree.results_in_mono_raw in_frontier_addD le_iff_add
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
         subgoal for s
           apply simp
           apply (rule frontier_below_eq_frontier_plus_neg)
           using prems2(1) by (auto simp add: zcount_update_zmultiset)
        apply simp_all
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



end