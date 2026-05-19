theory Propagates

imports
  General
  Dataplane.Timely_Stream
  Dataplane.MyProduct_Instances
  Dataplane.AntichainOrder
begin


lemma propagate_all_preserves_c_pts:
  assumes "propagate_all summary c = Some c'"
  shows "c_pts c' = c_pts c"
  apply (rule while_option_rule[rotated, OF assms[unfolded propagate_all_def comp_def]])
  apply simp
  apply (simp only: take_step_PR_preserves_c_pts)
  done

lemma propagate_all_preserves_inv:
  "propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> 't:: {ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} antichain) c = Some c' \<Longrightarrow>
   dataflow_topology summary (-+-) \<Longrightarrow>
   ID CCOMPARE('t) = Some compare \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary (-+-) c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary (-+-) c'"
  unfolding propagate_all_def
  subgoal
    apply (drule while_option_rule[rotated])
    defer
    apply (rule take_step_PR_p_preserves_inv)
    apply assumption+
    apply simp_all
    subgoal
      unfolding worklist_is_empty_def 
      apply clarsimp
      apply blast
      done
    done
  done

lemma propagate_all_frontier_c_imp_correctness_aux:
  "propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> 't:: {ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} antichain) c = Some c' \<Longrightarrow>
   dataflow_topology summary (-+-) \<Longrightarrow>
   ID CCOMPARE('t) = Some compare \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary (-+-) c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   (t \<in>\<^sub>A frontier (c_imp c' loc)) = (t \<in>\<^sub>A ifrontier summary (-+-) c' loc) \<and>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary (-+-) c'"
  apply (frule propagate_all_preserves_inv)
  apply assumption+
  unfolding propagate_all_def worklist_is_empty_def
  apply (frule while_option_stop2)
  apply (intro conjI)
  apply (rule Propagate.dataflow_topology.implication_frontier_iff_implied_frontier_alt_vacant)
  apply simp_all
  apply (rule Propagate.dataflow_topology.empty_worklists_vacant_to)
  apply auto
  done

lemma propagate_all_frontier_c_imp_correctness_aux2:
  "propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> 't:: {ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} antichain) c = Some c' \<Longrightarrow>
   dataflow_topology summary (-+-) \<Longrightarrow>
   ID CCOMPARE('t) = Some compare \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary (-+-) c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   frontier (c_imp c' loc) = ifrontier summary (-+-) c' loc \<and>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary (-+-) c'"
  using propagate_all_frontier_c_imp_correctness_aux by (metis dataflow_topology.antichain_eqI)

lemma propagate_all_preserves_ifrontier:
  "propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> 't:: {ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} antichain) c = Some c' \<Longrightarrow>
   dataflow_topology summary (-+-) \<Longrightarrow>
   ifrontier summary (-+-) c' loc = ifrontier summary (-+-) c loc"
  apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def)
  apply assumption
  using propagate_all_preserves_c_pts apply force
  done

lemma propagate_all_frontier_c_imp_correctness:
  "propagate_all (summary :: _ \<Rightarrow> _ \<Rightarrow> 't:: {ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} antichain) c = Some c' \<Longrightarrow>
   dataflow_topology summary (-+-) \<Longrightarrow>
   ID CCOMPARE('t) = Some compare \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary (-+-) c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   frontier (c_imp c' loc) = ifrontier summary (-+-) c loc \<and>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary (-+-) c'"
  using propagate_all_frontier_c_imp_correctness_aux2 propagate_all_preserves_ifrontier by fastforce

lemma c_pts_change_multiplicities_cong:
  "c_pts c loc = c_pts c' loc \<Longrightarrow>
   c_pts (change_multiplicities su cbs c) loc = c_pts (change_multiplicities su cbs c') loc"
  apply (induct cbs arbitrary: c c')
  apply simp
  subgoal premises prems for a cbs c c'
    using prems(2-) apply -
    apply (cases a)
    apply (auto split: prod.splits simp add: change_multiplicities_simp_alt)
    using prems(1) apply metis+
    done
  done


lemma dataplane_tracker_inv_front_update:
  assumes D: "dataflow_topology (summ sg) (-+-)"
    and T: "ID CCOMPARE('t) = Some compare"
    and R: "reachable_locations (summ sg) = UNIV"
  shows  "propagate_all ((summ sg) :: _ \<Rightarrow> _ \<Rightarrow> 't:: {ccompare,compare_order,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} antichain) (pt_tr sg) = Some c \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   dataplane_tracker_inv (map_entry nid (front_update (\<lambda>_. frontier \<circ> (\<lambda>p. c_imp c (Loc nid (Trg p))))) os) cbufs (sg\<lparr>pt_tr := c\<rparr>)"
  unfolding dataplane_tracker_inv_def
  apply (elim conjE exE)
  apply simp
  apply hypsubst_thin
  subgoal for c' c'' cgs chns caps
    apply (rule exI[of _ caps])
    apply (intro conjI)
    subgoal premises prems
      using prems(3) apply -
      unfolding Src_caps_inv_def obtain_progress_def
      apply auto
      done
    subgoal premises prems
      using prems(4) apply -     
      unfolding Trg_caps_inv_def
      apply (auto simp add: outputs_at_target_def BULK_BENQ_def split: prod.splits)
      done
    subgoal premises prems
      using prems(5) apply -   
      unfolding c_pts_inv_def extract_prog_def extract_progress_def obtain_progress_def
      apply (auto simp add: c_pts_change_multiplicities  split: prod.splits option.splits)
      subgoal for l
        apply (drule spec[of _ l])
        apply (drule sym)
        apply (auto simp add: monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat map_concat filter_concat comp_def split_beta c_pts_change_multiplicities  split: option.splits)
        using prems(1) propagate_all_preserves_c_pts apply fastforce
        done
      done
    subgoal premises prems
      using prems(6) apply -   
      unfolding front_inv_def
      apply auto
      subgoal premises temp for nid' p
        apply (subgoal_tac "frontier (c_imp c (Loc nid' (Trg p))) = ifrontier (summ sg) (-+-) (pt_tr sg) (Loc nid' (Trg p))")
        subgoal
          by (metis imp_front_inv_def order_trans_rules(23) prems(7) temp(1))
        subgoal
          using prems(1) apply -
          apply (drule propagate_all_frontier_c_imp_correctness[OF _ D T R, where loc="Loc nid' (Trg p)"])
          using prems(10)[unfolded propagation_inv_def]
          apply auto
          done
        done
      done
    subgoal premises prems
      using prems(7) apply -   
      unfolding imp_front_inv_def
      apply auto
      subgoal for l
        apply (subgoal_tac "frontier (c_imp c l) = ifrontier (summ sg) (-+-) (pt_tr sg) l")
        subgoal
          by (metis Orderings.order_eq_iff assms(1) prems(1) propagate_all_preserves_ifrontier)
        subgoal
          using prems(1) apply -
          apply (drule propagate_all_frontier_c_imp_correctness[OF _ D T R, where loc=l])
          using prems(10)[unfolded propagation_inv_def]
          apply auto
          done
        done
      done
    subgoal premises prems
      using prems(8) apply -   
      unfolding chnls_imp_front_inv_def
      apply auto
      subgoal for nid' p a b
        apply (drule spec2[of _ nid' p])
        apply (drule bspec[of _ _ "(a, b)"])
        subgoal
          unfolding outputs_at_target_def BULK_BENQ_def
          apply (auto split: if_splits)
          done
        subgoal
          apply (subgoal_tac "frontier (c_imp c (Loc nid' (Trg p))) = ifrontier (summ sg) (-+-) (pt_tr sg) (Loc nid' (Trg p))")
          subgoal
            by (metis assms(1) prems(1) prod.sel(2) propagate_all_preserves_ifrontier)
          subgoal
            using prems(1) apply -
            apply (drule propagate_all_frontier_c_imp_correctness[OF _ D T R, where loc="Loc nid' (Trg p)"])
            using prems(10)[unfolded propagation_inv_def]
            apply auto
            done
          done
        done
      done
    subgoal premises prems
      using prems(9)
      unfolding change_deltas_inv_def
      by auto
    subgoal premises prems
      using prems(10)
      unfolding propagation_inv_def
      using T assms(1) prems(1) propagate_all_preserves_inv by blast
    subgoal premises prems
      using prems(11) apply -
      unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def
      apply auto
      subgoal for xs l aa b
        apply (drule spec[of _ nid])
        apply (drule spec[of _ xs])
        apply simp
        apply (drule bspec[of _ _ "(l, aa, b)"])
        subgoal
          unfolding extract_progress_def obtain_progress_def
          by auto
        subgoal
          apply simp
          apply (subgoal_tac "ifrontier (summ sg) (-+-) (change_multiplicities (summ sg) (extract_prog xs (subgraph.nxt sg) os) (pt_tr sg)) l = ifrontier (summ sg) (-+-) (change_multiplicities (summ sg) (extract_prog xs (subgraph.nxt sg) os) c) l")
          subgoal
            by auto
          subgoal
            apply (rule sym)
            apply (subst (1 2) Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
            apply (metis (no_types, opaque_lifting) c_pts_change_multiplicities_cong prems(1) propagate_all_preserves_c_pts)
            done
          done
        done
      subgoal for nid' xs l b d
        apply (drule spec[of _ nid'])
        apply (drule spec[of _ xs])
        apply simp
        apply (drule bspec[of _ _ "(l, b, d)"])
        subgoal
          unfolding extract_progress_def obtain_progress_def
          by auto
        subgoal
          apply simp
          apply (subgoal_tac "(ifrontier (summ sg) (-+-) (change_multiplicities (summ sg) (extract_prog xs (subgraph.nxt sg) (map_entry nid (front_update (\<lambda>_. frontier \<circ> (\<lambda>p. c_imp c (Loc nid (Trg p))))) os)) c) l) = ifrontier (summ sg) (-+-) (change_multiplicities (summ sg) (extract_prog xs (subgraph.nxt sg) os) (pt_tr sg)) l")
          subgoal
            by auto
          subgoal premises temp
            apply simp
            apply (smt (verit, best) assms(1) c_pts_change_multiplicities_cong ifrontier_eq_all_le prems(1) propagate_all_preserves_c_pts)
            done
          done
        done
      done
    subgoal premises prems
      using prems(12) apply -
      unfolding produ_consu_inter_supported_def
      apply (auto del: disjCI)
      apply (metis (no_types, opaque_lifting) prems(1) propagate_all_preserves_c_pts)
      apply (metis (no_types, lifting) prems(1) propagate_all_preserves_c_pts)
      apply (metis (lifting) ext prems(1) propagate_all_preserves_c_pts)
      apply (metis (lifting) ext prems(1) propagate_all_preserves_c_pts)
      done
    done
  done


end