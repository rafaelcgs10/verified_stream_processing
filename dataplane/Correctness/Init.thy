theory Init

imports
  General
  Dataplane.Timely_Stream
  Dataplane.MyProduct_Instances
  Dataplane.AntichainOrder
  Dataplane.Propagation_Properties
  Propagates
begin


(*FIXME: move me*)
lemma init_config_empty_conf:
  assumes D: "dataflow_topology su (-+-)"
  shows "dataflow_topology_from_tree.init_config initial_conf"
  apply (subst dataflow_topology.init_config_def[OF D])
  apply (auto simp add: frontier_singleton split: port.splits)
  done

lemma propagation_inv_initial_conf:
  fixes su :: "(_, _) location \<Rightarrow> (_, _) location \<Rightarrow> ('t :: {canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,order_ccompare,bots}) antichain"
  assumes D: "dataflow_topology su (-+-)"
  shows "propagation_inv su initial_conf"
  unfolding propagation_inv_def
  apply (intro conjI)
  subgoal
    by (auto simp add: Propagate.dataflow_topology.init_imp_inv_imps_work_sum[OF D, of initial_conf, OF init_config_empty_conf[OF D]])
  subgoal
    using Propagate.dataflow_topology.init_imp_inv_implications_nonneg[OF D, of initial_conf, OF init_config_empty_conf[OF D]] by auto
  subgoal
  apply (subst Propagate.dataflow_topology.inv_imp_plus_work_nonneg_def[OF D])
    apply simp
    done
  done

lemma dataplane_tracker_inv_init_op_state:
  fixes su :: "('nid :: {enum,linorder, one,zero}, _) location \<Rightarrow> (_, _) location \<Rightarrow> ('t :: {canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,order_ccompare,bots}) antichain"
  assumes D: "dataflow_topology su (-+-)"
    and SU: "\<forall> loc. su loc loc = {}\<^sub>A"
    and R: "reachable_locations su = UNIV"
  shows  "dataplane_tracker_inv (\<lambda> x. init_op_state isu (i x)) (\<lambda>_. []) \<lparr>pt_tr =the (propagate_all su initial_conf), nxt = graph_to_nxt su, summ = su, upfro = upf\<rparr>"
  unfolding dataplane_tracker_inv_def
  apply clarsimp
  apply (rule exI[of _ "\<lambda> l. case l of Loc nid (Trg p) \<Rightarrow> {#}\<^sub>z | Loc nid (Src p) \<Rightarrow> to_zmset bots"])
  apply (cases "propagate_all su initial_conf")
  subgoal
    apply (rule FalseE)
    using propagate_all_terminates propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] assms(1,2,3) by fastforce
  subgoal for c
    apply (intro conjI)
    subgoal
      unfolding Src_caps_inv_def by auto
    subgoal
      unfolding Trg_caps_inv_def outputs_at_target_def by auto
    subgoal
      apply simp
      unfolding c_pts_inv_def
      apply (auto simp add: extract_prog_def obtain_progress_def c_pts_change_multiplicities comp_def split: location.splits port.splits)
      subgoal
        apply (subst filter_False)
        subgoal
          unfolding extract_progress_def
          apply auto
          done
        subgoal
          apply simp
          apply (drule propagate_all_preserves_c_pts)
          apply (auto simp add: extract_prog_def obtain_progress_def c_pts_change_multiplicities comp_def split: location.splits port.splits)
          done
        done
      subgoal for nid p
        apply (subst filter_False)
        subgoal
          unfolding extract_progress_def
          apply auto
          done
        subgoal
          apply simp
          apply (drule propagate_all_preserves_c_pts)
          apply (auto simp add: extract_prog_def obtain_progress_def c_pts_change_multiplicities comp_def split: location.splits port.splits)
          done
        done
      done
    subgoal
      unfolding front_inv_def
      apply safe
      subgoal for nid p
      apply (drule propagate_all_frontier_c_imp_correctness[OF _ D R, where loc="Loc nid (Trg p)"])
      using propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] apply simp
      using propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] apply simp
      using propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] apply simp
      apply simp
      done
    done
  subgoal
    unfolding imp_front_inv_def
    apply safe
    subgoal for l
      apply (subgoal_tac \<open>dataflow_topology.inv_imps_work_sum su (-+-) (initial_conf :: (('nid, 'd) location, 't) configuration) \<and> dataflow_topology_from_tree.inv_implications_nonneg (initial_conf :: (('nid, 'd) location, 't) configuration) \<and> dataflow_topology_from_tree.inv_imp_plus_work_nonneg (initial_conf :: (('nid, 'd) location, 't) configuration)\<close>)
      subgoal
        apply clarsimp
        apply (frule propagate_all_frontier_c_imp_correctness[OF _ D R, where loc=l])
           apply (simp_all add: assms(1) propagate_all_preserves_ifrontier)
        done
      subgoal
      using propagation_inv_initial_conf[OF D, unfolded propagation_inv_def] by simp
    done
  done
  subgoal
    unfolding chnls_imp_front_inv_def outputs_at_target_def
    by clarsimp
  subgoal
    unfolding change_deltas_inv_def
    by clarsimp
  subgoal
    using propagation_inv_initial_conf[OF D]
    by (simp add: D propagate_all_preserves_inv propagation_inv_def)
  subgoal
    unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def obtain_progress_def extract_prog_def extract_progress_def
    by auto
  subgoal
    unfolding produ_consu_inter_supported_def
    by auto
  done
  done

end