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

lemma take_step_enum_dataflow_topology_take_step:
  "enum_dataflow_topology su dataflow_topology_from_tree.followed_by \<Longrightarrow>
   take_step su = enum_dataflow_topology.take_step su dataflow_topology_from_tree.followed_by cless"
  apply (rule ext)+
  subgoal for S c
    apply (cases S; hypsubst_thin)
     apply (simp add: Executable.enum_dataflow_topology.take_step.simps)
    apply (subst Executable.enum_dataflow_topology.take_step.simps(2))
     apply assumption
    apply (simp add: after_summary_def mymin_code_def)
    done
  done

lemma take_step_CM_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   d \<noteq> 0 \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary (CM loc t d)) c)"
  apply (frule Executable.enum_dataflow_topology.CM_next[where delta=d, simplified, unfolded enum_dataflow_topology_def])
    apply assumption+
  apply (elim exE)
  apply (subst take_step_enum_dataflow_topology_take_step)
   apply (simp add: enum_dataflow_topology_def)
  apply (rule Propagate.dataflow_topology.cm_preserves_inv_imps_work_sum)
    apply assumption+
  done

lemma take_step_CM_p_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   d \<noteq> 0 \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary (CM loc t d)) c) \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg ((take_step summary (CM loc t d)) c) \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary (CM loc t d)) c)"
  apply (frule Executable.enum_dataflow_topology.CM_next[where delta=d, simplified, unfolded enum_dataflow_topology_def])
    apply assumption+
  apply (elim exE)
  apply (subst (1 2) take_step_enum_dataflow_topology_take_step)
   apply (simp add: enum_dataflow_topology_def)
  apply (intro conjI)
    apply (rule Propagate.dataflow_topology.cm_preserves_inv_implications_nonneg)
      apply assumption+
   apply (rule Propagate.dataflow_topology.iiws_imp_iipwn)
    apply assumption+
   apply (subst take_step_enum_dataflow_topology_take_step[symmetric])
    apply (simp add: enum_dataflow_topology_def)
   apply (rule take_step_CM_p_preserves_inv_imps_work_sum)
      apply assumption+
   apply auto[1]
  apply (rule take_step_CM_p_preserves_inv_imps_work_sum)
     apply assumption+
  apply auto
  done

lemma change_multiplicities_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   (\<forall> d \<in> snd ` snd ` set xs. d \<noteq> 0) \<Longrightarrow>
   (\<forall> (l, t, d) \<in> set xs. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c l) \<and> t' \<le> t) \<Longrightarrow>
   change_multiplicities summary xs c = c' \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c'"
  apply (induct xs arbitrary: c c')
   apply simp
  subgoal premises prems for a xs c c'
    using prems(2-) apply -
    apply (simp split: prod.splits)
    subgoal for l b t' d t
      apply (subst (asm) change_multiplicities_simps(2)[where summary=summary])
      apply (frule take_step_CM_p_preserves_inv[where loc=l and t=t'])
           apply assumption+
       apply force
      apply (elim conjE)
      using prems(1) apply -
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      back
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply fastforce
      apply (drule meta_mp)
       apply auto
      done
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
        unfolding extract_prog_changes_above_impl_inv_def
        apply (drule spec[of _ nid])
        apply (drule spec[of _ "[]"])
        unfolding changes_above_impl_inv_def extract_prog_def
        apply auto
        done
      done
    subgoal premises prems
      using prems(8) apply -  
      unfolding chnls_imp_front_inv_def
      apply clarsimp
      apply (drule spec)+
      apply (drule bspec)
       apply assumption
      apply simp
      subgoal for nid' p' a t
        using prems(4,5) apply -
        unfolding Trg_caps_inv_def
        apply (drule spec[of _ nid'])
        apply (drule spec[of _ p'])
        unfolding c_pts_inv_def
        apply (drule spec[of _ "Loc nid' (Trg p')"])
        apply simp
        apply (subst (asm) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
          apply simp_all
        apply (cases "\<exists> p. nxt sg (nid, p) = Some (nid', p')")
        subgoal
          apply (rule frontier_less_equal_ifrontierI[OF prems(1), of 0 "Loc nid' (Trg p')", simplified])
          subgoal 
            apply (rule Graph.graph.path_weight_refl)
            apply (rule dataflow_topology.axioms(1)[OF prems(1)])
            done
          subgoal
            apply (cases "nid' = nid")
            subgoal
              apply clarsimp
              subgoal for p
                apply hypsubst_thin
                apply (simp add: c_pts_change_multiplicities)
                apply (subst (asm) (2) filter_False)
                subgoal
                  unfolding extract_prog_def extract_progress_def obtain_progress_def
                  apply (clarsimp del: disjCI simp add: Misc.set_map_filter split_beta image_iff split: option.splits)
                  using prems(2)[unfolded graph_summar_nt_def] apply (metis Pair_inject domI inv_on_f_f)
                  done
                subgoal
                  apply simp
                  apply (metis (no_types, opaque_lifting) frontier_less_equal_zcount_pos image_set img_snd zcount_to_zmset_gt_0)
                  done
                done
              done
            subgoal
              apply clarsimp
              subgoal for p
                apply (simp add: change_multiplicities_append_comp)
                apply (subst (asm) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid'])
                  apply simp_all
                apply (simp add: c_pts_change_multiplicities)
                apply (subst (asm) (3) filter_False)
                subgoal
                  unfolding extract_prog_def extract_progress_def obtain_progress_def
                  apply (clarsimp del: disjCI simp add: Misc.set_map_filter split_beta image_iff split: option.splits)
                  using prems(2)[unfolded graph_summar_nt_def] apply (metis Pair_inject domI inv_on_f_f)
                  done
                subgoal
                  apply simp
                  apply (subst (asm) (2) extract_progress_def)
                  apply (simp add: filter_map comp_def split_beta List.map_filter_def split: option.splits)
                  apply (subst (asm) (2) filter_False)
                  subgoal
                    unfolding extract_prog_def extract_progress_def obtain_progress_def
                    apply (clarsimp del: disjCI simp add: Misc.set_map_filter split_beta image_iff split: option.splits)
                    using prems(2)[unfolded graph_summar_nt_def] apply (metis domIff inj_on_contraD not_Some_eq2 prod.inject)
                    done
                  subgoal
                    apply simp
                    apply (subst (asm) (2) obtain_progress_def)
                    apply simp
                    apply (subgoal_tac "\<forall> t. zcount (zmset (map snd (filter (\<lambda>x. p' = fst x) (consu (os nid'))))) t \<ge> 0")
                    subgoal
                      by (metis (no_types, lifting) frontier_below_eq_frontier_minus frontier_less_equal_le_trans frontier_less_equal_zcount_pos img_snd list.set_map zcount_to_zmset_gt_0)
                    subgoal
                      using prems(9)[unfolded change_deltas_inv_def] apply -
                      apply (auto intro!: zcount_zmset_ge_0I)
                      apply (smt (verit, best))
                      done
                    done
                  done
                done
              done
            done
          done
        subgoal
          apply (cases "\<exists> nid'' p'' m. subgraph.nxt sg (nid'', p'') = Some (nid', p') \<and> (p'', t, m) \<in> set (produ (os nid''))")
          subgoal
            apply clarsimp
            subgoal for nid'' p'' m
              using prems(12)[unfolded produ_supported_def] apply -
              apply (drule spec[of _ nid''])
              apply (drule spec[of _ p''])
              back
              apply (drule spec[of _ t])
              apply (drule spec[of _ m])
              apply (drule mp)
               apply assumption
              apply (elim disjE)
              subgoal
                apply (rule frontier_less_equal_ifrontierI[OF prems(1), of 0 "Loc nid'' (Src p'')", simplified])
                subgoal 
                  using prems(2)[unfolded graph_summar_nt_def] 
                   path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF prems(1)]]
                  by simp
                subgoal
                  apply (simp add: c_pts_change_multiplicities)
                  apply (subst filter_False)
                  subgoal
                    apply (subst obtain_progress_def)
                    apply (subst extract_progress_def)
                    apply (auto del: disjCI simp add: Misc.set_map_filter split_beta image_iff split: option.splits)
                    done
                  subgoal
                    apply simp
                    apply (metis frontier_less_equal_zcount_pos)
                    done
                  done
                done
              subgoal
                apply clarsimp
                subgoal for m'
                  using prems(11)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format, of "[nid]" nid'' "(Loc nid'' (Src p''), t, m')", simplified] apply -
                  apply (drule meta_mp)
                  subgoal
                    by blast
                  apply (drule meta_mp)
                  subgoal
                    apply (subst obtain_progress_def)
                    apply (subst extract_progress_def)
                    apply (clarsimp del: disjCI simp add: Misc.set_map_filter split_beta image_iff split: option.splits)
                    apply force
                    done
                  subgoal
                    apply (subst (asm) (1) extract_prog_def)
                    apply (rule frontier_less_equal_ifrontier_trans_alt2[OF prems(1), of 0 "Loc nid'' (Src p'')"])
                    subgoal 
                      using prems(2)[unfolded graph_summar_nt_def] path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF prems(1)]] by simp
                     apply assumption
                    apply simp
                    done
                  done
                done
              done
            done
          subgoal
            apply (clarsimp simp add: zmultiset_eq_iff c_pts_change_multiplicities)
            apply (drule spec[of _ t])+
            apply (subgoal_tac "zcount (zmset (map snd (filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog (remove1 nid enum_class.enum) (subgraph.nxt sg) os)))) t \<le> 0")
            subgoal
              apply (rule frontier_less_equal_ifrontierI[OF prems(1), of 0 "Loc nid' (Trg p')", simplified])
              subgoal 
                apply (rule Graph.graph.path_weight_refl)
                apply (rule dataflow_topology.axioms(1)[OF prems(1)])
                done
              apply (clarsimp simp add: frontier_less_equal_zcount_pos img_snd zmultiset_eq_iff c_pts_change_multiplicities)
              apply (smt (verit, ccfv_SIG) frontier_less_equal_zcount_pos img_snd list.set_map zcount_to_zmset_gt_0 zcount_union)
              done
            subgoal
              apply (rule zcount_zmset_le_0I)
              apply (subst extract_prog_def)
              apply (subst obtain_progress_def)
              apply (subst extract_progress_def)
              apply (auto del: disjCI simp add: Misc.set_map_filter split: option.splits)
              subgoal
                using prems(9)[unfolded change_deltas_inv_def] 
                by (smt (verit, best) Un_iff)
              done
            done
          done
        done
      done
    subgoal premises prems
      using prems(9) apply -  
      unfolding change_deltas_inv_def obtain_progress_def
      apply auto
      done
    subgoal premises prems
      using prems(10) apply - 
      unfolding propagation_inv_def
      apply clarsimp
      apply (drule change_multiplicities_preserves_inv[OF prems(1), where xs="extract_progress nid (subgraph.nxt sg) (snd (obtain_progress (os nid)))"])
           apply assumption+
      subgoal
        using prems(9)[unfolded change_deltas_inv_def]
        apply (auto simp add: Misc.set_map_filter extract_progress_def obtain_progress_def split: option.splits)
         apply blast+
        done
      subgoal
        apply safe
        subgoal for l t m
          unfolding frontier_less_equal_iff2[symmetric]
          apply (rule frontier_less_equal_le_trans)
           apply (drule prems(11)[unfolded extract_prog_changes_above_impl_inv_def extract_prog_def changes_above_impl_inv_def, rule_format, of "[]" nid, simplified])
           apply simp
          using prems(7)[unfolded imp_front_inv_def]
          apply fast
          done
        done
       apply (rule refl)
      apply auto
      done
    subgoal premises prems
      unfolding extract_prog_changes_above_impl_inv_def
      apply clarsimp
      subgoal for nid2 xs
        using prems(11) apply -
        unfolding extract_prog_changes_above_impl_inv_def
        apply (drule spec[of _ nid2])
        apply (drule spec[of _ "nid # remove1 nid xs"])
        apply (simp add: extract_prog_obtain_progress_remove1)
        unfolding extract_prog_def
        apply (simp add: change_multiplicities_append_alt)
        done
      done
    subgoal premises prems
      using prems(12) apply -
      unfolding produ_supported_def
      apply (clarsimp del: disjCI simp add: c_pts_change_multiplicities)
      subgoal for nid' p' t m
        apply (subst extract_progress_def)
        apply (simp add: filter_map comp_def split_beta )
        apply (subst filter_False)
         apply (auto simp add: Misc.set_map_filter split: option.splits)
        done
      done
    done
  done

lemma dataplane_tracker_inv_upfro:
  "sg = sg'\<lparr> upfro := f \<rparr> \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os cbufs sg'"
  unfolding dataplane_tracker_inv_def
  apply auto
  done


end