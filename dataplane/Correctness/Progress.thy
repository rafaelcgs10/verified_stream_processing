theory Progress

imports
  General
  Propagation_Properties
begin

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

section \<open>Invariant Preservation under Progress Extraction\<close>

text \<open>Extracting progress changes from an operator keeps the invariant.\<close>

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
              using conjunct1[OF prems(12)[unfolded produ_consu_inter_supported_def]] apply -
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
      unfolding produ_consu_inter_supported_def
      apply (clarsimp del: disjCI simp add: c_pts_change_multiplicities)
      apply (intro allI conjI impI)
      subgoal 
        apply (subst extract_progress_def)
        apply (simp add: filter_map comp_def split_beta )
        apply (subst filter_False)
        apply (auto simp add: Misc.set_map_filter split: option.splits)
        done
      subgoal for nid' p t
        apply (subst extract_progress_def)
        apply (clarsimp del: disjCI simp add: filter_map comp_def split_beta )
        apply (drule spec2, drule spec, drule mp, blast)
        unfolding obtain_progress_def
        apply (clarsimp simp add: monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat List.map_filter_def comp_def map_concat filter_map split_beta obtain_progress_def Misc.set_map_filter split: option.splits)
        apply (simp add: add.assoc)
        apply (rule lt_le_lt)
        apply assumption
        subgoal premises temp
          apply (clarsimp simp add: zcount_sum)
          apply (cases "\<exists> nid p'. subgraph.nxt sg (nid, p') = Some (nid', p)")
          subgoal
            apply clarsimp
            subgoal for nid'' p''
              apply (subst (1 2) comm_monoid_add_class.sum.subset_diff[of "{(nid'', p'')}"])
              apply auto
              subgoal 
                apply (subgoal_tac "zmset (map snd (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid, p''a) = Some (nid', p) \<and> p'' = p''a) (produ (os nid)))) =
  zmset
          (map (\<lambda>x. snd (the (case subgraph.nxt sg (nid, fst x) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), fst (snd x), snd (snd x)))))
            (filter (\<lambda>x. (\<exists>a b. subgraph.nxt sg (nid, fst x) = Some (a, b)) \<and> (\<forall>a b. subgraph.nxt sg (nid, fst x) = Some (a, b) \<longrightarrow> nid' = a \<and> p = b)) (produ (os nid))))")
                defer
                subgoal
                  apply (rule arg_cong[where f=zmset])
                  apply (rule map_cong)
                  apply (rule filter_cong)
                  apply auto
                  using prems(2)[unfolded graph_summar_nt_def]
                  apply (metis domI inj_on_eq_iff prod.inject)
                  done
                apply simp
                apply (rule ordered_comm_monoid_add_class.sum_mono)
                apply (auto simp add: linorder_class.not_le dest!: zcount_zmset_gt_0_set_Ex)
                using prems(2)[unfolded graph_summar_nt_def]
                apply (metis (mono_tags, lifting) domI inj_onD snd_conv)
                done
              subgoal
                apply (subst comm_monoid_add_class.sum.neutral)
                subgoal
                  apply clarsimp
                  subgoal
                    apply (drule zmset_elem_nonneg)
                    apply (auto intro!: zcount_zmset_ge_0I dest!: zcount_zmset_gt_0_set_Ex)
                    using prems(9)[unfolded change_deltas_inv_def] apply force
                    using prems(2)[unfolded graph_summar_nt_def]
                    apply (metis domI inj_on_eq_iff prod.inject)+
                    done
                  done
                subgoal
                  apply (auto simp add: zcount_sum intro!: ordered_comm_monoid_add_class.sum_nonneg ordered_comm_monoid_add_class.add_nonneg_nonneg zcount_zmset_ge_0I dest!: zcount_zmset_gt_0_set_Ex)
                  using prems(9)[unfolded change_deltas_inv_def] apply force
                  using prems(2)[unfolded graph_summar_nt_def]
                  apply (metis domI inj_on_eq_iff prod.inject)+
                  done
                done
              done
            done
          subgoal
            apply (subst filter_False)
            subgoal
              by clarsimp
            subgoal
              apply simp
              apply (auto simp add: zcount_sum intro!: ordered_comm_monoid_add_class.sum_nonneg ordered_comm_monoid_add_class.add_nonneg_nonneg zcount_zmset_ge_0I dest!: zcount_zmset_gt_0_set_Ex)
              done
            done
          done
        done
      subgoal for nid' p t
        apply (drule spec2, drule spec, drule mp, blast)
        apply (elim exE bexE conjE disjE)
        subgoal for t''
          by (metis (mono_tags, lifting) group_cancel.rule0 zcount_union zmset_filter_extract_progress_Src_consumes_diff)
        subgoal for t''
          by auto
        done
      done
    done
  done

end