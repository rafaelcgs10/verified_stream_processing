theory OCapsReorder

imports
  General
begin


declare cin.rep_eq[simp del]
declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

lemma dataplane_tracker_inv_replace_ocaps:
  "dataplane_tracker_inv os' cbufs sg \<Longrightarrow>
   mset (ocaps (os nid) p) = mset C \<Longrightarrow>
   os' = os(nid := (os nid)\<lparr> ocaps := (ocaps (os nid))(p := C) \<rparr>) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg"
  apply hypsubst_thin
  unfolding dataplane_tracker_inv_def
  apply clarsimp
  subgoal premises prems for caps
    apply (rule exI[of _ caps])
    apply (intro conjI)
    subgoal
      using prems(1,2) apply -
      unfolding Src_caps_inv_def
      apply clarsimp
      apply (metis Diff_eq_empty_iff_mset diff_left_imp_eq mset_list_diff mset_zero_iff_right subset_mset.dual_order.order_iff_strict to_zmset_list_diff)
      done
    subgoal
      using prems(1,3) apply -
      unfolding Trg_caps_inv_def 
      apply safe
      subgoal for nid p
        apply (drule spec2[of _ nid p])
        apply simp
        subgoal premises aux
          apply (rule arg_cong[where f=to_zmset])
          apply (rule map_cong)
          unfolding outputs_at_target_def BULK_BENQ_def
          by (auto simp: if_splits prod.splits cong: if_cong)
        done
      done
    subgoal
      using prems(1,4) apply -
      unfolding c_pts_inv_def  extract_prog_def extract_progress_def obtain_progress_def
      apply (auto simp:if_distrib[of produ]  if_distrib[of inter] if_distrib[of consu] split: if_splits prod.splits cong: map_eq_conv)
      subgoal for l
        apply (drule spec[of _ l])
        apply (drule sym[of _ "caps l"])
        apply simp
        subgoal premises aux
          apply (auto simp add: c_pts_change_multiplicities if_distrib[of produ]  if_distrib[of inter] if_distrib[of consu] split: if_splits prod.splits cong: map_eq_conv)
          apply (rule arg_cong[where f=zmset])
          apply (rule map_cong)
           apply (rule filter_cong)
            apply (rule arg_cong[where f=concat])
            apply (rule map_cong)
             apply simp_all
          done
        done
      done
    subgoal
      using prems(1,5) apply -
      unfolding front_inv_def 
      apply (auto simp:if_distrib[of produ]  if_distrib[of inter] if_distrib[of consu] split: if_splits prod.splits)
      done
    subgoal
      using prems(1,7) apply -
      apply (subgoal_tac "outputs_at_target (summ sg) (map_entry nid (ocaps_update (\<lambda>_. (ocaps (os nid))(p := C))) os) = outputs_at_target (summ sg) os")
       apply simp
      subgoal premises
        unfolding outputs_at_target_def BULK_BENQ_def
        apply (auto del: disjCI simp add:split_beta if_distrib[of produ] if_distrib[of outpu]   if_distrib[of inter] if_distrib[of consu] split: if_splits prod.splits)
        done
      done
    subgoal
      using prems(1,8)
      unfolding change_deltas_inv_def
      by fastforce
    subgoal
      using prems(1,10) apply -
      unfolding extract_prog_changes_above_impl_inv_def
      apply safe
      subgoal for nid' xs
        apply (drule spec)+
        apply (drule mp)
         apply assumption
        apply (drule mp)
         apply assumption
        apply (subgoal_tac "extract_prog xs (subgraph.nxt sg) (map_entry nid (ocaps_update (\<lambda>_. (ocaps (os nid))(p := C))) os) = extract_prog xs (subgraph.nxt sg) os")
        subgoal
          apply simp
          apply (subgoal_tac "extract_progress nid' (subgraph.nxt sg) (snd (obtain_progress (if nid' = nid then os nid\<lparr>ocaps := (ocaps (os nid))(p := C)\<rparr> else os nid'))) = extract_progress nid' (subgraph.nxt sg) (snd (obtain_progress (os nid')))")
          subgoal
            by simp
          subgoal premises aux
            unfolding obtain_progress_def
            by auto
          done
        subgoal premises aux
          unfolding obtain_progress_def extract_prog_def extract_progress_def
          apply (auto del: disjCI simp add:split_beta if_distrib[of produ] if_distrib[of outpu]   if_distrib[of inter] if_distrib[of consu] split: if_splits prod.splits)
          apply (rule arg_cong[where f=concat])
          apply (rule map_cong)
           apply auto
          done
        done
      done
    subgoal
      supply  if_cong[cong]
      unfolding produ_consu_inter_supported_def
      apply (intro allI impI conjI)
      subgoal
        using conjunct1[OF prems(11)[unfolded produ_consu_inter_supported_def]] apply -
        apply (auto del: disjCI simp add:split_beta if_distrib[of produ] if_distrib[of outpu]   if_distrib[of inter] if_distrib[of consu] split: if_splits prod.splits)
        done
      subgoal for nid' p t m
        apply (cases "nid' = nid")
        subgoal
          apply hypsubst_thin
          using conjunct1[OF conjunct2[OF prems(11)[unfolded produ_consu_inter_supported_def]], simplified, unfolded if_distrib[of produ] if_distrib[of outpu]   if_distrib[of inter] if_distrib[of consu], simplified, rule_format, where nid=nid and p=p and t=t, simplified] apply -
          apply (drule meta_mp)
           apply blast
          apply simp
          by (smt (verit, best) map_eq_conv split_cong)
        subgoal
          subgoal
            using conjunct1[OF conjunct2[OF prems(11)[unfolded produ_consu_inter_supported_def]], simplified, unfolded if_distrib[of produ] if_distrib[of outpu]   if_distrib[of inter] if_distrib[of consu], simplified, rule_format, where nid=nid' and p=p and t=t, simplified] apply -
            apply (drule meta_mp)
             apply simp
             apply blast
            apply simp
            apply (smt (verit, best) map_eq_conv split_cong)
            done
          done
        done
      subgoal for nid' p t m
        using conjunct2[OF conjunct2[OF prems(11)[unfolded produ_consu_inter_supported_def]], simplified, unfolded if_distrib[of produ] if_distrib[of outpu]   if_distrib[of inter] if_distrib[of consu], simplified, rule_format, where nid=nid' and p=p and t=t, simplified] apply -
        apply (drule meta_mp)
         apply simp
         apply blast
        apply (auto del: disjCI simp add:split_beta if_distrib[of produ] if_distrib[of outpu]   if_distrib[of inter] if_distrib[of consu] split: if_splits prod.splits)
        done
      done
    done
  done


end