theory Mints

imports
  General
begin

section \<open>Invariant Preservation under Mint\<close>

text \<open>The dataplane tracker invariant survives minting a capability.\<close>

lemma dataplane_tracker_inv_mints:
  assumes D: "dataflow_topology (summ sg) (-+-)"
  shows
    "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   m > 0 \<Longrightarrow>
   (\<exists> t' \<in>  set (ocaps (os nid) p). t' \<le> t) \<Longrightarrow>
   dataplane_tracker_inv (os(nid := os nid\<lparr>ocaps := (ocaps (os nid))(p := ocaps (os nid) p @ replicate m t) , inter := operator_state.inter (os nid) @ [(p, t, m)]\<rparr>)) cbufs sg"
  unfolding dataplane_tracker_inv_def
  apply (elim conjE exE)
  apply simp
  apply hypsubst_thin
  subgoal for c c' cgs chns caps
    apply (rule exI[of _ 
          "(\<lambda> l. case l of 
        Loc nid' (Src p') \<Rightarrow> if nid' = nid \<and> p' = p then update_zmultiset (caps l) t m else caps l 
     | Loc nid' (Trg p') \<Rightarrow> caps l)"])
    apply (intro conjI)
    subgoal premises prems
      using prems(4) apply -
      unfolding Src_caps_inv_def to_zmset_correct
      apply auto
      done
    subgoal premises prems
      using prems(5) apply -
      unfolding Trg_caps_inv_def outputs_at_target_def
      apply (auto simp add: map_tl BHD_def BTL_def BULK_BENQ_def split: prod.splits)
      done
    subgoal premises prems
      using prems(6) apply -
      unfolding c_pts_inv_def
      apply safe
      subgoal for l
        apply (drule spec[of _ l])
        apply (drule sym)
        apply (auto simp add:  extract_prog_def extract_progress_def obtain_progress_def map_tl BHD_def BTL_def BULK_BENQ_def split: prod.splits location.splits port.splits; hypsubst_thin?)
        subgoal for nid' p'
          by (auto simp add: monoid_add_class.sum_list_distinct_conv_sum_set c_pts_change_multiplicities map_concat filter_concat comp_def split_beta zmset_concat intro: dataflow_topology_from_tree.all_eq_sum_eq)
        subgoal  premises temp
          apply (auto simp add: if_distrib[of inter] if_distrib[of produ] monoid_add_class.sum_list_distinct_conv_sum_set c_pts_change_multiplicities map_concat filter_concat comp_def split_beta zmset_concat intro!: dataflow_topology_from_tree.all_eq_sum_eq)
          apply (subst (1 2) comm_monoid_add_class.sum.subset_diff[where B="{nid}"])
          apply simp_all
          done
        subgoal
          by (auto simp add: monoid_add_class.sum_list_distinct_conv_sum_set c_pts_change_multiplicities map_concat filter_concat comp_def split_beta zmset_concat intro: dataflow_topology_from_tree.all_eq_sum_eq)
        subgoal 
          using prems(2) apply -
          apply (auto simp add:  if_distrib[of inter] if_distrib[of produ] monoid_add_class.sum_list_distinct_conv_sum_set c_pts_change_multiplicities map_concat filter_concat comp_def split_beta zmset_concat intro!: dataflow_topology_from_tree.all_eq_sum_eq)
          done
        done
      done
    subgoal premises prems
      using prems(7)
      unfolding front_inv_def
      by auto
    subgoal premises prems
      using prems(9) apply -
      unfolding chnls_imp_front_inv_def
      apply auto
      subgoal for nid' p' nid'' p''
        apply (drule spec2[of _ nid' p'])
        apply (drule bspec[of _ _ "(nid'', p'')"])
        subgoal
          unfolding outputs_at_target_def BULK_BENQ_def
          apply (auto split: if_splits prod.splits)
          done
        subgoal
          by auto
        done
      done
    subgoal premises prems
      using prems(2,10) 
      unfolding change_deltas_inv_def
      by auto
    subgoal premises prems
      using prems(2,3,12) apply -
      unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def
      apply auto
      subgoal for t'' xs l' t' m'
        subgoal
          apply (cases "(l', t', m') \<in> set (extract_progress nid (subgraph.nxt sg) (snd (obtain_progress (os nid))))")
          subgoal
            apply (drule spec[of _ nid])
            apply (drule spec[of _ xs])
            apply simp
            apply (drule bspec[of _ _ "(l', t', m')"])
            apply simp_all
            done
          subgoal
            unfolding extract_progress_def obtain_progress_def
            apply (clarsimp del: disjCI simp add: Misc.set_map_filter image_iff split: option.splits prod.splits)
            subgoal
              apply (subgoal_tac "zcount (zmset (map snd (filter ((=) p \<circ> fst) (operator_state.inter (os nid))))) t'' > 0 \<or> zcount (c_pts (pt_tr sg) (Loc nid (Src p))) t'' > 0")
              defer
              subgoal
                using prems(4)[unfolded Src_caps_inv_def, rule_format, of nid p]
                  prems(6)[unfolded c_pts_inv_def, rule_format, of "Loc nid (Src p)"] apply -
                apply (simp add: c_pts_change_multiplicities)
                apply (metis (no_types, opaque_lifting) gt_0_plusD zcount_to_zmset_gt_0 zcount_union)
                done
              subgoal
                apply (elim disjE)
                subgoal
                  apply hypsubst_thin
                  apply (drule spec[of _ nid])
                  apply (drule spec[of _ xs])
                  apply simp
                  apply (drule zcount_zmset_gt_0_set_Ex)
                  apply clarsimp
                  subgoal for m''
                    apply (drule bspec[of _ _ "(Loc nid (Src p), t'', m'')"])
                    subgoal
                      by (force del: disjCI simp add: image_iff split: prod.splits)
                    subgoal
                      apply simp
                      apply (meson frontier_less_equal_trans)
                      done
                    done
                  done
                subgoal
                  apply (rule frontier_less_equal_trans[rotated])
                  apply assumption
                  apply (rule frontier_less_equal_ifrontierI [OF D, of  0 "Loc nid (Src p)", simplified])
                  subgoal
                    apply (rule graph.path_weight_refl)
                    apply (rule dataflow_topology.axioms(1)[OF D])
                    done
                  subgoal
                    apply (clarsimp simp add: monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat map_concat filter_concat split_beta comp_def obtain_progress_def extract_progress_def extract_prog_def c_pts_change_multiplicities)
                    apply (subst comm_monoid_add_class.sum.distrib)
                    apply (subst comm_monoid_add_class.sum.neutral)
                    subgoal premises temp
                      using temp(5,6) apply -
                      apply clarsimp
                      apply (subst filter_False)
                      apply auto
                      done
                    subgoal
                      apply simp
                      apply (subgoal_tac "\<forall> t. zcount (\<Sum>x\<in>set xs.
           zmset
            (map snd
              (filter (\<lambda>(l', t, d). Loc nid (Src p) = l')
                (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (x, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os x)))))) t \<ge> 0")
                      subgoal
                        by (meson frontier_below_eq_frontier_plus_pos frontier_less_equal_le_trans frontier_less_equal_zcount_pos)
                      subgoal premises temp
                        using temp(5,6) apply -
                        apply (clarsimp simp add: zcount_sum intro!: ordered_comm_monoid_add_class.sum_nonneg)
                        apply (subst filter_False)
                        apply (auto simp add: Misc.set_map_filter split: option.splits)
                        done
                      done
                    done
                  done
                done
              done
            subgoal for p'' nid' p'
              apply (drule spec[of _ nid])
              apply (drule spec[of _ xs])
              apply simp
              apply (drule bspec[of _ _ "(Loc nid (Src p''), t', _)"])
              apply fast
              apply simp
              apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc nid (Src p'')", simplified, OF D])
              apply simp_all
              subgoal
                using prems(1)[unfolded graph_summar_nt_def]
                by auto
              done
            done
          done
        done
      subgoal for t' nid' xs l t'' m'
        apply (drule spec[of _ nid'])
        apply (drule spec[of _ xs])
        apply simp
        apply (cases "nid \<in> set xs")
        subgoal
          apply (drule bspec[of _ _ "(l, t'', m')"])
          apply simp_all
          apply (drule frontier_less_equal_ifrontierE[OF _ D])
          apply clarsimp
          subgoal for l' s t'''
            apply (cases "l' = Loc nid (Src p)")
            subgoal
              apply (rule frontier_less_equal_ifrontierI[OF D])
              apply assumption
              apply (clarsimp simp add: if_distrib[of inter]  monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat map_concat filter_concat split_beta comp_def obtain_progress_def extract_progress_def extract_prog_def c_pts_change_multiplicities)
              apply (subst (1) comm_monoid_add_class.sum.subset_diff[where B="{nid}"])
              apply simp_all
              apply (subst (asm) (1) comm_monoid_add_class.sum.subset_diff[where B="{nid}"])
              apply simp_all
              apply (rule frontier_less_equal_le_trans)
              apply assumption
              subgoal premises temp
                apply (subgoal_tac "c_pts (pt_tr sg) (Loc nid (Src p)) +
      ((\<Sum>x\<in>set xs - {nid}.
          zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p) = l') (map (\<lambda>(p, y). (Loc x (Src p), y)) (operator_state.inter (os x))))) +
          zmset
           (map snd
             (filter (\<lambda>(l', t, d). Loc nid (Src p) = l')
               (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (x, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os x)))))) +
       (zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p) = l') (map (\<lambda>(p, y). (Loc nid (Src p), y)) (operator_state.inter (os nid))))) + to_zmset (replicate m t) +
        zmset
         (map snd
           (filter (\<lambda>(l', t, d). Loc nid (Src p) = l')
             (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os nid))))))) =
     (c_pts (pt_tr sg) (Loc nid (Src p)) +
      ((\<Sum>x\<in>set xs - {nid}.
          zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p) = l') (map (\<lambda>(p, y). (Loc x (Src p), y)) (operator_state.inter (os x))))) +
          zmset
           (map snd
             (filter (\<lambda>(l', t, d). Loc nid (Src p) = l')
               (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (x, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os x)))))) +
       (zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p) = l') (map (\<lambda>(p, y). (Loc nid (Src p), y)) (operator_state.inter (os nid))))) +
        zmset
         (map snd
           (filter (\<lambda>(l', t, d). Loc nid (Src p) = l')
             (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os nid))))))) + to_zmset (replicate m t))")
                subgoal premises temp2
                  apply (subst temp2(1))
                  apply (rule frontier_below_eq_frontier_plus_pos)
                  using  to_zmset_nenneg 
                  apply fast
                  done
                subgoal
                  by simp
                done
              done
            subgoal
              apply (rule frontier_less_equal_ifrontierI[OF D])
              apply assumption
              apply (clarsimp simp add: if_distrib[of inter]  monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat map_concat filter_concat split_beta comp_def obtain_progress_def extract_progress_def extract_prog_def c_pts_change_multiplicities)
              apply (subst (1) comm_monoid_add_class.sum.subset_diff[where B="{nid}"])
              apply simp_all
              apply (subst (asm) (1) comm_monoid_add_class.sum.subset_diff[where B="{nid}"])
              apply simp_all
              done
            done
          done
        subgoal
          apply (drule bspec)
          apply simp_all
          apply clarsimp
          done
        done
      done
    subgoal premises prems
      using prems(13) apply -
      unfolding produ_consu_inter_supported_def
      apply (auto del: disjCI simp add: if_distrib[of inter] if_distrib[of produ]  monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat map_concat filter_concat split_beta comp_def)
      subgoal
        by fast
      subgoal for p' t' m'
        apply (drule spec2, drule spec, drule mp, blast)
        subgoal premises temp
          using temp(4) apply -
          apply (subgoal_tac "(\<Sum>x\<in>UNIV.
            zmset
             (map snd
               (filter (\<lambda>(p'', ab). subgraph.nxt sg (fst x, p'') = Some (nid, p') \<and> snd x = p'')
                 (if fst x = nid then produ (os nid\<lparr>ocaps := (ocaps (os nid))(p := ocaps (os nid) p @ replicate m t), inter := operator_state.inter (os nid) @ [(p, t, int m)]\<rparr>) else produ (os (fst x)))))) = (\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(p'', ab). subgraph.nxt sg (fst x, p'') = Some (nid, p') \<and> snd x = p'') (produ (os (fst x))))))")
          subgoal
            by simp
          subgoal
            by (auto intro!: dataflow_topology_from_tree.all_eq_sum_eq)
          done
        done
      subgoal for nid' p' t' m'
        apply (drule spec2, drule spec, drule mp, blast)
        apply (subgoal_tac " (\<Sum>x\<in>UNIV.
            zmset
             (map snd
               (filter (\<lambda>(p'', ab). subgraph.nxt sg (fst x, p'') = Some (nid', p') \<and> snd x = p'')
                 (if fst x = nid then produ (os nid\<lparr>ocaps := (ocaps (os nid))(p := ocaps (os nid) p @ replicate m t), inter := operator_state.inter (os nid) @ [(p, t, int m)]\<rparr>) else produ (os (fst x)))))) = (\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(p'', ab). subgraph.nxt sg (fst x, p'') = Some (nid', p') \<and> snd x = p'') (produ (os (fst x))))))")
        subgoal
          by auto
        subgoal
          by (auto intro!: dataflow_topology_from_tree.all_eq_sum_eq)
        done
      subgoal
        using prems(3) apply -
        apply (auto del: disjCI simp add: remove1_append)
        subgoal for t''
          apply (subgoal_tac "zcount (zmset (map snd (filter ((=) p \<circ> fst) (operator_state.inter (os nid))))) t'' > 0 \<or> zcount (c_pts (pt_tr sg) (Loc nid (Src p))) t'' > 0")
          defer
          subgoal
            using prems(4)[unfolded Src_caps_inv_def, rule_format, of nid p]
              prems(6)[unfolded c_pts_inv_def, rule_format, of "Loc nid (Src p)"] apply -
            apply (simp add: c_pts_change_multiplicities)
            apply (metis (no_types, opaque_lifting) gt_0_plusD zcount_to_zmset_gt_0 zcount_union)
            done
          subgoal premises temp2
            using temp2(5-) apply -
            apply (elim disjE)
            subgoal
              apply (drule gt_0_zcount_msetD)
              using temp2(3)[rule_format, of p t'' nid] apply -
              apply (drule meta_mp)
              apply blast
              apply fastforce
              done
            subgoal
              by auto
            done
          done
        done
      subgoal for p' t' m'
        apply fast
        done
      done
    done
  done

section \<open>Minting Many and Adding Capabilities\<close>

text \<open>Iterated mints and directly added capabilities preserve the
  invariant.\<close>

lemma dataplane_tracker_inv_mints_many:
  assumes D: "dataflow_topology (summ sg) (-+-)"
  shows
    "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   (\<forall> t\<in>set xs. \<exists> t' \<in>  set (ocaps (os nid) p). t' \<le> t) \<Longrightarrow>
   dataplane_tracker_inv (os(nid := os nid\<lparr>ocaps := (ocaps (os nid))(p := ocaps (os nid) p @ xs) , inter := operator_state.inter (os nid) @ map (\<lambda> t. (p, t, 1)) xs\<rparr>)) cbufs sg"
  apply (induct xs arbitrary: os rule: rev_induct)
  subgoal
    by simp
  subgoal premises prems for t xs os
    using prems(2-) apply -
    apply simp
    apply (rule dataplane_tracker_inv_mints[where m=1 and nid=nid and p=p and t=t and os="os(nid := (os nid)\<lparr> ocaps := (ocaps (os nid))( p := ocaps (os nid) p @ xs), inter := inter (os nid) @ map (\<lambda>t. (p, t, 1)) xs \<rparr>)", simplified])
    using D apply assumption
    using prems(1) apply blast
     apply (auto simp add: graph_summar_nt_def)
    done
  done

lemma dataplane_tracker_inv_mints_many_list:
  assumes D: "dataflow_topology (summ sg) (-+-)"
  shows
    "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
     graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
     distinct ps \<Longrightarrow>
     (\<forall> p \<in> set ps. \<forall> t \<in> set (xs p). \<exists> t' \<in> set (ocaps (os nid) p). t' \<le> t) \<Longrightarrow>
     dataplane_tracker_inv
       (os(nid := os nid\<lparr>
          ocaps := (\<lambda>p. ocaps (os nid) p @ (if p \<in> set ps then xs p else [])),
          inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (xs p)) ps)\<rparr>))
       cbufs sg"
proof (induct ps arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  let ?os1 = "os(nid := os nid\<lparr>
    ocaps := (ocaps (os nid))(p := ocaps (os nid) p @ xs p),
    inter := operator_state.inter (os nid) @ map (\<lambda>t. (p, t, 1)) (xs p)\<rparr>)"
  have inv1: "dataplane_tracker_inv ?os1 cbufs sg"
    apply (rule dataplane_tracker_inv_mints_many[OF D])
       apply (rule Cons.prems(1))
      apply (rule Cons.prems(2))
     using Cons.prems(4) apply simp
    done
  have gs1: "graph_summar_nt (summ sg) (nxt sg) ?os1"
    using Cons.prems(2) by (auto simp add: graph_summar_nt_def)
  have supp1:
    "\<forall>p\<in>set ps. \<forall>t\<in>set (xs p). \<exists>t'\<in>set (ocaps (?os1 nid) p). t' \<le> t"
    using Cons.prems by auto
  have distinct_ps: "distinct ps"
    using Cons.prems by simp
  have inv2:
    "dataplane_tracker_inv
       (?os1(nid := ?os1 nid\<lparr>
          ocaps := (\<lambda>p. ocaps (?os1 nid) p @ (if p \<in> set ps then xs p else [])),
          inter := operator_state.inter (?os1 nid) @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (xs p)) ps)\<rparr>))
       cbufs sg"
    using Cons.hyps[OF inv1 gs1 distinct_ps supp1] .
  have eq:
    "(?os1(nid := ?os1 nid\<lparr>
       ocaps := (\<lambda>pa. ocaps (?os1 nid) pa @ (if pa \<in> set ps then xs pa else [])),
       inter := operator_state.inter (?os1 nid) @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (xs p)) ps)\<rparr>)) =
     (os(nid := os nid\<lparr>
       ocaps := (\<lambda>pa. ocaps (os nid) pa @ (if pa \<in> set (p # ps) then xs pa else [])),
       inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (xs p)) (p # ps))\<rparr>))"
    using Cons.prems by (auto simp add: fun_eq_iff)
  show ?case
    using inv2 eq by metis
qed

lemma dataplane_tracker_inv_mints_many_ports:
  assumes D: "dataflow_topology (summ sg) (-+-)"
  shows
    "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
     graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
     (\<forall> p. \<forall> t \<in> set (xs p). \<exists> t' \<in> set (ocaps (os nid) p). t' \<le> t) \<Longrightarrow>
     dataplane_tracker_inv
       (os(nid := os nid\<lparr>
          ocaps := (\<lambda>p. ocaps (os nid) p @ xs p),
          inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (xs p)) Enum.enum)\<rparr>))
       cbufs sg"
proof -
  assume inv: "dataplane_tracker_inv os cbufs sg"
  assume gs: "graph_summar_nt (summ sg) (nxt sg) os"
  assume supp: "\<forall>p. \<forall>t\<in>set (xs p). \<exists>t'\<in>set (ocaps (os nid) p). t' \<le> t"
  have inv_enum:
    "dataplane_tracker_inv
       (os(nid := os nid\<lparr>
          ocaps := (\<lambda>p. ocaps (os nid) p @ (if p \<in> set Enum.enum then xs p else [])),
          inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (xs p)) Enum.enum)\<rparr>))
       cbufs sg"
    apply (rule dataplane_tracker_inv_mints_many_list[OF D])
       apply (rule inv)
      apply (rule gs)
     apply simp
    using supp apply simp
    done
  then show ?thesis
    by simp
qed

lemma dataplane_tracker_inv_add_cap:
  assumes \<open>dataflow_topology (summ sg) (-+-)\<close> \<open>dataplane_tracker_inv os cbufs sg\<close>
    \<open>graph_summar_nt (summ sg) (subgraph.nxt sg) os\<close> \<open>\<exists>t' \<in>  set (ocaps (os nid) p). t' \<le> t\<close>
    \<open>os' = os(nid := add_cap (os nid) p t)\<close>
  shows \<open>dataplane_tracker_inv os' cbufs sg\<close>
proof -
  have \<open>dataplane_tracker_inv (os(nid := (os nid)\<lparr>
  ocaps := (ocaps (os nid))(p := ocaps (os nid) p @ [t]),
  inter := operator_state.inter (os nid) @ [(p, t, 1)]\<rparr>))
  cbufs sg\<close> (is \<open>dataplane_tracker_inv ?os' _ _\<close>)
    using dataplane_tracker_inv_mints[OF assms(1-3) _ assms(4), where m=1] by simp
  moreover have \<open>?os' = os'\<close> by (simp add: assms(5) add_cap_def fun_eq_iff)
  ultimately show ?thesis by simp
qed

end
