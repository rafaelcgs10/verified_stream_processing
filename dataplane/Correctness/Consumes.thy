theory Consumes

imports
  General
begin

declare cin.rep_eq[simp del]
declare enum_class.enum_UNIV[simp] enum_class.enum_distinct[simp]
declare filter_True[simp del] filter_False[simp del] list_emb_Nil2[simp del] BULK_BENQ_right_empty[simp del] BULK_BENQ_left_empty[simp del]
declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]


section \<open>Channel Data Justifies Pointstamps\<close>

text \<open>Each timestamp of data sitting in a channel is covered by a
  positive pointstamp count at the receiving target, counting in-flight
  productions.\<close>
lemma data_in_channel_justifies_c_pts_alt:
  "Trg_caps_inv caps chnls \<Longrightarrow>
   c_pts_inv (change_multiplicities su (extract_prog Enum.enum nt os) c) caps \<Longrightarrow> 
   t \<in> snd ` set (chnls (nid, p)) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (produ (os n)). m \<ge> 0) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (consu (os n)). m \<ge> 0) \<Longrightarrow>
   inj_on nt (dom nt) \<Longrightarrow>
   zcount (c_pts c (Loc nid (Trg p)) + zmset (concat (map (\<lambda> (nid', p'). (map snd (filter (\<lambda> (p'', _, _). nt (nid', p'') = Some (nid, p) \<and> p' = p'') (produ (os nid'))))) Enum.enum))) t > 0"
  unfolding Trg_caps_inv_def
  apply (drule spec[of _ nid])
  apply (drule spec[of _ p])
  unfolding c_pts_inv_def
  apply (drule spec[of _ "Loc nid (Trg p)"])
  apply (simp add: c_pts_change_multiplicities)
  subgoal premises prems3
    using prems3(1,6) apply -
    unfolding extract_prog_def obtain_progress_def extract_progress_def
    apply (simp add:  BULK_BENQ_def zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
    apply (subst (asm) (1) monoid_add_class.sum_list_distinct_conv_sum_set)
    apply (simp_all)
    apply (subst (asm) Groups.ab_group_add_class.ab_diff_conv_add_uminus)
    apply (subst (asm) comm_monoid_add_class.sum.distrib)
    apply (subgoal_tac 
        "((\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (List.map_filter (\<lambda>(p, t, m). case nt (x, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os x))))))) =
  (\<Sum>x\<leftarrow>enum_class.enum. zmset (map snd (filter (\<lambda>(p'', ab). nt (fst x, p'') = Some (nid, p) \<and> snd x = p'') (produ (os (fst x))))))")
    subgoal
      apply (simp add: zmultiset_eq_iff)
      apply (drule spec[of _ t])+
      apply (simp add:  comp_def split_beta monoid_add_class.sum_list_distinct_conv_sum_set zcount_sum)
      apply (subgoal_tac "zcount (to_zmset (map snd (chnls (nid, p)))) t > 0")
      subgoal
        apply (drule sym)
        apply simp
        apply (drule plus_minus_gt)
        subgoal
          apply (rule zcount_zmset_ge_0I)
          using prems3  apply auto
          done
        subgoal
          supply filter_True[simp] filter_False[simp] list_emb_Nil2[simp] BULK_BENQ_right_empty[simp] BULK_BENQ_left_empty[simp]
          by auto
        done
      subgoal
        apply (auto simp add: zcount_to_zmset)
        done
      done
    subgoal premises prems4
      apply (auto simp add: comp_def filter_map zcount_sum monoid_add_class.sum_list_distinct_conv_sum_set List.map_filter_def split_beta split: option.splits)
      apply (cases "\<exists> nid' p'. nt (nid', p') = Some (nid, p)")
      subgoal
        apply clarsimp
        subgoal for nid' p'
          apply (subst comm_monoid_add_class.sum.subset_diff[of "{nid'}"])
          apply simp_all
          apply (subst comm_monoid_add_class.sum.neutral)
          subgoal
            apply (intro ballI)
            apply (auto simp add: filter_empty_conv split: prod.splits intro!: zmset_emptyI)
            using prems3(4)
            apply (metis domI inj_on_contraD not_Some_eq2 prod.simps(1))
            done
          apply simp
          apply (subst comm_monoid_add_class.sum.subset_diff[of "{(nid', p')}"])
          apply simp_all
          apply (subst comm_monoid_add_class.sum.neutral)
          subgoal
            apply (intro ballI)
            apply (auto simp add: filter_empty_conv split: prod.splits intro!: zmset_emptyI)
            using prems3(4)
            apply (metis domI inj_on_contraD not_Some_eq2 prod.simps(1))+
            done
          apply simp
          apply (rule arg_cong[where f=zmset])
          apply (rule map_cong)
          subgoal
            apply (rule filter_cong)
            apply auto
            using prems3(4)
            apply (metis domI inj_on_contraD not_Some_eq2 prod.simps(1))
            done
          apply auto
          done
        done
      subgoal
        apply (subst comm_monoid_add_class.sum.neutral)
        subgoal
          apply (intro ballI)
          apply (auto simp add: filter_empty_conv split: prod.splits intro!: zmset_emptyI)
          apply (metis not_Some_eq2)
          done
        apply (subst comm_monoid_add_class.sum.neutral)
        subgoal
          apply (intro ballI)
          apply (auto simp add: filter_empty_conv split: prod.splits intro!: zmset_emptyI)
          done
        apply auto
        done
      done
    done
  done

section \<open>Extracted Progress Stays above the Implied Frontier\<close>

text \<open>Progress changes extracted at a consume step never fall below the
  implied frontier of the consuming location.\<close>
lemma extract_prog_changes_above_impl_inv_consumes:
  assumes D: "dataflow_topology su (-+-)"
    and C: "cbufs (nid, p) = (d, t) # cbufs'"
    and S: "Src_caps_inv caps os"
    and T: "Trg_caps_inv caps (outputs_at_target su os >> cbufs)"
    and P: "c_pts_inv (change_multiplicities su (extract_prog enum_class.enum nt os) c) caps"
    and CA: "change_deltas_inv os"
    and G: "graph_summar_nt su nt os"
    and PR: "produ_consu_inter_supported nt os c"
    and E: "extract_prog_changes_above_impl_inv su nt c os"
  shows 
    "extract_prog_changes_above_impl_inv su nt c (os(nid := consumes (os nid) p t d))"
  using C PR P T G CA apply -
  unfolding extract_prog_changes_above_impl_inv_def
  apply (auto 0 0)
  defer
  subgoal for nid' xs
    unfolding changes_above_impl_inv_def
    apply safe
    subgoal for l t' m
      apply (cases "nid \<in> set xs"; simp?)
      subgoal
        apply (cases "\<exists> s p'' t''. t'' \<in> set (intsum (os nid) p p'') \<and> s \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) l \<and> t -+- t'' -+- s \<le> t'")
        subgoal
          apply clarsimp
          subgoal for s p'' t''
            apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, of s _ _ _ "t -+- t''"])
            apply assumption
            subgoal
              apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid (Src p'')", simplified, OF D])
              subgoal
                apply (rule graph.path_weight_refl)
                apply (rule dataflow_topology.axioms(1))
                using D apply assumption
                done
              subgoal
                subgoal
                  using S apply -
                  unfolding Src_caps_inv_def
                  apply (drule spec[of _ nid])
                  apply (drule spec[of _ p''])
                  unfolding c_pts_inv_def
                  apply (drule spec[of _ "Loc nid (Src p'')"])
                  apply simp
                  unfolding zmultiset_eq_iff
                  apply (drule spec[of _ "t -+- t''"])+
                  apply (simp add: c_pts_change_multiplicities)
                  apply (subgoal_tac "zcount (c_pts c (Loc nid (Src p'')) + zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p'') = l') (extract_prog xs nt (os(nid := consumes (os nid) p t d)))))) (t -+- t'') > 0")
                  subgoal
                    using frontier_less_equal_zcount_pos 
                    by force
                  subgoal
                    apply (subgoal_tac "zcount (zmset (map snd (filter ((=) p'' \<circ> fst) (concat (map (\<lambda>p'. map (\<lambda>t'. (p', t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))) (t -+- t'') > 0")
                    subgoal
                      apply (simp add: zmset_map_filter_Src_extract_prog)
                      using to_zmset_nenneg[of "ocaps (os nid) p''" "t -+- t''"] by linarith
                    subgoal
                      apply (rule zcount_zmset_gt_0I)
                      apply (auto simp add: image_iff)
                      done
                    done
                  done
                done
              done
            subgoal
              by fast
            done
          done
        subgoal
          using E[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs" nid', unfolded changes_above_impl_inv_def] apply -
          apply simp
          apply (drule bspec)
          apply assumption
          apply simp
          apply (subst (asm) extract_progress_def)
          apply (subst (asm) (1 2 3) obtain_progress_def)
          apply (clarsimp simp add: image_iff Misc.set_map_filter split: option.splits; hypsubst_thin?)
          subgoal for p' m
            apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
            apply (subst (asm) Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
            apply simp_all
            apply fast
            apply (drule frontier_less_equal_add_cases)
            apply (elim disjE)
            subgoal
              apply (subst (asm) frontier_less_equal_iff)
              apply clarsimp
              subgoal for ft
                apply (drule in_frontier_sumEx)
                apply (simp_all add: zcount_sum image_iff split_beta)
                subgoal
                  by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                subgoal
                  apply (elim conjE bexE)
                  apply (drule in_frontier_sumEx)
                  apply (simp_all add: zcount_sum image_iff split_beta)
                  apply clarsimp
                  subgoal for l' s
                    apply (drule in_frontier_zmset_imageD)
                    apply clarsimp
                    subgoal for ft
                      apply hypsubst_thin
                      apply (elim disjE rangeE)
                      subgoal 
                        apply (clarsimp simp add: split: prod.splits)
                        subgoal for nid'' p''
                          apply hypsubst_thin
                          apply (cases "nid'' = nid \<and> p'' = p")
                          subgoal
                            apply clarsimp
                            apply (simp_all flip: member_antichain.rep_eq)
                            apply hypsubst_thin
                            apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                            apply simp_all
                            apply (subgoal_tac "\<exists> t p'' s'. t \<in> set (intsum (os nid) p p'') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) (Loc nid' (Trg p')) \<and> s = t -+- s'")
                            defer
                            subgoal
                              using G[unfolded graph_summar_nt_def]
                              by blast
                            subgoal
                              apply clarsimp
                              subgoal for t'' p'' s'
                                apply hypsubst_thin
                                apply (drule spec2, drule mp, assumption)
                                apply (drule spec, drule mp, assumption)
                                apply (subgoal_tac "ft \<noteq> t")
                                defer
                                subgoal
                                  by (metis dataflow_topology_from_tree.followed_by_summary)
                                apply (simp add: change_multiplicities_comm change_multiplicities_append_alt)
                                apply (drule in_frontier_c_pts_change_multiplicities_consumes_Trg[where t=t and d=d]) 
                                apply simp
                                apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                                apply assumption
                                apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Trg p)" _ _ ft])
                                subgoal
                                  apply (rule graph.path_weight_refl)
                                  apply (rule dataflow_topology.axioms(1)[OF D])
                                  done
                                subgoal
                                  apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                  apply (metis (no_types, opaque_lifting) change_multiplicities_append change_multiplicities_comm frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                                  done
                                subgoal
                                  by auto
                                done
                              done
                            done
                          subgoal
                            apply clarsimp
                            apply (simp_all flip: member_antichain.rep_eq)
                            apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                            apply assumption
                            defer
                            apply assumption
                            apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Trg p'')" _ _ ft, simplified])
                            subgoal
                              apply (rule graph.path_weight_refl)
                              apply (rule dataflow_topology.axioms(1)[OF D])
                              done
                            subgoal
                              apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                              apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                              apply (simp add: zmset_filter_extract_progress_Trg_consumes_diff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                              unfolding frontier_less_equal_iff
                              apply (rule exI[of _ ft])
                              apply auto
                              done
                            done
                          done
                        done
                      subgoal
                        apply clarsimp
                        subgoal for nid'' p''
                          apply (cases "nid'' = nid \<and> (\<exists> t. t \<in> set (intsum (os nid) p p''))")
                          subgoal
                            apply clarsimp
                            subgoal for t''
                              apply hypsubst_thin
                              apply (simp_all flip: member_antichain.rep_eq)
                              apply (drule spec2, drule mp, assumption)
                              apply (drule spec, drule mp, assumption)
                              apply (subgoal_tac " ft \<noteq> t -+- t''")
                              defer
                              subgoal
                                by fast
                              apply (drule in_frontier_addEx[where B="to_zmset (map ((-+-) t) (intsum (os nid) p p''))"])
                              subgoal
                                using to_zmset_nenneg by fast
                              apply clarsimp
                              subgoal for ft'
                                apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft'])
                                apply assumption
                                defer
                                subgoal
                                  by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(23))
                                apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Src p'')" _ _ ft', simplified])
                                subgoal
                                  apply (rule graph.path_weight_refl)
                                  apply (rule dataflow_topology.axioms(1)[OF D])
                                  done
                                subgoal
                                  apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                  apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                  apply (simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                  using Groups.add_ac(2) frontier_less_equal_zcount_pos group_cancel.add2 member_frontier_pos_zmset 
                                proof -
                                  assume "ft' \<in>\<^sub>A frontier (c_pts c (Loc nid (Src p'')) + (zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p'') = l') (extract_progress nid nt (snd (obtain_progress (os nid)))))) + zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p'') = l') (extract_prog (remove1 nid xs) nt os)))) + to_zmset (map ((-+-) t) (intsum (os nid) p p'')))"
                                  then show "frontier_less_equal (frontier (c_pts c (Loc nid (Src p'')) + (zmset (map snd (filter (\<lambda>(l, c, i). Loc nid (Src p'') = l) (extract_progress nid nt (snd (obtain_progress (os nid)))))) + to_zmset (map ((-+-) t) (intsum (os nid) p p'')) + zmset (map snd (filter (\<lambda>(l, c, i). Loc nid (Src p'') = l) (extract_prog (remove1 nid xs) nt os)))))) ft'"
                                    by (smt (verit) Groups.add_ac(2) frontier_less_equal_zcount_pos group_cancel.add2 member_frontier_pos_zmset)
                                qed

                                done
                              done
                            done
                          subgoal
                            apply (clarsimp simp flip: member_antichain.rep_eq)
                            apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft])
                            apply assumption
                            defer
                            apply assumption
                            apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Src p'')" _ _ ft, simplified])
                            subgoal
                              apply (rule graph.path_weight_refl)
                              apply (rule dataflow_topology.axioms(1)[OF D])
                              done
                            subgoal
                              apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                              apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                              apply (simp add: zmset_filter_extract_progress_Src_consumes_no_intsum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                              apply (meson frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                              done
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done
            subgoal
              apply (subst Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
              apply (subst Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
              apply simp_all
              apply fast
              apply (rule frontier_less_equal_addI)
              subgoal
                apply (rule disjI2)
                apply (subst (asm) frontier_less_equal_iff)
                apply clarsimp
                subgoal for ft
                  apply (drule in_frontier_sumEx)
                  apply (simp_all add: zcount_sum image_iff split_beta)
                  subgoal
                    by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                  subgoal
                    apply clarsimp
                    subgoal for l'
                      apply (drule in_frontier_sumEx)
                      apply (simp_all add: zcount_sum image_iff split_beta)
                      apply clarsimp
                      subgoal for s
                        apply (drule in_frontier_zmset_imageD)
                        apply clarsimp
                        subgoal for ft
                          apply hypsubst_thin
                          apply (rule frontier_less_equal_sumI[where l=l'])
                          apply simp
                          subgoal
                            by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                          subgoal
                            by (clarsimp simp add: zcount_sum image_iff split_beta)
                          subgoal
                            apply (rule frontier_less_equal_sumI[where l=s])
                            apply simp_all
                            unfolding frontier_less_equal_iff
                            apply (subst in_frontier_zmset_image)
                            apply simp_all
                            apply (subst change_multiplicities_extract_prog_consumes)
                            apply simp_all
                            apply (clarsimp simp add: c_pts_change_multiplicities)
                            apply (cases "l' = Loc nid (Trg p)"; simp)
                            apply (drule in_frontier_in_frontier_add[where t=ft and B="zmset (map snd (filter (\<lambda>(l'a, t, d). l' = l'a) (concat (map (\<lambda>p'. map (\<lambda>t'. (Loc nid (Src p'), t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))"])
                            subgoal
                              by (clarsimp simp add: zcount_sum image_iff split_beta intro!: zcount_zmset_ge_0I)
                            apply clarsimp
                            subgoal for ft3
                              apply (rule exI[of _ "ft3 -+- s"])
                              apply simp
                              apply (intro conjI)
                              apply (metis (no_types, lifting) nat_arith.add1)
                              apply (meson assms(1) basic_trans_rules(23) dataflow_topology.results_in_mono(1)) 
                              done
                            done
                          done
                        done
                      done
                    done
                  done
                done
              subgoal
                by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
              subgoal
                by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
              done
            done
          subgoal  for p'
            apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
            apply (subst (asm) Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
            apply simp_all
            apply fast
            apply (drule frontier_less_equal_add_cases)
            apply (elim disjE)
            subgoal
              apply (subst (asm) frontier_less_equal_iff)
              apply clarsimp
              subgoal for ft
                apply (drule in_frontier_sumEx)
                apply (simp_all add: zcount_sum image_iff split_beta)
                subgoal
                  by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                subgoal
                  apply (elim conjE bexE)
                  apply (drule in_frontier_sumEx)
                  apply (simp_all add: zcount_sum image_iff split_beta)
                  apply clarsimp
                  subgoal for l' s
                    apply (drule in_frontier_zmset_imageD)
                    apply clarsimp
                    subgoal for ft
                      apply hypsubst_thin
                      apply (elim disjE rangeE)
                      subgoal 
                        apply (clarsimp simp add: split: prod.splits)
                        subgoal for nid'' p''
                          apply hypsubst_thin
                          apply (cases "nid'' = nid \<and> p'' = p")
                          subgoal
                            apply clarsimp
                            apply (simp_all flip: member_antichain.rep_eq)
                            apply hypsubst_thin
                            apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                            apply simp_all
                            apply (subgoal_tac "\<exists> t p'' s'. t \<in> set (intsum (os nid) p p'') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) (Loc nid' (Src p')) \<and> s = t -+- s'")
                            defer
                            subgoal
                              using G[unfolded graph_summar_nt_def]
                              by blast
                            subgoal
                              apply clarsimp
                              subgoal for t'' p'' s'
                                apply hypsubst_thin
                                apply (drule spec2, drule mp, assumption)
                                apply (drule spec, drule mp, assumption)
                                apply (subgoal_tac "ft \<noteq> t")
                                defer
                                subgoal
                                  by (metis dataflow_topology_from_tree.followed_by_summary)
                                apply (simp add: change_multiplicities_comm change_multiplicities_append_alt)
                                apply (drule in_frontier_c_pts_change_multiplicities_consumes_Trg[where t=t and d=d]) 
                                apply simp
                                apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                                apply assumption
                                apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Trg p)" _ _ ft])
                                subgoal
                                  apply (rule graph.path_weight_refl)
                                  apply (rule dataflow_topology.axioms(1)[OF D])
                                  done
                                subgoal
                                  apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                  apply (metis (no_types, opaque_lifting) change_multiplicities_append change_multiplicities_comm frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                                  done
                                subgoal
                                  by auto
                                done
                              done
                            done
                          subgoal
                            apply clarsimp
                            apply (simp_all flip: member_antichain.rep_eq)
                            apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                            apply assumption
                            defer
                            apply assumption
                            apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Trg p'')" _ _ ft, simplified])
                            subgoal
                              apply (rule graph.path_weight_refl)
                              apply (rule dataflow_topology.axioms(1)[OF D])
                              done
                            subgoal
                              apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                              apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                              apply (simp add: zmset_filter_extract_progress_Trg_consumes_diff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                              unfolding frontier_less_equal_iff
                              apply (rule exI[of _ ft])
                              apply auto
                              done
                            done
                          done
                        done


                      subgoal
                        apply clarsimp
                        subgoal for nid'' p''
                          apply (cases "nid'' = nid \<and> (\<exists> t. t \<in> set (intsum (os nid) p p''))")
                          subgoal
                            apply clarsimp
                            subgoal for t''
                              apply hypsubst_thin
                              apply (simp_all flip: member_antichain.rep_eq)
                              apply (drule spec2, drule mp, assumption)
                              apply (drule spec, drule mp, assumption)
                              apply (subgoal_tac " ft \<noteq> t -+- t''")
                              defer
                              subgoal
                                by fast
                              apply (drule in_frontier_addEx[where B="to_zmset (map ((-+-) t) (intsum (os nid) p p''))"])
                              subgoal
                                using to_zmset_nenneg by fast
                              apply clarsimp
                              subgoal for ft'
                                apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft'])
                                apply assumption
                                defer
                                subgoal
                                  by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(23))
                                apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Src p'')" _ _ ft', simplified])
                                subgoal
                                  apply (rule graph.path_weight_refl)
                                  apply (rule dataflow_topology.axioms(1)[OF D])
                                  done
                                subgoal
                                  apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                  apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                  apply (simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                proof -
                                  assume "ft' \<in>\<^sub>A frontier (c_pts c (Loc nid (Src p'')) + (zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p'') = l') (extract_progress nid nt (snd (obtain_progress (os nid)))))) + zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p'') = l') (extract_prog (remove1 nid xs) nt os)))) + to_zmset (map ((-+-) t) (intsum (os nid) p p'')))"
                                  then show "frontier_less_equal (frontier (c_pts c (Loc nid (Src p'')) + (zmset (map snd (filter (\<lambda>(l, c, i). Loc nid (Src p'') = l) (extract_progress nid nt (snd (obtain_progress (os nid)))))) + to_zmset (map ((-+-) t) (intsum (os nid) p p'')) + zmset (map snd (filter (\<lambda>(l, c, i). Loc nid (Src p'') = l) (extract_prog (remove1 nid xs) nt os)))))) ft'"
                                    by (smt (verit) Groups.add_ac(2) frontier_less_equal_zcount_pos group_cancel.add2 member_frontier_pos_zmset)
                                qed                                  
                                done
                              done
                            done
                          subgoal
                            apply (clarsimp simp flip: member_antichain.rep_eq)
                            apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft])
                            apply assumption
                            defer
                            apply assumption
                            apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Src p'')" _ _ ft, simplified])
                            subgoal
                              apply (rule graph.path_weight_refl)
                              apply (rule dataflow_topology.axioms(1)[OF D])
                              done
                            subgoal
                              apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                              apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                              apply (simp add: zmset_filter_extract_progress_Src_consumes_no_intsum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                              apply (meson frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                              done
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done

            subgoal
              subgoal
                apply (subst Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
                apply (subst Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
                apply simp_all
                apply fast
                apply (rule frontier_less_equal_addI)
                subgoal
                  apply (rule disjI2)
                  apply (subst (asm) frontier_less_equal_iff)
                  apply clarsimp
                  subgoal for ft
                    apply (drule in_frontier_sumEx)
                    apply (simp_all add: zcount_sum image_iff split_beta)
                    subgoal
                      by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                    subgoal
                      apply clarsimp
                      subgoal for l'
                        apply (drule in_frontier_sumEx)
                        apply (simp_all add: zcount_sum image_iff split_beta)
                        apply clarsimp
                        subgoal for s
                          apply (drule in_frontier_zmset_imageD)
                          apply clarsimp
                          subgoal for ft
                            apply hypsubst_thin
                            apply (rule frontier_less_equal_sumI[where l=l'])
                            apply simp
                            subgoal
                              by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                            subgoal
                              by (clarsimp simp add: zcount_sum image_iff split_beta)
                            subgoal
                              apply (rule frontier_less_equal_sumI[where l=s])
                              apply simp_all
                              unfolding frontier_less_equal_iff
                              apply (subst in_frontier_zmset_image)
                              apply simp_all
                              apply (subst change_multiplicities_extract_prog_consumes)
                              apply simp_all
                              apply (clarsimp simp add: c_pts_change_multiplicities)
                              apply (cases "l' = Loc nid (Trg p)"; simp)
                              apply (drule in_frontier_in_frontier_add[where t=ft and B="zmset (map snd (filter (\<lambda>(l'a, t, d). l' = l'a) (concat (map (\<lambda>p'. map (\<lambda>t'. (Loc nid (Src p'), t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))"])
                              subgoal
                                by (clarsimp simp add: zcount_sum image_iff split_beta intro!: zcount_zmset_ge_0I)
                              apply clarsimp
                              subgoal for ft3
                                apply (rule exI[of _ "ft3 -+- s"])
                                apply simp
                                apply (intro conjI)
                                apply (metis (no_types, lifting) nat_arith.add1)
                                apply (meson assms(1) basic_trans_rules(23) dataflow_topology.results_in_mono(1)) 
                                done
                              done
                            done
                          done
                        done
                      done
                    done
                  done
                subgoal
                  by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                subgoal
                  by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                done
              done
            done


          subgoal for p' nid'' p''
            supply filter_True[simp] filter_False[simp] list_emb_Nil2[simp] BULK_BENQ_right_empty[simp] BULK_BENQ_left_empty[simp]
            using conjunct1[OF PR[unfolded produ_consu_inter_supported_def]] apply -
            apply (drule spec2, drule spec2, drule mp, assumption)
            apply (elim disjE)
            subgoal
              apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid' (Src p')", simplified, OF D])
              subgoal
                using G apply -
                unfolding graph_summar_nt_def
                using path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF D]]
                by auto
              subgoal
                apply (subst change_multiplicities_extract_prog_consumes)
                apply simp_all
                apply (clarsimp simp add: c_pts_change_multiplicities )
                apply (subst filter_False)
                subgoal  apply -
                  unfolding extract_prog_def extract_progress_def
                  apply (auto simp add: Misc.set_map_filter split: option.splits)
                  done
                apply simp
                apply (meson frontier_less_equal_zcount_pos)
                done
              done
            subgoal
              apply clarsimp
              using E[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs" nid', unfolded changes_above_impl_inv_def] apply -
              apply simp
              apply (drule bspec)
              apply (subst obtain_progress_def)
              apply (subst extract_progress_def)
              apply simp
              apply force
              apply simp
              subgoal premises temp for m'
                using temp(1,2,4-) apply -
                apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc nid' (Src p')", simplified, OF D])
                subgoal
                  using G apply -
                  unfolding graph_summar_nt_def using path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF D]]
                  by auto
                subgoal
                  apply (subgoal_tac 
                      "nid \<in> set xs \<Longrightarrow>
    \<forall>s p''. s \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) (Loc nid' (Src p')) \<longrightarrow> (\<forall>t''. t'' \<in> set (intsum (os nid) p p'') \<longrightarrow> \<not> t -+- t'' -+- s \<le> t') \<Longrightarrow>
    frontier_less_equal (ifrontier su (-+-) (change_multiplicities su (extract_prog xs nt os) c) (Loc nid' (Src p'))) t' \<Longrightarrow>
    nid' \<noteq> nid \<Longrightarrow> distinct xs \<Longrightarrow> nid' \<notin> set xs \<Longrightarrow> frontier_less_equal (ifrontier su (-+-) (change_multiplicities su (extract_prog xs nt (os(nid := consumes (os nid) p t d))) c) (Loc nid' (Src p'))) t'")
                  subgoal
                    apply (drule meta_mp)
                    apply assumption
                    apply (drule meta_mp)
                    subgoal
                      apply safe
                      subgoal for s' p''' t''
                        apply (drule graph.path_weight_elem_trans[rotated 1, of _ _ _ _ 0 "Loc nid'' (Trg p'')"])
                        subgoal
                          using G apply -
                          unfolding graph_summar_nt_def using path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF D]]
                          by auto
                        subgoal
                          by (rule dataflow_topology.axioms(1)[OF D])
                        apply clarsimp
                        apply (metis add.assoc le_iff_add)
                        done
                      done
                    apply (drule meta_mp)
                    apply assumption
                    apply (drule meta_mp)
                    apply assumption
                    apply (drule meta_mp)
                    apply assumption
                    apply (drule meta_mp)
                    apply assumption
                    apply simp
                    done
                  subgoal premises temp
                    using temp(17-) apply -
                    apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
                    apply (subst (asm) Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
                    apply simp_all
                    apply fast
                    apply (drule frontier_less_equal_add_cases)
                    apply (elim disjE)
                    subgoal
                      apply (subst (asm) frontier_less_equal_iff)
                      apply clarsimp
                      subgoal for ft
                        apply (drule in_frontier_sumEx)
                        apply (simp_all add: zcount_sum image_iff split_beta)
                        subgoal
                          by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                        subgoal
                          apply (elim conjE bexE)
                          apply (drule in_frontier_sumEx)
                          apply (simp_all add: zcount_sum image_iff split_beta)
                          apply clarsimp
                          subgoal for l' s
                            apply (drule in_frontier_zmset_imageD)
                            apply clarsimp
                            subgoal for ft
                              apply hypsubst_thin
                              apply (elim disjE rangeE)
                              subgoal 
                                apply (clarsimp simp add: split: prod.splits)
                                subgoal for nid'' p''
                                  apply hypsubst_thin
                                  apply (cases "nid'' = nid \<and> p'' = p")
                                  subgoal
                                    apply clarsimp
                                    apply (simp_all flip: member_antichain.rep_eq)
                                    apply hypsubst_thin
                                    apply (subst (asm) (3) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                    apply simp_all
                                    apply (subgoal_tac "\<exists> t p'' s'. t \<in> set (intsum (os nid) p p'') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) (Loc nid' (Src p')) \<and> s = t -+- s'")
                                    defer
                                    subgoal
                                      using G[unfolded graph_summar_nt_def]
                                      by blast
                                    subgoal
                                      apply clarsimp
                                      subgoal for t'' p'' s'
                                        apply hypsubst_thin
                                        apply (drule spec2, drule mp, assumption)
                                        apply (drule spec, drule mp, assumption)
                                        apply (subgoal_tac "ft \<noteq> t")
                                        defer
                                        subgoal
                                          by (metis dataflow_topology_from_tree.followed_by_summary)
                                        apply (simp add: change_multiplicities_comm change_multiplicities_append_alt)
                                        apply (drule in_frontier_c_pts_change_multiplicities_consumes_Trg[where t=t and d=d]) 
                                        apply simp
                                        apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                                        apply assumption
                                        apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Trg p)" _ _ ft])
                                        subgoal
                                          apply (rule graph.path_weight_refl)
                                          apply (rule dataflow_topology.axioms(1)[OF D])
                                          done
                                        subgoal
                                          apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                          apply simp_all
                                          apply (metis (no_types, opaque_lifting) change_multiplicities_append change_multiplicities_comm frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                                          done
                                        subgoal
                                          by auto
                                        done
                                      done
                                    done
                                  subgoal
                                    apply clarsimp
                                    apply (simp_all flip: member_antichain.rep_eq)
                                    apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                                    apply assumption
                                    defer
                                    apply assumption
                                    apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Trg p'')" _ _ ft, simplified])
                                    subgoal
                                      apply (rule graph.path_weight_refl)
                                      apply (rule dataflow_topology.axioms(1)[OF D])
                                      done
                                    subgoal
                                      apply (subst (asm) (3) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                      apply simp_all
                                      apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                      apply simp_all
                                      apply (simp add: zmset_filter_extract_progress_Trg_consumes_diff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                      unfolding frontier_less_equal_iff
                                      apply (rule exI[of _ ft])
                                      apply auto
                                      done
                                    done
                                  done
                                done


                              subgoal
                                apply clarsimp
                                subgoal for nid'' p''
                                  apply (cases "nid'' = nid \<and> (\<exists> t. t \<in> set (intsum (os nid) p p''))")
                                  subgoal
                                    apply clarsimp
                                    subgoal for t''
                                      apply hypsubst_thin
                                      apply (simp_all flip: member_antichain.rep_eq)
                                      apply (drule spec2, drule mp, assumption)
                                      apply (drule spec, drule mp, assumption)
                                      apply (subgoal_tac " ft \<noteq> t -+- t''")
                                      defer
                                      subgoal
                                        by fast
                                      apply (drule in_frontier_addEx[where B="to_zmset (map ((-+-) t) (intsum (os nid) p p''))"])
                                      subgoal
                                        using to_zmset_nenneg by fast
                                      apply clarsimp
                                      subgoal for ft'
                                        apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft'])
                                        apply assumption
                                        defer
                                        subgoal
                                          by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(23))
                                        apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Src p'')" _ _ ft', simplified])
                                        subgoal
                                          apply (rule graph.path_weight_refl)
                                          apply (rule dataflow_topology.axioms(1)[OF D])
                                          done
                                        subgoal
                                          apply (subst (asm) (3) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                          apply simp_all
                                          apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                          apply simp_all
                                          apply (simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                        proof -
                                          assume "ft' \<in>\<^sub>A frontier (c_pts c (Loc nid (Src p'')) + (zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p'') = l') (extract_progress nid nt (snd (obtain_progress (os nid)))))) + zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p'') = l') (extract_prog (remove1 nid xs) nt os)))) + to_zmset (map ((-+-) t) (intsum (os nid) p p'')))"
                                          then show "frontier_less_equal (frontier (c_pts c (Loc nid (Src p'')) + (zmset (map snd (filter (\<lambda>(l, c, i). Loc nid (Src p'') = l) (extract_progress nid nt (snd (obtain_progress (os nid)))))) + to_zmset (map ((-+-) t) (intsum (os nid) p p'')) + zmset (map snd (filter (\<lambda>(l, c, i). Loc nid (Src p'') = l) (extract_prog (remove1 nid xs) nt os)))))) ft'"
                                            by (smt (verit) Groups.add_ac(2) frontier_less_equal_zcount_pos group_cancel.add2 member_frontier_pos_zmset)
                                        qed
                                        done
                                      done
                                    done
                                  subgoal
                                    apply (clarsimp simp flip: member_antichain.rep_eq)
                                    apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft])
                                    apply assumption
                                    defer
                                    apply assumption
                                    apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Src p'')" _ _ ft, simplified])
                                    subgoal
                                      apply (rule graph.path_weight_refl)
                                      apply (rule dataflow_topology.axioms(1)[OF D])
                                      done
                                    subgoal
                                      apply (subst (asm) (3) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                      apply simp_all
                                      apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                      apply simp_all
                                      apply (simp add: zmset_filter_extract_progress_Src_consumes_no_intsum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                      apply (meson frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      done

                    subgoal
                      subgoal
                        apply (subst Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
                        apply (subst Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
                        apply simp_all
                        apply fast
                        apply (rule frontier_less_equal_addI)
                        subgoal
                          apply (rule disjI2)
                          apply (subst (asm) frontier_less_equal_iff)
                          apply clarsimp
                          subgoal for ft
                            apply (drule in_frontier_sumEx)
                            apply (simp_all add: zcount_sum image_iff split_beta)
                            subgoal
                              by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                            subgoal
                              apply clarsimp
                              subgoal for l'
                                apply (drule in_frontier_sumEx)
                                apply (simp_all add: zcount_sum image_iff split_beta)
                                apply clarsimp
                                subgoal for s
                                  apply (drule in_frontier_zmset_imageD)
                                  apply clarsimp
                                  subgoal for ft
                                    apply hypsubst_thin
                                    apply (rule frontier_less_equal_sumI[where l=l'])
                                    apply simp
                                    subgoal
                                      by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                                    subgoal
                                      by (clarsimp simp add: zcount_sum image_iff split_beta)
                                    subgoal
                                      supply filter_True[simp] filter_False[simp] list_emb_Nil2[simp] BULK_BENQ_right_empty[simp] BULK_BENQ_left_empty[simp]
                                      apply (rule frontier_less_equal_sumI[where l=s])
                                      apply simp_all
                                      unfolding frontier_less_equal_iff
                                      apply (subst in_frontier_zmset_image)
                                      apply simp_all
                                      apply (subst change_multiplicities_extract_prog_consumes)
                                      apply simp_all
                                      apply (simp only: c_pts_change_multiplicities)
                                      apply (cases "l' = Loc nid (Trg p)"; simp)
                                      apply (drule in_frontier_in_frontier_add[where t=ft and B="zmset (map snd (filter (\<lambda>(l'a, t, d). l' = l'a) (concat (map (\<lambda>p'. map (\<lambda>t'. (Loc nid (Src p'), t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))"])
                                      subgoal
                                        by (clarsimp simp add: zcount_sum image_iff split_beta intro!: zcount_zmset_ge_0I)
                                      apply clarsimp
                                      subgoal for ft3
                                        apply (rule exI[of _ "ft3 -+- s"])
                                        apply simp
                                        apply (intro conjI)
                                        apply (metis (no_types, lifting) nat_arith.add1)
                                        apply (meson assms(1) basic_trans_rules(23) dataflow_topology.results_in_mono(1)) 
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        subgoal
                          by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                        subgoal
                          by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                        done
                      done
                    done

                  done
                done
              done
            done
          done
        done
      subgoal
        using E[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs" nid', unfolded changes_above_impl_inv_def] apply -
        apply simp
        apply (drule bspec)
        apply assumption
        apply auto
        done
      done
    done
  subgoal premises temp for xs
    using temp(1)
      conjunct1[OF temp(2)[unfolded produ_consu_inter_supported_def]]
      temp(3-) apply -
    using E[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs"] apply -
    apply simp
    apply (induct xs arbitrary: c os rule: rev_induct)
    subgoal for c os
      apply simp
      unfolding changes_above_impl_inv_def
      apply safe
      apply (drule set_extract_progress_consumesD)
      apply clarsimp
      apply (elim disjE conjE exE; simp?; hypsubst_thin?)
      apply fast
      subgoal
        apply (drule data_in_channel_justifies_c_pts[where nid=nid and t=t and p=p])
        apply assumption+
        subgoal
          unfolding BULK_BENQ_def
          by clarsimp
        subgoal
          unfolding change_deltas_inv_def by fastforce
        subgoal
          unfolding change_deltas_inv_def by fastforce
        apply (elim disjE)
        subgoal
          apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Trg p)", simplified])
          subgoal
            apply (rule graph.path_weight_refl)
            apply (rule dataflow_topology.axioms(1)[OF D])
            done
          subgoal
            by (metis frontier_less_equal_zcount_pos)
          done
        subgoal
          apply clarsimp
          apply (drule zcount_zmset_gt_0_set_Ex)
          apply clarsimp
          subgoal for nid' m' p'
            apply (drule meta_spec[of _ nid'])
            apply (drule bspec)
            apply (subst obtain_progress_def)
            apply (subst extract_progress_def)
            apply (clarsimp simp add: Misc.set_map_filter image_iff split_beta)
            apply fastforce
            apply simp
            done
          done
        done
      subgoal for a b _ p' s
        unfolding graph_summar_nt_def apply -
        apply clarsimp
        apply (drule spec2, drule spec2, drule mp, assumption)
        apply clarsimp
        subgoal for s'
          apply (drule data_in_channel_justifies_c_pts[where nid=nid and t=t and p=p])
          apply assumption+
          subgoal
            unfolding BULK_BENQ_def
            by clarsimp
          subgoal
            unfolding change_deltas_inv_def by fastforce
          subgoal
            unfolding change_deltas_inv_def by fastforce
          apply (elim disjE)
          subgoal
            apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, of s' "Loc nid (Trg p)" _ _ t])
            apply assumption
            apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Trg p)", simplified])
            subgoal
              apply (rule graph.path_weight_refl)
              apply (rule dataflow_topology.axioms(1)[OF D])
              done
            subgoal
              by (metis frontier_less_equal_zcount_pos)
            apply auto
            done
          subgoal
            apply clarsimp
            apply (drule zcount_zmset_gt_0_set_Ex)
            apply clarsimp
            subgoal for nid' m' p''
              apply (drule meta_spec[of _ nid'])
              apply (drule bspec)
              apply (subst obtain_progress_def)
              apply (subst extract_progress_def)
              apply (clarsimp simp add: Misc.set_map_filter image_iff split_beta)
              apply fastforce
              apply simp
              apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, of s' "Loc nid (Trg p)" _ _ t])
              apply assumption
              apply auto
              done
            done
          done
        done
      done
    subgoal premises prems for nid' xs c os
      supply filter_True[simp] filter_False[simp] list_emb_Nil2[simp] BULK_BENQ_right_empty[simp] BULK_BENQ_left_empty[simp]
      using prems(2-) apply -
      apply (auto 0 0)
      using prems(1) apply -
      apply simp
      apply (drule meta_spec[of _ "os( nid' := fst (obtain_progress (os nid')) )"])
      apply (drule meta_spec[of _ "change_multiplicities su (extract_prog [nid'] nt os) c"])
      apply (drule meta_mp)
      subgoal
        apply (auto del: disjCI)
        apply (drule spec2, drule spec, drule mp, rule exI, assumption)
        apply (clarsimp del: disjCI simp add: c_pts_change_multiplicities)
        apply (subst extract_progress_def)
        apply (simp add: filter_map comp_def split_beta )
        apply (subst filter_False)
        apply (auto simp add: Misc.set_map_filter split: option.splits)
        done
      apply (drule meta_mp)
      subgoal
        apply (subst extract_prog_obtain_progress_remove1)
        apply simp_all
        unfolding c_pts_inv_def
        apply clarsimp
        subgoal for l
          apply (drule spec[of _ l])
          apply (drule sym[of _ "caps l"])
          apply simp
          subgoal premises temp
            apply (subst (2) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid'])
            apply simp_all
            apply (auto simp add: change_multiplicities_append)
            done
          done
        done
      apply (drule meta_mp)
      subgoal
        unfolding Trg_caps_inv_def
        by auto
      apply (drule meta_mp)
      subgoal 
        unfolding graph_summar_nt_def obtain_progress_def
        by auto
      apply (drule meta_mp)
      subgoal
        unfolding change_deltas_inv_def obtain_progress_def
        by auto
      apply (drule meta_mp)
      subgoal
        apply (subst (2) extract_prog_def)
        apply (clarsimp simp add: change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid'])
        apply (metis change_multiplicities_append change_multiplicities_comm)
        done
      apply simp
      apply (subst change_multiplicities_comm)
      apply (simp add: change_multiplicities_append_alt )
      done
    done
  done

section \<open>Invariant Preservation under Consume\<close>

text \<open>The dataplane tracker invariant survives consuming data from a
  channel, for a single consume and for a fold over several.\<close>
lemma dataplane_tracker_inv_consumes:
  "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   cbufs (nid, p) = (d, t) # xs \<Longrightarrow>
   dataflow_topology (summ sg) (-+-) \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   dataplane_tracker_inv (os(nid := consumes (os nid) p (t :: 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) d)) (BTL (nid, p) cbufs) sg"
  supply if_cong[cong]
  unfolding dataplane_tracker_inv_def
  apply (elim conjE exE)
  apply simp
  apply hypsubst_thin
  subgoal for c c' cgs chns caps
    apply (rule exI[of _ 
          "(\<lambda> l. case l of 
        Loc nid' (Src p') \<Rightarrow> if nid' = nid then caps l + to_zmset (map (\<lambda> t'. t + t') (intsum (os nid) p p')) else caps l 
     | Loc nid' (Trg p') \<Rightarrow> if nid' = nid \<and> p = p' then caps l - {# t #}\<^sub>z else caps l)"])
    apply (intro conjI)
    subgoal premises prems
      using prems(4) apply -
      unfolding Src_caps_inv_def consumes_def add_caps_def to_zmset_correct
      apply (auto 0 0 simp add: filter_empty_conv)
      apply (auto 0 0 simp add:  comp_def  simp flip:  to_zmset_correct)
      subgoal premises prems2 for p''
        apply (simp flip: Multiset.mset_filter mset_map add: map_concat filter_concat comp_def)
        done
      done
    subgoal premises prems
      using prems(1,5) apply -
      unfolding Trg_caps_inv_def
      apply (auto simp add: map_tl BHD_def BTL_def BULK_BENQ_def)
      done
    subgoal premises prems
      using prems(6) apply -       
      unfolding c_pts_inv_def
      apply (auto 0 0 split: location.splits port.splits simp add:  filter_loc_extract_prof_consumes_diff_ports   change_multiplicities_extract_prog_extract_progress    zmset_concat map_concat filter_concat comp_def filter_map split_beta  c_pts_change_multiplicities)
      subgoal
        apply (subgoal_tac
            "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog Enum.enum (subgraph.nxt sg) (os(nid := consumes (os nid) p t d))))) =
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog Enum.enum (subgraph.nxt sg) os))) - {#t#}\<^sub>z")
        subgoal
          by auto
        subgoal premises
          apply (auto cong: if_cong simp add: if_distrib zmset_map_filter_Trg_extract_prog comp_def)
          apply (rule arg_cong2[where f=minus])
          apply (simp_all add: update_zmultiset_singleton(2))
          apply metis
          done
        done
      subgoal for nid'
        apply (drule spec[of _ "Loc nid (Src nid')"])
        apply (drule sym)
        apply simp
        subgoal premises
          apply (simp add: is_empty_antichain_plus dataflow_tree_to_graph_Src_Trg_zero  BHD_map BAPPEND_BENQ_BHD' change_multiplicities_extract_prog_extract_progress filter_loc_extract_prof_consumes_diff_ports is_empty_antichain_plus dataflow_tree_to_graph_Src_Trg_zero   filter_loc_Trg_extract_prof_consumes_diff_nids filter_loc_extract_prof_consumes_diff_ports   change_multiplicities_extract_prog_extract_progress    zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
          done
        done
      subgoal for nid' p'
        apply (drule spec[of _ "Loc nid' (Src p')"])
        apply (simp add: comp_def)
        done
      done
    subgoal premises prems
      using prems(7) unfolding front_inv_def by auto
    subgoal premises prems
      using prems(1,9) apply -
      unfolding chnls_imp_front_inv_def
      apply (simp_all add: BHD_def BTL_def BULK_BENQ_def)
      done
    subgoal premises prems
      using prems(10) apply -
      unfolding change_deltas_inv_def extract_prog_def consumes_def obtain_progress_def extract_progress_def
      apply (clarsimp simp add: split_beta split: prod.splits)
      done
    subgoal premises prems
      using prems apply -
      apply (rule extract_prog_changes_above_impl_inv_consumes)
      apply assumption+
      done
    subgoal premises prems
      using prems(13) apply -
      unfolding produ_consu_inter_supported_def
      apply (intro conjI)
      subgoal
        apply clarsimp
        apply blast
        done
      subgoal  
        apply (auto del: disjCI split: if_splits; hypsubst_thin?)
        subgoal
          using data_in_channel_justifies_c_pts_alt[where nid=nid and t=t and p=p,OF prems(5) prems(6)] apply -
          apply (drule meta_mp)
          subgoal
            using prems(1) unfolding BULK_BENQ_def
            by clarsimp
          apply (drule meta_mp)
          subgoal 
            using prems(10)[unfolded change_deltas_inv_def] by fastforce
          apply (drule meta_mp)
          subgoal using prems(10)[unfolded change_deltas_inv_def] by fastforce
          apply (drule meta_mp)
          subgoal
            using prems(3)[unfolded graph_summar_nt_def] by auto
          subgoal
            apply (auto simp add: consumes_def)
            apply (auto simp:if_distrib[of produ]  if_distrib[of inter] if_distrib[of consu] split: if_splits prod.splits cong: map_eq_conv)
            apply (smt (verit, ccfv_threshold) map_eq_conv prod.case_eq_if)
            done
          done
        subgoal
          apply (drule spec2, drule spec, drule mp, blast)
          apply (smt (verit) map_eq_conv produ_consumes split_def)
          done
        subgoal
          apply (drule spec2, drule spec, drule mp, blast)
          apply (smt (verit) map_eq_conv produ_consumes split_def)
          done
        done
      subgoal
        apply clarsimp
        apply (auto del: disjCI simp add: consumes_def)
        subgoal for p' t' m
          apply (drule spec2, drule spec, drule mp, blast)
          apply (elim disjE exE)
          subgoal for t''
            subgoal
              apply (subgoal_tac "zcount (zmset (map snd (filter (\<lambda>(p'a, _, _). p'a = p') (concat (map (\<lambda>p'. map (\<lambda>t'. (p', t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))) t'' \<ge> 0")
              subgoal
                by auto
              subgoal
                by (auto simp add: image_iff intro!: zcount_zmset_ge_0I)
              done
            done
          subgoal
            by blast
          done
        using zero_less_one apply blast
        done
      done
    done
  done

lemma dataplane_tracker_inv_fold_consumes:
  "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   dataflow_topology (summ sg) (-+-) \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   n \<le> length (cbufs (nid, p)) \<Longrightarrow>
   buf' = (\<lambda> (nid', p'). if nid' = nid \<and> p' = p then drop n (cbufs (nid, p)) else cbufs (nid', p')) \<Longrightarrow>
   os' = (os(nid := fold (\<lambda>(d, t) os. consumes os p t d) (take n (cbufs (nid, p))) (os nid))) \<Longrightarrow>
   dataplane_tracker_inv os' buf' sg"
  apply (induct n arbitrary: cbufs os buf' os')
  subgoal
    apply simp
    apply (smt (verit, ccfv_threshold) cond_case_prod_eta drop0)
    done
  subgoal premises prems for n cbufs os buf' os'
    using prems(2-) apply -
    apply hypsubst_thin
    apply (cases "cbufs (nid, p)")
    subgoal
      by simp
    subgoal for a xs
      apply (cases a)
      apply simp
      apply hypsubst_thin
      apply (rule prems(1))
      apply (rule dataplane_tracker_inv_consumes)
      apply assumption+
      apply (simp_all add: BTL_def)
      subgoal
        unfolding graph_summar_nt_def
        by auto
      subgoal
        by (auto simp add: BTL_def)
      done
    done
  done

end
