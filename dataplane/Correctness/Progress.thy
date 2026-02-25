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


lemma sorried:
  "finite S \<Longrightarrow>
   S \<noteq> {} \<Longrightarrow>
   frontier (\<Sum>loc\<in>S. f loc) \<le> x \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   (\<exists> s \<in> S. frontier (f s) \<le> x)"
  apply (cases "x = {}\<^sub>A")
   apply simp
  apply blast
  apply (induct S rule: finite_induct)
   apply simp_all
  subgoal
    apply auto
  unfolding less_eq_antichain_def
  apply auto
  apply transfer
  apply (auto simp add: minimal_antichain_def)
  oops

lemma frontier_less_equal_le_frontier_alt:
  "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (f l) t) \<Longrightarrow>
   (\<exists> (l, t, m) \<in> set A. f l \<le> frontier (zmset (map snd (filter (\<lambda>(l', t, d). l = l') A))))"
  apply (induct A rule: rev_induct)
   apply simp
  oops

lemma frontier_less_equal_le_frontier:
  "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (f l) t) \<Longrightarrow>
   f l \<le> frontier (zmset (map snd A))"
  apply (induct A rule: rev_induct)
   apply simp
  apply (clarsimp split: prod.splits)
  oops


lemma frontier_less_equal_le_frontier:
  "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (f l) t) \<Longrightarrow>
   f l \<le> frontier (zmset (map snd (filter (\<lambda>(l', t, d). loc' = l') A)))"
  oops

lemma frontier_less_equal_frontier_sum_iff:
  "finite A \<Longrightarrow>
   (\<forall> a\<in>A. \<forall> t. zcount (f a) t \<ge> 0) \<Longrightarrow>
   frontier_less_equal (frontier (sum f A)) t \<longleftrightarrow> (\<exists>a\<in>A. frontier_less_equal (frontier (f a)) t)"
  apply (rule iffI)
  subgoal
    apply (induct A rule: finite_induct)
     apply simp_all
    using frontier_less_equal_add_cases apply blast
    done
  subgoal
    apply clarsimp
    subgoal for a
    apply (induct A rule: finite_induct)
     apply simp_all
      apply (auto simp add: frontier_less_equal_addI sum_nonneg zcount_sum)
      done
    done
  done




lemma frontier_less_equal_le_frontier:
  "(\<forall> (l, t, m) \<in> set A. f l \<le> frontier (zmset (map snd (filter (\<lambda>(l', t, d). l = l') A)))) \<Longrightarrow>
   (\<forall> (l, t, m) \<in> set A. frontier_less_equal (f l) t)"
  apply clarsimp
  subgoal for l t m
    apply (drule bspec)
     apply assumption
    apply simp
    subgoal
      apply (induct A rule: rev_induct)
       apply simp_all
      apply auto
      subgoal
        oops


lemma frontier_less_equal_change_multiplicities:
  assumes D: "dataflow_topology su (-+-)"
  shows 
  "(\<forall> (l, t, m) \<in> set A. frontier_less_equal (ifrontier su (+) c l) t \<and> m \<ge> 0)  \<Longrightarrow>
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
        using prems2(2-) apply -
        apply (drule frontier_less_equal_ifrontierE)
        using D apply assumption
        apply clarsimp
        subgoal for l3 s' t'
          apply hypsubst_thin
             unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D]
             apply (clarsimp simp add: c_pts_change_multiplicities comp_def)
             apply (subst (1) comm_monoid_add_class.sum.subset_diff[where B="{l2,l3}"])
             apply simp_all
             apply (subst (3) comm_monoid_add_class.sum.subset_diff[where B="{l2,l3}"])
               apply auto
             subgoal
               apply (rule frontier_add_add_le)
                  apply (simp_all add: zcount_sum sum_nonneg)
               subgoal
                 apply (cases "l3 = l2")
                 subgoal
                   apply simp
                 apply (rule frontier_sum_le)
                     apply simp_all
                   apply clarsimp
 apply (rule frontier_le_image)
                     apply simp_all
     apply (smt (verit, ccfv_threshold) Timely_Infrastructure.update_zmultiset_plus add.commute add_cancel_right_right dataflow_topology_from_tree.obtain_elem_frontier dataflow_topology_from_tree.result_in_geq
                     frontier_less_equal_iff2 le_add_same_cancel1 less_eq_antichain_def member_frontier_pos_zmset zcount_update_zmultiset zero_compare_simps(3))
                   done
                 subgoal
                   apply simp
                   apply (cases "frontier_less_equal (frontier (c_pts c l2)) t'")
                   subgoal
                   apply (rule frontier_add_le_gen)
                  apply (simp_all add: zcount_sum sum_nonneg)
                    apply (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg frontier_le_remove_left verit_comp_simplify(2))
       apply (rule frontier_sum_le)
                     apply simp_all
                   apply clarsimp
                   apply (rule frontier_le_image)
                   apply simp_all
                   apply (rule frontier_below_eq_frontier_plus_frontier_below_eq_frontier_plus)
                     apply (smt (verit, del_insts) add.commute dataflow_topology_from_tree.result_in_geq frontier_less_equal_iff2 le_add_same_cancel1 less_eq_antichain_def member_frontier_pos_zmset zcount_empty zcount_update_zmultiset
                         zero_compare_simps(3))
                     done
                   subgoal



                   find_theorems "_ \<le> frontier (_ + _)"



                 apply (subst (1) comm_monoid_add_class.sum.subset_diff[where B="{l2}"])
                 apply simp_all


end
                 apply (rule frontier_sum_le)
                   apply simp_all
                 apply clarsimp
                 apply (rule frontier_le_image)
                   apply simp_all
                 apply (smt (verit, ccfv_threshold) Timely_Infrastructure.update_zmultiset_plus add.commute add_cancel_right_right dataflow_topology_from_tree.obtain_elem_frontier dataflow_topology_from_tree.result_in_geq
                     frontier_less_equal_iff2 le_add_same_cancel1 less_eq_antichain_def member_frontier_pos_zmset zcount_update_zmultiset zero_compare_simps(3))
                 done
               subgoal
                 by (clarsimp simp add: zcount_sum sum_nonneg)
                    subgoal
                 by (clarsimp simp add: zcount_sum sum_nonneg)
               done
             subgoal
               apply (rule frontier_add_add_le)
                  apply (simp_all add: zcount_sum sum_nonneg)
               subgoal


             find_theorems "frontier (_ + _) \<le> _"

end
             apply (subst (1 2) filter.simps(1))
             apply (cases "\<exists>s. s \<in>\<^sub>A graph.path_weight su l2 l")
             subgoal
               apply clarsimp 
               subgoal for s''

                 find_theorems "sum _ _ = sum _ (_ - _) + _"

end
                 apply (rule frontier_sum_le_one[of _ l3])
                    apply simp_all
                 subgoal
                   apply (drule Graph.graph.path_weight_elem_trans[rotated])
                     apply assumption
                   subgoal
                     apply (rule dataflow_topology.axioms(1))
                     using D apply assumption
                     done
                   apply clarsimp
                   subgoal for u
                     apply (rule frontier_sum_le_one[of _ u])
                        apply simp_all
                     using member_antichain.rep_eq apply blast 


                   find_theorems frontier "_ \<le> _" image_zmset

             thm frontier_sum_le_one
             thm frontier_sum_le

             thm frontier_sum_le_one

                find_theorems filter Nil

end
                apply (cases "l2 = l")
                subgoal
                  apply simp
                  apply hypsubst_thin
                  apply (rule frontier_sum_le)
                    apply simp_all
                  subgoal
                    apply (rule frontier_sum_le)
                      apply simp_all
                    apply clarsimp
                    subgoal for s'



end
            apply (rule frontier_sum_le_one[of _ l])
              apply simp_all
                  subgoal


                    find_theorems name: frontier_sum_le


            apply (rule ifrontier_le_all_le[OF D])
        apply auto

            apply (rule frontier_below_eq_frontier_plus_frontier_below_eq_frontier_plus)


            find_theorems t


          find_theorems "frontier _ \<le> frontier (sum _ _)"


   apply assumption


      find_theorems change_multiplicities append


    oops




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

        using prems(11)

end
      sorry
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