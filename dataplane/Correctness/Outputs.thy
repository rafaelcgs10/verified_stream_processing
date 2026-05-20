theory Outputs

imports
  General
  Dataplane.Timely_Stream
  Dataplane.MyProduct_Instances
  Dataplane.AntichainOrder
begin

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]


lemma dataplane_tracker_inv_update_outputs_outside:
  "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   os' = os(nid := (os nid)\<lparr> outpu := (\<lambda> p'. if p' = p then xs else outpu (os nid) p') \<rparr>) \<Longrightarrow>
   (\<forall> l. summ sg (Loc nid (Src p)) l = {}\<^sub>A) \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   dataplane_tracker_inv os' cbufs sg"
  unfolding dataplane_tracker_inv_def
  apply clarsimp
  apply hypsubst_thin
  subgoal for caps
    apply (rule exI[of _ caps])
    apply (intro conjI)                                         
    subgoal premises prems
      using prems(3) apply -
      unfolding Src_caps_inv_def
      apply auto
      done
    subgoal premises prems
      using prems(1,4) apply -
      unfolding Trg_caps_inv_def outputs_at_target_def
      apply clarsimp
      apply (rule arg_cong[where f=to_zmset])
      apply (rule map_cong)
      unfolding BULK_BENQ_def
       apply (auto split: prod.splits)
      subgoal for nid' p' nid'' p''
        apply (cases "nid'' = nid \<and> p'' = p")
        subgoal
          by auto
        subgoal
          apply (rule FalseE)
          apply auto
          using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(2)[unfolded graph_summar_nt_def]]]]]]]]
            the_elem_bi_unique_op_conn apply fastforce+
          done
        done
      done
    subgoal premises prems
      using prems(5) apply -
      unfolding c_pts_inv_def extract_prog_def obtain_progress_def
      apply auto
      subgoal for l
        apply (drule spec[of _ l])
        apply (drule sym)
        apply simp
        subgoal premises temp
          apply (simp add:  c_pts_change_multiplicities)
          apply (rule arg_cong[where f=zmset])
          apply (rule map_cong)
           apply (rule filter_cong)
            apply (rule arg_cong[where f=concat])
            apply (rule map_cong)
             apply auto
          done
        done
      done
    subgoal premises prems
      using prems(6) apply -
      unfolding front_inv_def
      apply auto
      done
    subgoal premises prems
      using prems(1,8) apply -
      unfolding chnls_imp_front_inv_def outputs_at_target_def BULK_BENQ_def
      apply (auto simp add: image_iff split_beta split:  if_splits cong: if_cong)
      apply (rule FalseE)
      using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(2)[unfolded graph_summar_nt_def]]]]]]]]
        the_elem_bi_unique_op_conn
        prod.split_sels(2)
      apply (smt (verit, ccfv_SIG) Collect_cong case_prod_beta prod.exhaust_sel)
      done
    subgoal premises prems
      using prems(9) apply -
      unfolding change_deltas_inv_def
      apply auto
      done
    subgoal premises prems
      using prems(11) apply -
      unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def 
      apply (auto simp add: image_iff split_beta split:  if_splits)
      subgoal for xs a b c
        apply (drule spec2)
        apply (drule mp)
         apply assumption
        apply (drule mp)
         apply assumption
        apply (drule bspec)
        unfolding extract_progress_def obtain_progress_def
         apply simp
        apply auto
        done
      subgoal for xs' a b c
        apply (drule spec2)
        apply (drule mp)
         apply assumption
        apply (drule mp)
         apply assumption
        apply (drule bspec)
        unfolding extract_progress_def obtain_progress_def
         apply simp
        apply clarsimp
        apply (subgoal_tac "extract_prog a (subgraph.nxt sg) (map_entry nid (outpu_update (\<lambda>_ p'. if p' = p then xs else outpu (os nid) p')) os) = extract_prog a (subgraph.nxt sg) os")
        subgoal
          by auto
        subgoal premises temp
          unfolding extract_prog_def extract_progress_def obtain_progress_def
          apply clarsimp
          apply (rule arg_cong[where f=concat])
          apply (rule map_cong)
           apply auto
          done
        done
      done
    subgoal premises prems
      using prems(12) apply -
      unfolding produ_consu_inter_supported_def
      apply (auto simp add: map_concat image_iff split_beta if_distrib[of produ] if_distrib[of filter] split:  if_splits)
      subgoal for p'' t m
        apply (drule spec2, drule spec, drule mp, blast)
        apply (subgoal_tac "map (\<lambda>(nid', p'). map snd (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid', p''a) = Some (nid, p'') \<and> p' = p''a) (if nid' = nid then produ (os nid\<lparr>outpu := \<lambda>p'. if p' = p then xs else outpu (os nid) p'\<rparr>) else produ (os nid'))))
               enum_class.enum = map (\<lambda>(nid', p'). map snd (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid', p''a) = Some (nid, p'') \<and> p' = p''a) (produ (os nid')))) enum_class.enum")
        subgoal
          by auto
        subgoal premises temp
          apply (rule map_cong)
           apply auto
          done
        done
      subgoal for p'' t m
        apply (drule spec2, drule spec, drule mp, blast)
        apply (subgoal_tac "map (\<lambda>(nid', p'). map snd (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid', p''a) = Some (p'', t) \<and> p' = p''a) (if nid' = nid then produ (os nid\<lparr>outpu := \<lambda>p'. if p' = p then xs else outpu (os nid) p'\<rparr>) else produ (os nid'))))
               enum_class.enum = map (\<lambda>(nid', p'). map snd (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid', p''a) = Some (p'', t) \<and> p' = p''a) (produ (os nid')))) enum_class.enum")
        subgoal
          by auto
        subgoal premises temp
          apply (rule map_cong)
           apply auto
          done
        done
      done
    done
  done

lemma the_elem_graph_summar_nt_summ:
  "the_elem {(nid'a, p'a). summ sg (Loc nid'a (Src p'a)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A} = (nid, p) \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   summ sg (Loc nid'' (Src p'')) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A \<Longrightarrow>
   nid'' = nid \<and> p'' = p"
  subgoal premises prems
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(2)[unfolded graph_summar_nt_def]]]]]]]]
      the_elem_bi_unique_op_conn
      prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
      prems(1,3) by fastforce
  done


lemma dataplane_tracker_inv_update_outputs:
  "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   outpu (os nid) p = xs @ ys \<Longrightarrow>
   os' = os(nid := (os nid)\<lparr> outpu := (\<lambda> p'. if p' = p then ys else outpu (os nid) p') \<rparr>) \<Longrightarrow>
   cbufs'  = cbufs((nid', p') := cbufs (nid', p') @ xs)  \<Longrightarrow>
   summ sg (Loc nid (Src p)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   dataplane_tracker_inv os' cbufs' sg"
  unfolding dataplane_tracker_inv_def
  apply clarsimp
  apply hypsubst_thin
  subgoal for caps
    apply (rule exI[of _ caps])
    apply (intro conjI)
    subgoal premises prems
      using prems(4) apply -
      unfolding Src_caps_inv_def
      apply auto
      done
    subgoal premises prems
      using prems(2,1,5) apply -
      unfolding Trg_caps_inv_def outputs_at_target_def
      apply clarsimp
      apply (rule arg_cong[where f=to_zmset])
      apply (rule map_cong)
       apply simp_all
      unfolding BULK_BENQ_def
      apply (auto 0 0 split: prod.splits cong: if_cong)
      subgoal 
        apply (drule the_elem_graph_summar_nt_summ[OF _ prems(3)])
         back
         apply assumption
        apply clarsimp
        apply (rule FalseE)
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
          the_elem_bi_unique_op_conn
          prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
        apply fastforce
        done
      subgoal 
        apply (drule the_elem_graph_summar_nt_summ[OF _ prems(3)])
         back
         apply assumption
        apply clarsimp
        apply (rule FalseE)
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
          the_elem_bi_unique_op_conn
          prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
        apply fastforce
        done
      subgoal 
        apply (drule the_elem_graph_summar_nt_summ[OF _ prems(3)])
         back
         apply assumption
        apply clarsimp
        apply (rule FalseE)
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
          the_elem_bi_unique_op_conn
          prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
        apply fastforce
        done
      subgoal 
        apply (drule the_elem_graph_summar_nt_summ[OF _ prems(3)])
         back
         apply assumption
        apply clarsimp
        apply (rule FalseE)
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
          the_elem_bi_unique_op_conn
          prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
        by fastforce
      subgoal 
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
          the_elem_bi_unique_op_conn
          prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
        by fastforce
      subgoal 
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
          the_elem_bi_unique_op_conn
          prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
        by fastforce
      subgoal 
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
          the_elem_bi_unique_op_conn
          prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
        by fastforce
      subgoal 
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
          the_elem_bi_unique_op_conn
          prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
        by fastforce
      done

    subgoal premises prems
      using prems(6) apply -
      unfolding c_pts_inv_def extract_prog_def obtain_progress_def
      apply auto
      subgoal for l
        apply (drule spec[of _ l])
        apply (drule sym)
        apply simp
        subgoal premises temp
          apply (simp add:  c_pts_change_multiplicities)
          apply (rule arg_cong[where f=zmset])
          apply (rule map_cong)
           apply (rule filter_cong)
            apply (rule arg_cong[where f=concat])
            apply (rule map_cong)
             apply auto
          done
        done
      done
    subgoal premises prems
      using prems(7) apply -
      unfolding front_inv_def
      apply auto
      done
    subgoal premises prems
      using prems(9) apply -
      apply (subgoal_tac "outputs_at_target (summ sg) (map_entry nid (outpu_update (\<lambda>_ p'. if p' = p then ys else outpu (os nid) p')) os) >> cbufs((nid', p') := cbufs (nid', p') @ xs) = outputs_at_target (summ sg) os >> cbufs")
      subgoal
        by auto
      subgoal
        using prems(1,2) apply -
        unfolding chnls_imp_front_inv_def outputs_at_target_def BULK_BENQ_def apply -
        apply (auto del: prod_eqI simp add: image_iff split_beta split:  if_splits)
        apply (rule ext)+
        subgoal premises aux for nidp
          using aux(2-) apply -
          apply (subgoal_tac "the_elem {(nid'a, p'a). summ sg (Loc nid'a (Src p'a)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A} = (nid, p)")
          subgoal
            apply (cases "nidp = (nid', p')")
            subgoal
              apply (simp split: if_splits)
              apply (auto 0 0 del: prod_eqI simp add: image_iff split: if_splits)
              done
            subgoal
              apply (cases "nidp")
              subgoal for nid'' p''
                using aux(1)[rule_format, of nid'' p''] apply -
                apply (simp split: if_splits prod.splits)
                apply (auto 0 0 del: disjCI prod_eqI simp add: image_iff split: if_splits; hypsubst_thin)
                subgoal
                  using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
                    the_elem_bi_unique_op_conn
                    prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
                  by (smt (verit, best) Collect_cong split_def split_pairs2 the_elem_graph_summar_nt_summ)
                subgoal
                  using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
                    the_elem_bi_unique_op_conn
                    prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
                  by (smt (verit, best) Collect_cong split_def split_pairs2 the_elem_graph_summar_nt_summ)
                subgoal
                  using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
                    the_elem_bi_unique_op_conn
                    prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
                  by (smt (verit, best) Collect_cong split_def split_pairs2 the_elem_graph_summar_nt_summ)
                subgoal
                  using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
                    the_elem_bi_unique_op_conn
                    prod.split_sels(2) Pair_inject bi_uniqueDr op_conn.simps
                  by (smt (verit, best) Collect_cong split_def split_pairs2 the_elem_graph_summar_nt_summ)
                done
              done
            done
          subgoal
            using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF prems(3)[unfolded graph_summar_nt_def]]]]]]]]
            by (smt (verit, ccfv_SIG) Collect_cong op_conn.elims(1) prems(3) split_beta the_elem_graph_summar_nt_summ)
          done
        done
      done
    subgoal premises prems
      using prems(10) apply -
      unfolding change_deltas_inv_def
      apply auto
      done
    subgoal premises prems
      using prems(12) apply -
      unfolding extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def
      apply (auto simp add: image_iff split_beta split:  if_splits)
      subgoal for xs 
        apply (drule spec2)
        apply (drule mp)
         apply assumption
        apply (drule mp)
         apply assumption
        apply (drule bspec)
        unfolding extract_progress_def obtain_progress_def
         apply simp
        apply auto
        done
      subgoal for xs' a b c
        apply (drule spec2)
        apply (drule mp)
         apply assumption
        apply (drule mp)
         apply assumption
        apply (drule bspec)
        unfolding extract_progress_def obtain_progress_def
         apply simp
        apply clarsimp
        apply (subgoal_tac "extract_prog a (subgraph.nxt sg) (map_entry nid (outpu_update (\<lambda>_ p'. if p' = p then ys else outpu (os nid) p')) os) = extract_prog a (subgraph.nxt sg) os")
        subgoal
          by auto
        subgoal premises temp
          unfolding extract_prog_def extract_progress_def obtain_progress_def
          apply clarsimp
          apply (rule arg_cong[where f=concat])
          apply (rule map_cong)
           apply auto
          done
        done
      done
    subgoal premises prems
      using prems(13) apply -
      unfolding produ_consu_inter_supported_def
      apply (auto simp add: map_concat image_iff split_beta if_distrib[of produ] if_distrib[of filter] split:  if_splits)
      subgoal for p'' t'' m
        apply (drule spec2, drule spec, drule mp, blast)
        apply (subgoal_tac "
             (map (\<lambda>(nid', p').
                      map snd
                       (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid', p''a) = Some (nid, p'') \<and> p' = p''a)
                         (if nid' = nid then produ (os nid\<lparr>outpu := \<lambda>p'. if p' = p then ys else outpu (os nid) p'\<rparr>) else produ (os nid'))))
               enum_class.enum) = (map (\<lambda>(nid', p'). map snd (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid', p''a) = Some (nid, p'') \<and> p' = p''a) (produ (os nid')))) enum_class.enum)")
        subgoal
          by auto
        subgoal premises temp
          apply (rule map_cong)
           apply auto
          done
        done
      subgoal for nid'' p'' t'' m
        apply (drule spec2, drule spec, drule mp, blast)
        apply (subgoal_tac "map (\<lambda>(nid', p').
                      map snd
                       (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid', p''a) = Some (nid'', p'') \<and> p' = p''a)
                         (if nid' = nid then produ (os nid\<lparr>outpu := \<lambda>p'. if p' = p then ys else outpu (os nid) p'\<rparr>) else produ (os nid'))))
               enum_class.enum = map (\<lambda>(nid', p'). map snd (filter (\<lambda>(p''a, ab). subgraph.nxt sg (nid', p''a) = Some (nid'', p'') \<and> p' = p''a) (produ (os nid')))) enum_class.enum")
        subgoal
          by auto
        subgoal premises temp
          apply (rule map_cong)
           apply auto
          done
        done
      done
    done
  done

end