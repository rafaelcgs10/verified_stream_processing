theory Produces

imports
  General
  Dataplane.Timely_Stream
  Dataplane.MyProduct_Instances
  Dataplane.AntichainOrder
begin

declare cin.rep_eq[simp del]
declare enum_class.enum_UNIV[simp] enum_class.enum_distinct[simp]
no_notation shiftr  (infixl \<open>>>\<close> 55)


find_theorems filter zmset

(*
   (\<forall> p. to_zmset (drops p) \<subseteq>#\<^sub>z zmset (map snd (filter (\<lambda>x. p = fst x) produs))) \<Longrightarrow>
*)

(* FIXME: move me *)
lemma to_zmset_list_diff[simp]:
  "mset ys \<subseteq># mset xs \<Longrightarrow>
   to_zmset (list_diff xs ys) = to_zmset xs - to_zmset ys"
  apply (induct xs ys rule: list_diff.induct)
   apply clarsimp+
  apply (metis add_zmset_diff_bothsides insert_DiffM insert_subset_eq_iff mset_remove_last to_zmset_correct zmset_of_add_mset)
  done

lemma outputs_at_target_updates[simp]:
  "outputs_at_target su (os(nid := (os nid)\<lparr> inter := A, nfron := F, produ := B, ocaps := C, input := D, inter := E  \<rparr>)) = outputs_at_target su os"
  unfolding outputs_at_target_def
  apply (rule ext)
  apply (auto split: prod.splits if_splits)
  done


lemma to_zmset_BULK_BENQ[simp]:
  "to_zmset ((xs >> ys) p) = to_zmset (xs p) + to_zmset (ys p)"
  unfolding BULK_BENQ_def
  by auto

lemma find_Some_singleton:
  "{x \<in> set xs . P x} = {x} \<Longrightarrow>
   find P xs = Some x"
  apply (induct xs)
   apply simp_all
  apply (auto 0 0 simp add:)
   apply blast
  apply (smt (verit, best) Collect_cong)
  done

lemma eq_singletonD:
  "{x. P x} = {x} \<Longrightarrow> P x"
  by auto

lemma in_op_conn_graph_to_nxt_iff:
  "bi_unique (op_conn su) \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid', p') \<longleftrightarrow> op_conn su (nid, p) (nid', p')"
  unfolding graph_to_nxt_def
  apply (auto simp add: is_empty_antichain_iff split: prod.splits)
  subgoal
    apply (auto simp add: dest!: find_SomeD' split: prod.splits)
    done
  subgoal
    apply (rule find_Some_singleton)
    apply (auto simp add: bi_unique_def split: prod.splits)
    done
  done

lemma graph_to_nxt_not_Ex_op_conn[simp]:
  "graph_to_nxt su (nid, p) = None \<longleftrightarrow>
   \<not> (\<exists> nid' p'. op_conn su (nid, p) (nid', p'))"
  unfolding graph_to_nxt_def
  apply (auto simp add: is_empty_antichain_iff find_None_iff dest!: find_SomeD' split: prod.splits)
  done

lemma the_elem_bi_unique_op_conn:
  "the_elem {(nid', p'). su (Loc nid' (Src p')) (Loc nid (Trg p)) \<noteq> {}\<^sub>A} = (nid', p') \<Longrightarrow>
   su (Loc nid'' (Src p'')) (Loc nid (Trg p)) \<noteq> {}\<^sub>A \<Longrightarrow>
   bi_unique (op_conn su) \<Longrightarrow>
   nid' = nid'' \<and> p' = p''"
  apply (subst (asm) the_elem_image_unique[where f=id, simplified, of _  "(nid'', p'')"])
    apply blast
  unfolding bi_unique_def
   apply auto
  done


lemma outputs_at_target_outpu_if:
  "bi_unique (op_conn su) \<Longrightarrow>
   os' = os(nid := (os nid)\<lparr> outpu := X \<rparr>) \<Longrightarrow>
   outputs_at_target su os' (nid', p') = 
  (let S = {p. op_conn su (nid, p) (nid', p')} in if S \<noteq> {} then let p = the_elem S in X p else outputs_at_target su os (nid', p'))"
  unfolding outputs_at_target_def
  apply (auto split: prod.splits)
  subgoal
    apply (drule the_elem_bi_unique_op_conn)
      apply assumption+
    apply auto
    done
  subgoal for x2 a b x
    apply (subst the_elem_image_unique[where f=id, simplified, of _ "b"])
      apply fast
    unfolding bi_unique_def
     apply auto
    apply (subst (asm) the_elem_image_unique[where f=id, simplified, of _  "(a, b)"])
      apply blast
     apply auto
    done
  subgoal for x2 a b x
    apply (subst the_elem_image_unique[where f=id, simplified, of _ "x"])
      apply fast
    unfolding bi_unique_def
     apply auto
    apply (subst (asm) the_elem_image_unique[where f=id, simplified, of _  "(_, x)"])
      apply blast
     apply auto
    done
  done

lemma dataplane_tracker_inv_produces_drops:
  fixes drops :: "'p :: {enum,linorder} \<Rightarrow> 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} list"
  assumes D: "dataflow_topology (summ sg) (-+-)"
  shows
    "noutput = (\<lambda> p . outpu (os nid) p @ oputs p) \<Longrightarrow>
   nocaps = (\<lambda> p . list_diff (ocaps (os nid) p) (drops p)) \<Longrightarrow>
   ninput = (\<lambda> p. filter (\<lambda> (_, t). t \<notin> set (drops p)) (input (os nid) p)) \<Longrightarrow> 
   nprodu = produ (os nid) @ produs \<Longrightarrow>
   ninter = operator_state.inter (os nid) @ concat (map (\<lambda> p. map (\<lambda>os. (p, os, - 1)) (drops p)) Enum.enum) \<Longrightarrow>
   (\<forall> p. mset (drops p) \<subseteq># mset (ocaps (os nid) p)) \<Longrightarrow>
   (\<forall> (p, t, m) \<in> set produs. m > 0 \<and> t \<in> set (ocaps (os nid) p)) \<Longrightarrow>
   (\<forall> p. snd ` set (oputs p) \<subseteq> set (ocaps (os nid) p)) \<Longrightarrow>
   (\<forall> p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))) \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   nxt sg = graph_to_nxt (summ sg) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   dataplane_tracker_inv (os(nid := os nid \<lparr>outpu := noutput, ocaps := nocaps, input := ninput, produ := nprodu, inter := ninter, nfron := V\<rparr>)) cbufs sg"
  unfolding dataplane_tracker_inv_def
  apply (elim conjE exE)
  apply simp
  apply hypsubst_thin
  subgoal premises temp for c c' cgs chns caps
    using temp(5)[unfolded graph_summar_nt_def] apply -
    apply clarsimp
    subgoal premises GS
      using temp(1,2,3,4,6-) apply-
      apply (rule exI[of _ 
            "(\<lambda> l. case l of 
       Loc nid' (Src p') \<Rightarrow> if nid' = nid then caps l - to_zmset (drops p') else caps l 
     | Loc nid' (Trg p') \<Rightarrow> caps l + zmset (map snd (filter (\<lambda> (p'', _, _). (graph_to_nxt (summ sg)) (nid, p'') = Some (nid', p')) produs)))"])
      apply (intro conjI)
      subgoal premises prems
        using prems(6)
        unfolding Src_caps_inv_def
        by (auto simp add: temp(1))
      subgoal premises prems
        using prems(7,8) apply -
        unfolding Trg_caps_inv_def
        apply (clarsimp simp add: to_zmset_map)
        subgoal for nid' p'
          apply (drule spec[of _ nid'])
          apply (drule spec[of _ p'])
          unfolding c_pts_inv_def
          apply (drule spec[of _ "Loc nid' (Trg p')"])
          apply (drule sym)
          back
          apply simp
          apply (auto simp add: in_op_conn_graph_to_nxt_iff[OF GS(7)] outputs_at_target_def split: prod.splits if_splits)
          subgoal for nid'' p''' p''
            apply (subst temp(4)[rule_format, of p''', unfolded to_zmset_map, simplified])
            apply (rule arg_cong[where f=zmset])
            apply (rule map_cong)
            subgoal
              apply (rule filter_cong)
               apply (auto split: prod.splits simp add: )
              subgoal
                apply (drule conjunct2[OF GS(7)[unfolded bi_unique_def, simplified, rule_format], rule_format])
                 apply assumption
                apply auto
                apply hypsubst_thin
                apply (subst (asm) the_elem_image_unique[where f=id, simplified])
                  apply blast
                 apply clarsimp
                 apply (drule conjunct2[OF GS(7)[unfolded bi_unique_def, simplified, rule_format], rule_format])              
                  apply auto
                done
              subgoal
                apply (subst (asm) the_elem_image_unique[where f=id, simplified])
                  apply blast
                 apply clarsimp
                 apply (drule conjunct2[OF GS(7)[unfolded bi_unique_def, simplified, rule_format], rule_format])
                  apply auto
                done
              done
            apply simp
            done
          subgoal
            apply (subst filter_False)
             apply simp_all
            subgoal
              apply (auto split: prod.splits simp add: )
              apply (subst (asm) the_elem_image_unique[where f=id, simplified])
                apply blast
               apply clarsimp
              using conjunct2[OF GS(7)[unfolded bi_unique_def, simplified, rule_format], rule_format] apply blast+
              done
            done
          done
        done
      subgoal premises prems
        using prems(8) apply -
        unfolding c_pts_inv_def
        apply safe
        subgoal for l
          apply (drule spec[of _ l])
          apply (drule sym)
          apply (auto simp add: extract_prog_def  c_pts_change_multiplicities split: location.splits port.splits; hypsubst_thin)
          subgoal premises aux for nid' p'
            apply (simp add: filter_map monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat filter_concat map_concat comp_def)
            apply (subst (1 2) comm_monoid_add_class.sum.subset_diff[where B="{nid}"])
              apply simp_all
            unfolding extract_progress_def obtain_progress_def
            apply (simp add: List.map_filter_def split_beta filter_map monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat filter_concat map_concat comp_def split: option.splits)
            apply (rule arg_cong[where f=zmset])
            apply (rule map_cong)
             apply simp_all
             apply (rule filter_cong)
              apply (auto simp add: in_op_conn_graph_to_nxt_iff[OF GS(7)] split: prod.splits option.splits dest: conjunct1[OF GS(7)[unfolded bi_unique_def, simplified, rule_format], rule_format])
            done
          subgoal premises aux for nid'
            apply (simp add: filter_map monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat filter_concat map_concat comp_def)
            apply (subst (1 2) comm_monoid_add_class.sum.subset_diff[where B="{nid}"])
              apply simp_all
            unfolding extract_progress_def obtain_progress_def
            apply (simp add: to_zmset_filter List.map_filter_def split_beta filter_map monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat filter_concat map_concat comp_def split: option.splits)
            apply (subst comm_monoid_add_class.sum.subset_diff[where B="{nid'}"])
              apply auto
            done
          subgoal for nid' p'
            apply (simp add: filter_map monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat filter_concat map_concat comp_def)
            apply (subst (1 2) comm_monoid_add_class.sum.subset_diff[where B="{nid}"])
              apply simp_all
            unfolding extract_progress_def obtain_progress_def
            apply (simp add: to_zmset_filter List.map_filter_def split_beta filter_map monoid_add_class.sum_list_distinct_conv_sum_set zmset_concat filter_concat map_concat comp_def split: option.splits)
            done
          done
        done
      subgoal premises prems
        using prems(9) apply -
        unfolding front_inv_def
        apply simp
        done
      subgoal premises prems
        apply (subgoal_tac "(\<forall> p nid' p'. \<forall> t \<in> snd ` set (oputs p). summ sg (Loc nid (Src p)) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A \<longrightarrow> frontier_less_equal (ifrontier (summ sg) (+) (pt_tr sg) (Loc nid' (Trg p'))) t)")
        subgoal
          using prems(11) apply -
          unfolding chnls_imp_front_inv_def Let_def BULK_BENQ_def apply -
          apply (auto simp add: outputs_at_target_def split: if_splits prod.splits)
              apply (smt (verit) Collect_cong Un_iff mem_Collect_eq snd_conv split_cong)
             apply (smt (verit) Collect_cong Un_iff mem_Collect_eq snd_conv split_cong)
          subgoal
            apply (drule spec)+
            apply auto
               apply force
              defer
              apply force+
            done
          subgoal
            apply (drule sym)
            apply (drule the_elem_bi_unique_op_conn)
              apply assumption
            using GS(7) apply assumption
            apply auto
            apply (drule spec2, drule spec, drule mp, assumption)
            apply (drule bspec)
             apply simp
            apply simp
            done
          subgoal
            apply (drule sym)
            apply (drule the_elem_bi_unique_op_conn)
              apply assumption
            using GS(7) apply assumption
            apply auto
            apply (drule spec2, drule spec, drule mp, assumption)
            apply (drule bspec)
             apply simp
            apply simp
            done
          done
        subgoal
          apply safe
          subgoal for p nid' p' _ d t
            apply simp
            using temp(3,7,9) apply -
            unfolding Src_caps_inv_def
            apply (drule spec2[of _ nid p])
            unfolding c_pts_inv_def
            apply (drule spec[of _ "Loc nid (Src p)"])
            apply simp
            apply (rule frontier_less_equal_le_trans[rotated])
             apply (rule frontier_less_equal_change_multiplicities[OF D, where A="extract_prog enum_class.enum (graph_to_nxt (summ sg)) os"])
            subgoal 
              apply safe
              subgoal for l t m
                apply (subst (asm) (2) extract_prog_def)
                apply clarsimp
                subgoal for nid''
                  using temp(15)[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of Nil nid'', simplified, unfolded changes_above_impl_inv_def]
                  apply auto
                  done
                done
              done
            subgoal
              apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid (Src p)", simplified, OF D])
              subgoal
                apply (rule path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF D]])
                apply (meson GS(2,7) in_op_conn_graph_to_nxt_iff op_conn.simps)
                done
              apply simp
              apply (meson frontier_less_equal_zcount_pos snd_image_mp zcount_to_zmset_gt_0)
              done
            done
          done
        done
      subgoal premises prems
        using prems(12,2) apply -
        unfolding change_deltas_inv_def
        apply auto
        done
      defer
      subgoal premises prems
        unfolding produ_consu_supported_def
        apply (auto del: disjCI simp add: image_iff)
        subgoal
          using prems(15)[unfolded produ_consu_supported_def]
          by blast
        subgoal for p t m
          using temp(2) apply -
          apply (drule bspec)
           apply assumption
          apply (clarsimp del: disjCI simp add: image_iff)
          apply (simp flip: zcount_to_zmset_gt_0)
          using prems(8)[unfolded c_pts_inv_def, rule_format, of "Loc nid (Src p)", symmetric]
            prems(6)[unfolded Src_caps_inv_def, rule_format, of nid p, symmetric] apply -
          apply (clarsimp del: disjCI simp add: c_pts_change_multiplicities comp_def)
          apply (subgoal_tac "0 < zcount (c_pts (pt_tr sg) (Loc nid (Src p))) t \<or> zcount (zmset (map snd (filter (\<lambda>x. p = fst x) (operator_state.inter (os nid))))) t > 0")
          defer
          subgoal
            by linarith
          apply (elim disjE)
          subgoal
            by blast
          subgoal
            apply (rule disjI2)
            apply (metis (no_types, lifting) fun_comp_eq_conv gt_0_zcount_msetD)
            done
          done
        subgoal for nid' p t m
          using prems(15)[unfolded produ_consu_supported_def]
          by blast
        subgoal for p t m
          using prems(15)[unfolded produ_consu_supported_def] apply -
          apply clarsimp
          apply (drule spec2, drule spec, drule mp, blast)
          apply (simp add:  zmset_concat comp_def monoid_add_class.sum_list_distinct_conv_sum_set split_beta if_distrib[where f=produ])
          apply (subgoal_tac "
(\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(p'', ab). graph_to_nxt (summ sg) (fst x, p'') = Some (nid, p) \<and> snd x = p'') (produ (os (fst x)))))) \<subseteq>#\<^sub>z
(\<Sum>x\<in>UNIV.
            zmset
             (map snd
               (filter (\<lambda>(p'', ab). graph_to_nxt (summ sg) (fst x, p'') = Some (nid, p) \<and> snd x = p'')
                 (if fst x = nid
                  then produ
                        (os nid
                         \<lparr>outpu := \<lambda>p. outpu (os nid) p @ oputs p, ocaps := \<lambda>p. list_diff (ocaps (os nid) p) (drops p), input := \<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drops p)) (input (os nid) p),
                            produ := produ (os nid) @ produs, inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum), nfron := V\<rparr>)
                  else produ (os (fst x))))))
          ")
          subgoal
            by (smt (verit, best) zmset_subset_eq_zcount)
          subgoal premises temp
            unfolding subseteq_zmset_def
            apply (clarsimp simp add: zcount_sum)
            apply (rule ordered_comm_monoid_add_class.sum_le_included)
               apply auto
            subgoal
              apply (rule ordered_comm_monoid_add_class.add_nonneg_nonneg)
              subgoal
                apply (rule zcount_zmset_ge_0I)
                apply clarsimp
                using prems(12)[unfolded change_deltas_inv_def] apply fastforce
                done
              subgoal
                apply (rule zcount_zmset_ge_0I)
                apply clarsimp
                using prems(2) apply fastforce
                done
              done
            subgoal 
              apply (rule zcount_zmset_ge_0I)
              apply clarsimp
              using prems(12)[unfolded change_deltas_inv_def] apply fastforce
              done
            apply (intro exI impI conjI)
               apply fast
              apply simp_all
            subgoal 
              apply (rule zcount_zmset_ge_0I)
              apply clarsimp
              using prems(2) apply fastforce
              done
            done
          done
        subgoal for nid' p t m
          using prems(15)[unfolded produ_consu_supported_def] apply -
          apply clarsimp
          apply (drule spec2, drule spec, drule mp, blast)          
          apply (simp add:  zmset_concat comp_def monoid_add_class.sum_list_distinct_conv_sum_set split_beta if_distrib[where f=produ])
          apply (subgoal_tac "
(\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(p'', ab). graph_to_nxt (summ sg) (fst x, p'') = Some (nid', p) \<and> snd x = p'') (produ (os (fst x)))))) \<subseteq>#\<^sub>z
(\<Sum>x\<in>UNIV.
            zmset
             (map snd
               (filter (\<lambda>(p'', ab). graph_to_nxt (summ sg) (fst x, p'') = Some (nid', p) \<and> snd x = p'')
                 (if fst x = nid
                  then produ
                        (os nid
                         \<lparr>outpu := \<lambda>p. outpu (os nid) p @ oputs p, ocaps := \<lambda>p. list_diff (ocaps (os nid) p) (drops p), input := \<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drops p)) (input (os nid) p),
                            produ := produ (os nid) @ produs, inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum), nfron := V\<rparr>)
                  else produ (os (fst x))))))
          ")
          subgoal
            by (smt (verit, best) zmset_subset_eq_zcount)
  subgoal premises temp
            unfolding subseteq_zmset_def
            apply (clarsimp simp add: zcount_sum)
            apply (rule ordered_comm_monoid_add_class.sum_le_included)
               apply auto
            subgoal
              apply (rule ordered_comm_monoid_add_class.add_nonneg_nonneg)
              subgoal
                apply (rule zcount_zmset_ge_0I)
                apply clarsimp
                using prems(12)[unfolded change_deltas_inv_def] apply fastforce
                done
              subgoal
                apply (rule zcount_zmset_ge_0I)
                apply clarsimp
                using prems(2) apply fastforce
                done
              done
            subgoal 
              apply (rule zcount_zmset_ge_0I)
              apply clarsimp
              using prems(12)[unfolded change_deltas_inv_def] apply fastforce
              done
            apply (intro exI impI conjI)
               apply fast
              apply simp_all
            subgoal 
              apply (rule zcount_zmset_ge_0I)
              apply clarsimp
              using prems(2) apply fastforce
              done
            done
          done
        done
      subgoal premises prems
        unfolding extract_prog_changes_above_impl_inv_def
        apply (auto 0 0)
        subgoal for xs
          using prems(14)[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of xs] D temp(1,7,9,2) GS(2,7) apply -
          apply (induct xs arbitrary: os sg rule: rev_induct)
          subgoal for os sg
            apply simp
            unfolding changes_above_impl_inv_def
            apply safe
            subgoal for l t m
              apply (clarsimp simp add: split_beta)
              apply (subst (asm) (2) obtain_progress_def)
              apply (subst (asm) (2) extract_progress_def)
              apply (clarsimp simp add: Misc.set_map_filter image_iff split_beta split: option.splits; hypsubst_thin?)
              subgoal for p' m
                apply (drule meta_spec)+
                apply (drule bspec)
                 back
                unfolding extract_progress_def obtain_progress_def
                 apply (clarsimp del: disjCI simp add: Misc.set_map_filter image_iff split_beta split: option.splits; hypsubst_thin?)
                 apply fast
                apply simp
                done
              subgoal for p' 
                apply (drule meta_spec)+
                apply (drule bspec)
                 back
                unfolding extract_progress_def obtain_progress_def
                 apply (clarsimp simp add: Misc.set_map_filter image_iff split_beta split: option.splits; hypsubst_thin?)
                 apply blast
                apply simp
                done
              subgoal for p' 
                apply (rule frontier_less_equal_le_trans[rotated])
                 apply (rule frontier_less_equal_change_multiplicities[where A="extract_prog enum_class.enum (graph_to_nxt (summ sg)) os"])
                  apply assumption
                subgoal 
                  apply safe
                  apply (subst (asm) (2) extract_prog_def)
                  apply clarsimp
                  subgoal
                    by force
                  done
                subgoal
                  apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid (Src p')", simplified])
                    apply assumption
                  subgoal
                    apply (rule graph.path_weight_refl)
                    apply (rule dataflow_topology.axioms(1))
                    apply auto
                    done
                  subgoal
                    unfolding Src_caps_inv_def
                    apply (drule spec2[of _ nid p'])
                    unfolding c_pts_inv_def
                    apply (drule spec[of _ "Loc nid (Src p')"])
                    apply simp
                    apply (subgoal_tac "t \<in> set (ocaps (os nid) p')") 
                    subgoal
                      by (simp add: frontier_less_equal_zcount_pos)
                    subgoal
                      by force
                    done
                  done
                done
              subgoal for p nid' p'
                apply (drule meta_spec[of _ nid])
                apply (drule spec2, drule spec2, drule mp, assumption)
                apply (drule bspec[of _ _ "(Loc nid' (Trg p'), _, _)"])
                 apply simp_all
                unfolding extract_progress_def obtain_progress_def
                apply (clarsimp del: disjCI simp add: Misc.set_map_filter image_iff split_beta split: option.splits; hypsubst_thin?)
                apply (rule disjI2)+
                apply (rule exI[of _ p])
                apply (intro conjI impI allI)
                 apply (rule exI[of _ nid'])
                 apply (rule exI[of _ p'])
                 apply simp
                apply auto
                done
              subgoal for p t' b nid' p'
                apply (subgoal_tac "graph_to_nxt (summ sg) (nid, p) = Some (nid', p')")
                subgoal
                  apply (drule spec2[of _ nid' p'])
                  apply (drule mp)
                   apply assumption
                  apply clarsimp
                  apply hypsubst_thin
                  apply (drule bspec)
                   apply assumption
                  apply clarsimp
                  unfolding Src_caps_inv_def
                  apply (drule spec2[of _ nid p])
                  unfolding c_pts_inv_def
                  apply (drule spec[of _ "Loc nid (Src p)"])
                  apply simp
                  apply (rule frontier_less_equal_le_trans[rotated])
                   apply (rule frontier_less_equal_change_multiplicities[where A="extract_prog enum_class.enum (graph_to_nxt (summ sg)) os"])
                    apply assumption
                  subgoal
                    apply safe
                    apply (subst (asm) (2) extract_prog_def)
                    apply clarsimp
                    apply fastforce
                    done
                  apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid (Src p)", simplified])
                    apply assumption
                  subgoal
                    apply (rule path_weight_direct_0path[OF dataflow_topology.axioms(1)[]])
                     apply assumption
                    apply auto
                    done
                  apply simp
                  apply (meson frontier_less_equal_zcount_pos zcount_to_zmset_gt_0)
                  done
                subgoal premises temp2
                  using temp2(10) apply -
                  unfolding graph_to_nxt_def
                  apply simp
                  apply (rule find_Some_singleton)
                  apply (auto simp add: is_empty_antichain_iff)
                  using temp2(8)
                   apply (metis Pair_inject bi_uniqueDr op_conn.simps)+
                  done
                done
              done
            done
          subgoal premises prems for nid' xs os sg
            using prems(2-) apply -
            using prems(1) apply -
            apply (drule meta_spec[of _ "sg\<lparr> pt_tr :=  change_multiplicities (summ sg) (extract_prog [nid'] (graph_to_nxt (summ sg)) os) (pt_tr sg) \<rparr>"])
            apply (drule meta_spec[of _ "os( nid' := fst (obtain_progress (os nid')) )"])
            apply (drule meta_mp)
            subgoal 
              using prems(2) by auto
            apply (drule meta_mp)
            subgoal 
              using prems(3) by auto
            apply (drule meta_mp)
            subgoal for nid''
              apply (auto simp add:  )
              apply (drule meta_spec[of _ nid''])
              apply (drule meta_mp)
               apply simp
              apply (metis (no_types, opaque_lifting) change_multiplicities_append_alt change_multiplicities_comm)
              done
            apply auto
            apply (drule meta_mp)
            subgoal 
              using prems(7) apply -
              unfolding Src_caps_inv_def obtain_progress_def
              apply auto
              done
            apply (metis (no_types, lifting) change_multiplicities_append_alt change_multiplicities_comm)
            done
          done
        subgoal for nid' xs
          unfolding changes_above_impl_inv_def
          apply safe
          subgoal for l t m
            apply (cases "nid \<in> set xs"; simp?)
            subgoal
              apply (subst (asm) obtain_progress_def)
              apply (subst (asm) extract_progress_def)
              apply (clarsimp simp add: image_iff split_beta Misc.set_map_filter split: option.splits; hypsubst_thin?)
              subgoal for p' m
                apply (frule conjunct2[OF prems(15)[unfolded produ_consu_supported_def], rule_format])
                apply (cases "\<exists> nid'' p''. graph_to_nxt (summ sg) (nid'', p'') = Some (nid', p')")
                subgoal
                  apply clarsimp
                  subgoal for nid'' p''
                    apply (cases "nid'' \<in> set xs")
                    subgoal
                      apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid' (Trg p')", simplified])
                      subgoal
                        sorry
                      subgoal
                        apply (cases "nid'' = nid")
                        subgoal
                          apply hypsubst_thin
                        apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                        apply simp_all
                        apply (clarsimp simp add: c_pts_change_multiplicities obtain_progress_def extract_progress_def filter_map comp_def split_beta split: option.splits)
                          apply (subst (3) filter_False)
                          subgoal
                            apply (auto simp add: obtain_progress_def Misc.set_map_filter extract_prog_def extract_progress_def split: option.splits)
                            using temp(5)[unfolded graph_summar_nt_def]
                            apply (metis (no_types, lifting) Pair_inject domI in_op_conn_graph_to_nxt_iff inj_on_eq_iff op_conn.simps)
                            done
                          apply (clarsimp simp add: monoid_add_class.sum_list_distinct_conv_sum_set split_beta zmset_concat comp_def)
                          apply (subgoal_tac "
 (\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(p'', ab). graph_to_nxt (summ sg) (fst x, p'') = Some (nid', p') \<and> snd x = p'') (produ (os (fst x)))))) = 
zmset
          (map snd
            (filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (List.map_filter (\<lambda>(p, t, m). case graph_to_nxt (summ sg) (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os nid)))))")
                          defer
                          subgoal
                            apply (subst comm_monoid_add_class.sum.subset_diff[of "{(nid, p'')}"])
                            apply simp_all
                            apply (subst comm_monoid_add_class.sum.neutral)
                            subgoal
                              apply clarsimp
                              using temp(5)[unfolded graph_summar_nt_def]
                              apply (smt (verit, best) case_prodE domI filter_empty_conv inj_on_def list.map_disc_iff prod.inject zmset_emptyI)
                              done
                            apply simp
                            apply (rule arg_cong[where f=zmset])
                            apply (subst filter_map_filter[where g="\<lambda> (p'', t, m). (Loc nid' (Trg p''), t, m)"])
                              defer
                            defer
                            apply (clarsimp simp add: comp_def split: prod.splits)
                             apply (rule map_cong)
                              apply (rule filter_cong)
                               apply simp_all
                              defer
                            defer
                            apply (auto 0 0 simp add: comp_def split: prod.splits option.splits)[1]
                               defer
                               apply (auto 0 0 simp add: comp_def split: prod.splits option.splits)[1]


                          find_theorems map name: cong

              
                          find_theorems "filter _ (filter _ _)"

                      find_theorems "filter _ (List.map_filter  _ _)"

end
                apply (cases "\<exists> p. t \<in># mset (drops p) \<and> graph_to_nxt (summ sg) (nid, p) = Some (nid', p')")
                subgoal
                  apply clarsimp

                  term "graph_to_nxt (summ sg)"


              find_theorems List.map_filter set

end
            subgoal
              using prems(14)[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs" nid', unfolded changes_above_impl_inv_def]
        apply simp
        apply (drule bspec)
         apply assumption
              apply auto
              done

            find_theorems produs

end
  apply (rule frontier_less_equal_ifrontier_from_Src[where s=0 and nid=nid and nt="graph_to_nxt (summ sg)" and p=p and os=os, simplified, OF D])
  defer

  using prems(14) apply assumption



  find_theorems extract_prog_changes_above_impl_inv

  thm conjunct2[OF GS(7)[unfolded bi_unique_def, simplified, rule_format], rule_format]

  using GS(7)

  thm in_op_conn_graph_to_nxt_iff[OF GS(7)]

  find_theorems graph_to_nxt Some



end