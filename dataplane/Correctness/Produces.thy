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

lemma eq_singletonD:
  "{x. P x} = {x} \<Longrightarrow> P x"
  by auto


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


lemma sum_zmset_filter_graph_to_nxt:
  assumes GR: "graph_summar_nt su (graph_to_nxt su) os"
  shows "graph_to_nxt su (nid, p) = Some (nid', p') \<Longrightarrow>
   (\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(p'', ab). graph_to_nxt su (fst x, p'') = Some (nid', p') \<and> snd x = p'') (produ (os (fst x)))))) =
   zmset (map snd (filter (\<lambda> (p', _, _). p' = p) (produ (os nid))))"
  apply (rule sum_eq_singleton[where a="(nid, p)"])
     apply simp_all
  subgoal
    apply (rule arg_cong[where f=zmset])
    apply (rule map_cong)
     apply (rule filter_cong)
      apply auto
    done
  subgoal
    apply (auto simp add: filter_empty_conv intro!: zmset_emptyI)
    using GR[unfolded graph_summar_nt_def]
     apply (metis domI inj_on_eq_iff prod.inject)+
    done
  done

lemma sum_zmset_filter_graph_to_nxt_no_connection:
   "(\<forall> nid p. graph_to_nxt su (nid, p) \<noteq> Some (nid', p')) \<Longrightarrow>
   (\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(p'', ab). graph_to_nxt su (fst x, p'') = Some (nid', p') \<and> snd x = p'') (produ (os (fst x)))))) =
   {#}\<^sub>z"
  by (auto simp add: filter_empty_conv intro!: zmset_emptyI comm_monoid_add_class.sum.neutral)

lemma zmset_filter_graph_to_nxt:
  assumes GR: "graph_summar_nt su (graph_to_nxt su) os"
  shows "graph_to_nxt su (nid, p) = Some (nid', p') \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (List.map_filter (\<lambda>(p, t, m). case graph_to_nxt su (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs))) =
   zmset (map snd (filter (\<lambda> (p', _, _). p' = p) xs))"
  apply (rule arg_cong[where f=zmset])
  apply (induct xs)
   apply simp_all
  apply (auto simp add: split: option.splits)
  using GR[unfolded graph_summar_nt_def]
  apply (metis (no_types, opaque_lifting) domI inj_onD snd_conv)
  done

lemma sum_zmset_map_filter_graph_to_nxt:
  assumes GR: "graph_summar_nt su (graph_to_nxt su) os"
  shows
  "finite A \<Longrightarrow>
   nid \<in> A \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid', p') \<Longrightarrow>
   (\<Sum>x\<in>A.
            zmset
             (map snd (filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (List.map_filter (\<lambda>(p, t, m). case graph_to_nxt su (x, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os x)))))) =
    zmset (map snd (filter (\<lambda> (p', _, _). p' = p) (produ (os nid))))"
  apply (rule sum_eq_singleton[where a="nid"])
     apply simp_all
   apply (subst zmset_filter_graph_to_nxt[OF GR])
    apply assumption
   apply simp_all
    apply (auto simp add: Misc.set_map_filter filter_empty_conv intro!: zmset_emptyI split: option.splits)
  using GR[unfolded graph_summar_nt_def]
  apply (metis (no_types, lifting) Pair_inject domIff graph_to_nxt_not_Ex_op_conn in_op_conn_graph_to_nxt_iff inj_onD op_conn.simps)
  done

lemma zmset_filter_graph_to_nxt_no_connection:
  "(\<forall> nid p. graph_to_nxt su (nid, p) \<noteq> Some (nid', p')) \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (List.map_filter (\<lambda>(p, t, m). case graph_to_nxt su (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs))) =
   {#}\<^sub>z"
  apply (induct xs)
   apply simp_all
  apply (auto simp add: split: option.splits)
  done

lemma sum_minus_zero:
  "finite A \<Longrightarrow>
   (\<forall> x\<in>A. G x = (0 :: _ :: group_add)) \<Longrightarrow>
   (\<Sum>x\<in>A. F x - G x) =
   (\<Sum>x\<in>A. F x)"
  by auto

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
        unfolding produ_consu_inter_supported_def
        apply (auto del: disjCI simp add: image_iff)
        subgoal
          using prems(15)[unfolded produ_consu_inter_supported_def]
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
          using prems(15)[unfolded produ_consu_inter_supported_def]
          by blast
        subgoal for p t m
          using prems(15)[unfolded produ_consu_inter_supported_def] apply -
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
          using prems(15)[unfolded produ_consu_inter_supported_def] apply -
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
        subgoal
          using prems(15)[unfolded produ_consu_inter_supported_def] apply -
          apply clarsimp
          apply (drule spec2, drule spec, drule mp, blast)  
          apply auto
          done
        subgoal for p t
          using temp(1)[rule_format, of p] prems(6)[unfolded Src_caps_inv_def, rule_format, of nid p, symmetric]
            prems(8)[unfolded c_pts_inv_def, rule_format, of "Loc nid (Src p)", symmetric] apply -
          apply (simp add: c_pts_change_multiplicities comp_def)
          unfolding zmultiset_eq_iff
          apply (drule spec[of _ t])+
          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc nid (Src p))) t > 0 \<or> zcount (zmset (map snd (filter (\<lambda>x. p = fst x) (operator_state.inter (os nid))))) t > 0")
          subgoal
            apply (elim disjE)
            subgoal
          apply (rule exI[of _ t])
              by simp
            subgoal
              apply (drule zcount_zmset_gt_0_set_Ex)
          apply (clarsimp del: disjCI)
         using prems(15)[unfolded produ_consu_inter_supported_def] apply -
          apply (clarsimp del: disjCI)
          apply (drule spec2, drule spec, drule mp, blast)  
                   apply auto
         done
       done
     subgoal
       apply (subgoal_tac "zcount (to_zmset (ocaps (os nid) p)) t > 0")
       subgoal
         by force
       subgoal
         apply (rule zmset_elem_nonneg)
          apply force
         using to_zmset_nenneg apply fast
         done
       done
     done
   subgoal for nid' p t m
         using prems(15)[unfolded produ_consu_inter_supported_def] apply -
          apply (clarsimp del: disjCI)
         apply (drule spec2, drule spec, drule mp, blast)  
         apply auto
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
                      by fastforce
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
                apply (subst change_multiplicities_extract_prog_updates[where nid=nid])
                  apply assumption+
                apply (cases "\<exists> l t' s. (node l = nid \<longrightarrow> is_Trg (port l)) \<and> t \<ge> t' -+- s \<and> s \<in>\<^sub>A graph.path_weight (summ sg) l (Loc nid' (Trg p')) \<and> frontier_less_equal (frontier (c_pts (change_multiplicities (summ sg) (extract_prog xs (graph_to_nxt (summ sg)) os) (pt_tr sg)) l)) t'")
                subgoal
                  apply clarsimp
                  subgoal for l' t' s
                    apply (cases "node l' = nid")
                    subgoal
                      apply simp
                      apply (rule frontier_less_equal_trans[rotated])
                      apply assumption
                      apply (rule frontier_less_equal_ifrontierI[OF D, of s l'])
                      apply assumption
                      apply (clarsimp simp add: c_pts_change_multiplicities)
                      apply (subst (3) filter_False)
                      subgoal
                        apply (cases l'; simp)
                        apply (auto simp add: Misc.set_map_filter extract_prog_def extract_progress_def image_iff obtain_progress_def split: option.splits)
                        done
                      subgoal
                        apply simp
                        apply (subgoal_tac "\<forall> t. zcount (zmset (map snd (filter (\<lambda>(l'a, t, d). l' = l'a) (List.map_filter (\<lambda>(p, t, m). case graph_to_nxt (summ sg) (node l', p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) produs)))) t \<ge> 0")
                        subgoal
                          by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) frontier_below_eq_frontier_plus_pos frontier_less_equal_le_trans)
                        subgoal
                  apply (auto simp add: Misc.set_map_filter zcount_sum filter_empty_conv intro!: zcount_zmset_ge_0I zmset_emptyI ordered_comm_monoid_add_class.sum_nonneg split: option.splits)
                          using prems(12)[unfolded change_deltas_inv_def]
                          apply (metis graph_to_nxt_Some_alt old.prod.case temp(2,5) zle_add1_eq_le zless_add1_eq)
                          done
                        done
                      done
                    subgoal
                      apply simp
                      apply (rule frontier_less_equal_trans[rotated])
                      apply assumption
                      apply (rule frontier_less_equal_ifrontierI[OF D, of s l'])
                      apply assumption
                      apply (clarsimp simp add: c_pts_change_multiplicities)
                      apply (subst (3) filter_False)
                      subgoal
                        apply (cases l'; simp)
                        done
                      subgoal 
                        apply (subgoal_tac "\<forall> t. zcount (zmset (map snd (filter (\<lambda>(l'a, t, d). l' = l'a) (List.map_filter (\<lambda>(p, t, m). case graph_to_nxt (summ sg) (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) produs)))) t \<ge> 0")
                        subgoal
                          apply simp
                          apply (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) frontier_below_eq_frontier_plus_pos frontier_less_equal_le_trans)
                          done
                        subgoal
                          apply (auto simp add: Misc.set_map_filter zcount_sum filter_empty_conv intro!: zcount_zmset_ge_0I zmset_emptyI ordered_comm_monoid_add_class.sum_nonneg split: option.splits)
                          using prems(12)[unfolded change_deltas_inv_def]
                          apply (metis graph_to_nxt_Some_alt old.prod.case temp(2,5) zle_add1_eq_le zless_add1_eq)
                          done
                        done
                      done
                    done
                  done
                subgoal
                  apply auto
                using prems(14)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format, of xs nid' "(Loc nid' (Trg p'), t, -m)"] apply -
                apply simp
                apply (drule meta_mp)
                subgoal
                  unfolding extract_progress_def obtain_progress_def
                  apply simp
                  apply force
                  done
                subgoal
                  apply (drule frontier_less_equal_ifrontierE[OF _ D])
                  apply clarsimp
                  subgoal for l s t'
                    apply hypsubst_thin
                      apply (cases "\<exists> p. l = Loc nid (Src p)")
                       apply clarsimp
                      subgoal for p
                        apply hypsubst_thin
                        oops



function find_timestamp where
  "find_timestamp c su S (l :: 'loc :: {enum}) t =
   (if l \<in> S then {}
    else if \<exists> t'\<le>t. zcount (c_pts c l) t' > 0 
    then {l} 
    else
    let L = {(l', t'). \<exists> s. s \<in>\<^sub>A su l' l \<and> t = t' -+- s} in \<Union> ((\<lambda> (l', t'). find_timestamp c su (insert l S) l' t') ` L))"
  by auto
termination
  apply (relation "measure (\<lambda>(c, su, S, l, t). card ((UNIV :: 'loc set) - S))")
   apply simp
  apply clarsimp
  apply (rule diff_Suc_less)
  apply (simp add: card_gt_0_iff)
  apply blast
  done

lemma find_timestamp_sound:
  assumes G: "Graph.graph su"
  shows "l' \<in> find_timestamp c su S l t \<Longrightarrow>
   (\<exists> s t'. s \<in>\<^sub>A graph.path_weight su l' l \<and> s -+- t' \<le> t \<and> zcount (c_pts c l') t' > 0)"
  using assms
  apply (induction c su S l t arbitrary: l' rule: find_timestamp.induct)
  subgoal for c su S l t l'
    apply (subst (asm) (2) find_timestamp.simps)
    apply (split if_splits)
    subgoal by simp
    apply (split if_splits)
    subgoal for t'
      apply clarsimp
      apply hypsubst_thin
      subgoal
        apply (rule exI[of _ 0])
        apply (intro conjI)
        apply (meson graph.path_weight_refl)
        apply (rule exI[of _ t'])
         apply simp
        done
      done
    subgoal
      apply clarsimp
      subgoal for l'' t'' s_edge
        oops



lemma backtrack_consu_to_non_nid:
  assumes P: "produ_consu_inter_supported (graph_to_nxt su) os c"
    and G: "Graph.graph su"
    and C: "change_deltas_inv os"
    and GR: "graph_summar_nt su (graph_to_nxt su) os"
  shows "s \<in>\<^sub>A graph.path_weight su (Loc nid (Src p)) (Loc nid' lp) \<Longrightarrow>
   (case lp of Trg p' \<Rightarrow> \<exists>m. (p' :: 'p :: {enum,linorder}, t, m) \<in> set (consu (os nid')) | Src p' \<Rightarrow> \<exists>m. (p', t, m) \<in> set (inter (os nid'))) \<Longrightarrow>
   t \<ge> ft -+- s \<Longrightarrow>
   nid \<in> set xs \<Longrightarrow>
   nid \<noteq> nid' \<Longrightarrow>
   distinct xs \<Longrightarrow>
   nid' \<notin> set xs \<Longrightarrow>
   (\<exists> s l ft'. node l \<noteq> nid \<and> t \<ge> ft' -+- s \<and> s \<in>\<^sub>A graph.path_weight su l (Loc nid' lp) \<and>
   (zcount (c_pts (change_multiplicities su ((extract_prog xs (graph_to_nxt su) os) @ map (\<lambda>(p, y). (Loc nid (Src p), y)) (concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum))) c) l) ft' > 0))"
  apply (drule graph.path_weight_conv_path[OF G])
  apply clarsimp
  subgoal premises temp for ps
    using temp(1,2,3,4,5,6,7,9-) apply -
    apply hypsubst_thin
    apply (induct ps arbitrary: nid' lp p t  rule: rev_induct) 
    subgoal
      by (auto elim: graph.path0E[OF G])
    subgoal premises prems for a ps' nid' lp p t
      using prems(2-) apply -
      apply (clarsimp split: prod.splits; hypsubst_thin)
      subgoal for l1 s l2
        apply (erule graph.path_AppendE[OF G])
        apply (cases lp)
        subgoal for p'
        apply clarsimp
        apply hypsubst_thin
        apply (frule conjunct1[OF conjunct2[OF P[unfolded produ_consu_inter_supported_def]], rule_format])
          apply simp
           apply (frule summary_SrcEx[OF GR])
                apply (elim exE)
                apply hypsubst_thin
          apply (drule graph_to_nxt_Some[OF GR])
          subgoal for m nid'' p''
            apply (cases "nid'' \<in> set xs")
            subgoal
          apply (rule exI[of _ 0])
          apply (rule exI[of _ "Loc nid' (Trg p')"])
          apply clarsimp
          apply (rule exI[of _ t])        
          apply (intro conjI)
            apply simp_all
              subgoal 
                by (rule Graph.graph.path_weight_refl[OF G])
          subgoal
            apply (clarsimp simp add: c_pts_change_multiplicities)
            apply (auto simp add: monoid_add_class.sum_list_distinct_conv_sum_set  zmset_concat map_concat filter_map filter_concat comp_def split_beta Misc.set_map_filter extract_prog_def extract_progress_def image_iff obtain_progress_def split: option.splits)
            apply (subst sum_minus_zero)
              apply simp_all
            subgoal
              by (auto simp add: filter_empty_conv intro!: zmset_emptyI)
            subgoal
              apply (subst (asm) sum_zmset_filter_graph_to_nxt[OF GR])
              apply assumption
              apply (subst sum_zmset_map_filter_graph_to_nxt[where nid=nid'', OF GR])
              apply simp
                apply simp_all
              done
            done
          done
          subgoal
            apply (frule gt_0_plusD)
            apply (elim disjE)
            subgoal
              apply (rule exI[of _ 0])
              apply (rule exI[of _ "Loc nid' (Trg p')"])
              apply clarsimp
              apply (rule exI[of _ t])        
              apply (intro conjI)
                apply simp_all
              subgoal by (rule Graph.graph.path_weight_refl[OF G])
              subgoal
                apply (clarsimp simp add: c_pts_change_multiplicities)
            apply (auto simp add: monoid_add_class.sum_list_distinct_conv_sum_set  zmset_concat map_concat filter_map filter_concat comp_def split_beta Misc.set_map_filter extract_prog_def extract_progress_def image_iff obtain_progress_def split: option.splits)
                apply (subst sum_minus_zero)
                  apply simp_all
                subgoal
                  by (auto simp add: filter_empty_conv intro!: zmset_emptyI)
                subgoal
                  apply (rule ordered_comm_monoid_add_class.add_pos_nonneg)
                  apply simp_all
                  apply (auto simp add: Misc.set_map_filter zcount_sum filter_empty_conv intro!: zcount_zmset_ge_0I zmset_emptyI ordered_comm_monoid_add_class.sum_nonneg split: option.splits)
                  apply (drule spec2)
                  apply (drule graph_to_nxt_Some_alt[OF GR])
                  apply (drule mp)
                   apply assumption
                  apply clarsimp
                  using C[unfolded change_deltas_inv_def]
                  apply (smt (verit, del_insts) UnCI)
                  done
                done
              done
            subgoal
              apply (drule zcount_zmset_gt_0_set_Ex)
              apply clarsimp
              subgoal for m' nid''' p'''
                apply (subgoal_tac "nid''' = nid'' \<and> p''' = p''")
                 defer
                subgoal
                  using graph_to_nxt_inj[OF GR] by auto
                subgoal
                  apply clarsimp
                  apply hypsubst_thin
              apply (drule conjunct1[OF P[unfolded produ_consu_inter_supported_def], rule_format])
                apply (elim disjE)
                  subgoal
                  apply (rule exI[of _ 0])
                  apply (rule exI[of _ "Loc nid'' (Src p'')"])
                    apply clarsimp
                    apply (intro conjI)
                    apply blast
                    apply (rule exI[of _ t])  
                    apply simp_all
                    apply (intro conjI)
                    subgoal sorry
                    subgoal
                      apply (clarsimp simp add: c_pts_change_multiplicities)
                      apply (auto simp add: monoid_add_class.sum_list_distinct_conv_sum_set  zmset_concat map_concat filter_map filter_concat comp_def split_beta Misc.set_map_filter extract_prog_def extract_progress_def image_iff obtain_progress_def split: option.splits)
                      apply (rule ordered_comm_monoid_add_class.add_pos_nonneg)
                       apply simp_all
                  apply (auto simp add: Misc.set_map_filter zcount_sum filter_empty_conv intro!: zcount_zmset_ge_0I zmset_emptyI ordered_comm_monoid_add_class.sum_nonneg split: option.splits)
                      apply (subst (2) comm_monoid_add_class.sum.neutral)
                      subgoal
                  apply (auto simp add: Misc.set_map_filter zcount_sum filter_empty_conv intro!: zcount_zmset_ge_0I zmset_emptyI ordered_comm_monoid_add_class.sum_nonneg split: option.splits)
                        apply (subst filter_False)
                         apply auto
                        done
                  apply (auto simp add: Misc.set_map_filter zcount_sum filter_empty_conv intro!: zcount_zmset_ge_0I zmset_emptyI ordered_comm_monoid_add_class.sum_nonneg split: option.splits)
                        apply (subst filter_False)
                      subgoal
                        by auto
                  apply (auto simp add: Misc.set_map_filter zcount_sum filter_empty_conv intro!: zcount_zmset_ge_0I zmset_emptyI ordered_comm_monoid_add_class.sum_nonneg split: option.splits)
                      done
                    done
                  subgoal
                    apply clarsimp
                    using prems(1)[where lp="Src p''", of t nid'' p, simplified] apply -
                        apply simp
                        apply (drule meta_mp)
                        subgoal
                          by fast
                        apply (drule meta_mp)
                        subgoal
                          by (meson add_mono_thms_linordered_semiring(2) dataflow_topology_from_tree.foldr_plus_zero_le dual_order.trans)
                        apply (drule meta_mp)
                         apply fast
                        apply clarsimp
                        subgoal for mm s' l ft'
                          apply (rule exI)
                          apply (rule exI[of _ l])
                          apply simp
                          apply (rule exI[of _ ft'])
                          apply simp
                          sorry
                        done
                      done
                    done
                  done
                done
              done
            done
          subgoal for p'
        apply clarsimp
            apply hypsubst_thin
            apply (frule summary_TrgEx[OF GR])
            apply clarsimp
            apply hypsubst_thin
            subgoal for m nid'' p''
              apply (drule intsum_from_graph[OF GR])
              apply clarsimp
              apply hypsubst_thin
              apply (frule conjunct2[OF conjunct2[OF P[unfolded produ_consu_inter_supported_def]], rule_format])
              apply clarsimp
              subgoal for t''
                apply (elim disjE)
                subgoal
                  sorry
                subgoal
                  apply clarsimp
                  subgoal for t''' p''' s' m'
                    apply hypsubst_thin
                    apply (cases  "p''' = p''")
                    subgoal
                      apply hypsubst_thin
                      sorry
                    subgoal
                      apply (drule conjunct1[OF conjunct2[OF P[unfolded produ_consu_inter_supported_def]], rule_format])
                      oops


lemma finite_visit_backtrack_consu_to_non_nid:
  assumes P: "produ_consu_inter_supported (graph_to_nxt su) os c"
    and G: "Graph.graph su"
    and C: "change_deltas_inv os"
    and GR: "graph_summar_nt su (graph_to_nxt su) os"
  shows 
 "(case lp of Trg p' \<Rightarrow> \<exists>m. (p' :: 'p :: {enum,linorder}, t, m) \<in> set (consu (os nid')) | Src p' \<Rightarrow> \<exists>m. (p', t, m) \<in> set (inter (os nid'))) \<Longrightarrow>
   t \<ge> ft -+- s \<Longrightarrow>
   nid \<in> set xs \<Longrightarrow>
   nid \<noteq> nid' \<Longrightarrow>
   distinct xs \<Longrightarrow>
   nid' \<notin> set xs \<Longrightarrow>
   (\<exists> s l ft'. (is_Src (port l) \<longrightarrow> node l \<noteq> nid) \<and> t \<ge> ft' -+- s \<and> s \<in>\<^sub>A graph.path_weight su l (Loc nid' lp) \<and>
   (zcount (c_pts (change_multiplicities su ((extract_prog xs (graph_to_nxt su) os) @ map (\<lambda>(p, y). (Loc nid (Src p), y)) (concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum))) c) l) ft' > 0))"



  term "wf {}"

  find_theorems wf "(<)"


end
       


