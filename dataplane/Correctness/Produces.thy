theory Produces

imports
  Mints
  "HOL-Library.Product_Lexorder"
begin

declare cin.rep_eq[simp del]
declare enum_class.enum_UNIV[simp] enum_class.enum_distinct[simp]
no_notation shiftr  (infixl \<open>>>\<close> 55)

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]


(*
   (\<forall> p. to_zmset (drops p) \<subseteq>#\<^sub>z zmset (map snd (filter (\<lambda>x. p = fst x) produs))) \<Longrightarrow>
*)

section \<open>Graph Path Weights and Filtered Sums\<close>

text \<open>Path-weight facts for the summary graph and sums over filtered
  signed multisets.\<close>








function find_timestamp where
  "find_timestamp su P T (l :: 'loc :: {enum}) t =
   (if P l t then {l} else
    if t \<in> set (T l) then let LT = {(l', t'). \<exists> s. s \<in>\<^sub>A su l' l \<and> t = t' -+- s} in \<Union> ((\<lambda> (l', t'). find_timestamp su P (T(l := filter ((\<noteq>) t) (T l))) l' t') ` LT)
    else {})"
  by auto
termination
  apply (relation "measure (\<lambda>(su, P, T, l, t). sum (\<lambda> l'. card (set (T l'))) UNIV)")
  apply simp
  apply (clarsimp split: if_split)
  apply (rule sum_strict_mono_ex1)
  apply (auto simp add: card_mono intro!: psubset_card_mono)
  done

declare find_timestamp.simps[simp del]

inductive srcs_to_trg for P su where
  direct: "su (Loc snid (Src sp)) (Loc nid (Trg p)) \<noteq> {}\<^sub>A \<Longrightarrow> P nid p t m \<Longrightarrow> srcs_to_trg P su snid nid p t m"
| step: "su (Loc snid' (Src sp)) (Loc nid (Trg p)) \<noteq> {}\<^sub>A \<Longrightarrow> snid' \<noteq> snid \<Longrightarrow>
  (\<forall> p' s. s \<in>\<^sub>A su (Loc snid' (Trg p')) (Loc snid' (Src sp)) \<longrightarrow> (\<forall> t' m'. t = t' -+- s \<longrightarrow> P snid' p' t' m' \<longrightarrow> srcs_to_trg P su snid snid' p' t' m')) \<Longrightarrow> srcs_to_trg P su snid nid p t m"

section \<open>Zero Predecessors\<close>

text \<open>Predecessor locations whose summaries leave a timestamp unchanged,
  with a well-founded weight for inducting over them.\<close>
context dataflow_topology
begin

definition zero_predecessors where
  "zero_predecessors t loc  = {loc'. (\<exists> s . s \<in>\<^sub>A path_weight loc' loc \<and> loc \<noteq> loc' \<and> results_in t s = t)}"

context 
  fixes t :: "'t"
begin 

function weight' where
  "weight' loc = (1 :: nat) + (\<Sum> loc' \<in> zero_predecessors t loc . weight' loc')"
  by auto
termination
  apply(relation "{(loc', loc) . \<exists> s . s \<in>\<^sub>A path_weight loc' loc \<and> loc \<noteq> loc' \<and> results_in t s = t}")
  subgoal
    apply(rule Wellfounded.finite_acyclic_wf)
    apply simp
    unfolding acyclic_def
    apply safe
    subgoal premises self_loop for loc
    proof -
      have "(loc', loc) \<in> {(loc', loc). \<exists>s. s \<in>\<^sub>A path_weight loc' loc \<and> loc \<noteq> loc' \<and> results_in t s = t}\<^sup>+ \<Longrightarrow>
        \<exists>xs. path loc' loc xs \<and> xs \<noteq> [] \<and> results_in t (sum_weights (map (\<lambda>(s, l, t). l) xs)) = t" for loc'
        apply (induct loc' rule: converse_trancl_induct)
        apply auto []
        apply (auto simp only: results_in_sum_path_weights_append elim: path)
        apply(frule flow.path_weight_conv_path)
        apply safe
        subgoal for y s xs
          apply(rule exI[where x = xs])
          by(auto elim: flow.path0E)
        subgoal for y z xs x
          apply(auto dest!: flow.path_weight_conv_path)
          subgoal for xs'
            apply(rule exI[where x = "xs' @ xs"])
            apply(auto intro: flow.path_trans)
            by (metis (lifting) foldr_append followed_by_summary sum_weights_append)
          done
        done
      from this[OF self_loop] show False using no_zero_cycle[OF _ _ refl, of loc _ t]
        by force
    qed
    done
  apply(auto simp add: zero_predecessors_def)
  done

end
end


section \<open>Invariant Preservation under Produces and Drops\<close>

text \<open>The central lemma of this theory: the dataplane tracker invariant
  survives a step that produces data and drops capabilities.\<close>
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
   dataplane_tracker_inv (os(nid := os nid \<lparr>outpu := noutput, ocaps := nocaps, input := ninput, produ := nprodu, inter := ninter\<rparr>)) cbufs sg"
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
        by (auto simp add: temp(1) to_zmset_list_diff)
      subgoal premises prems
      supply  if_cong[cong]
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
          subgoal for p1 p''' p''
            apply (subst temp(4)[rule_format, of p1, unfolded to_zmset_map, simplified])
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
          supply if_cong[cong]
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
                            produ := produ (os nid) @ produs, inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum)\<rparr>)
                  else produ (os (fst x))))))
          ")
          subgoal
            apply simp
            apply (meson lt_le_lt subseteq_zmset_def)
            done
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
            subgoal
              by auto
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
                            produ := produ (os nid) @ produs, inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum)\<rparr>)
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
        subgoal for p t m
          using prems(15)[unfolded produ_consu_inter_supported_def] apply -
          apply (clarsimp del: disjCI)
          apply (drule spec2, drule spec, drule mp, blast)  
          apply (auto del: disjCI)
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
              by blast
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
          apply blast
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
              apply(subgoal_tac "\<And> lp p'' t' m nid'' n n'. nid \<in> set xs \<Longrightarrow>
    nid'' \<noteq> nid \<Longrightarrow>
    distinct xs \<Longrightarrow>
    nid'' \<notin> set xs \<Longrightarrow>
    (p'', t', m) \<in> set (consu (os nid'')) \<Longrightarrow>
    n' \<le> n \<Longrightarrow>
    n' \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid'' (Trg p'')) (Loc nid' lp) \<Longrightarrow>
    t \<ge> t' -+- n \<Longrightarrow>
    frontier_less_equal
     (ifrontier (summ sg) (-+-)
       (change_multiplicities (summ sg)
         (extract_prog xs (graph_to_nxt (summ sg))
           (os(nid :=
                 os nid
                 \<lparr>outpu := \<lambda>p. outpu (os nid) p @ oputs p, ocaps := \<lambda>p. list_diff (ocaps (os nid) p) (drops p),
                    input := \<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drops p)) (input (os nid) p), produ := produ (os nid) @ produs,
                    inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum)\<rparr>)))
         (pt_tr sg))                                                                                                               
       (Loc nid' lp))
     t")
              defer
              subgoal premises prems' for lp p'' t' m' nid'' n n'
                using prems'(3-4,6-)
                apply -
                apply(induction "(card {t. t \<le> t' \<and> (\<exists> p m nid. (p, t, m) \<in> set (consu (os nid)))}, Produces.dataflow_topology.weight' (summ sg) (-+-) t' (Loc nid'' (Trg p'')))" arbitrary: p'' t' m' nid'' n n' rule: less_induct)
                subgoal premises prems'' for p'' t' nid'' m' n n'
                  apply(subgoal_tac "Graph.graph (summ sg)")
                  defer
                  subgoal
                    by (rule dataflow_topology.axioms(1)[OF D])
                  using prems''(2-)
                  apply -
                  apply (frule conjunct1[OF conjunct2[OF prems(15)[unfolded produ_consu_inter_supported_def]], rule_format])
                  apply (cases "\<exists> nid''' p'''. graph_to_nxt (summ sg) (nid''', p''') = Some (nid'', p'')")
                  subgoal
                    apply clarsimp
                    subgoal for nid''' p'''
                      apply (cases "nid''' \<in> set xs")
                      subgoal
                        apply(rule frontier_less_equal_trans[of _ "t' -+- n'"]; simp?)
                        apply (rule frontier_less_equal_ifrontierI[OF D, of n' "Loc nid'' (Trg p'')", simplified])
                        subgoal
                          by simp
                        subgoal
                          apply (cases "nid''' = nid")
                          subgoal
                            apply hypsubst_thin
                            apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                            apply simp_all
                            apply (clarsimp simp add: c_pts_change_multiplicities obtain_progress_def extract_progress_def filter_map comp_def split_beta split: option.splits)
                            apply (subst (3) filter_False)
                            subgoal
                              apply (auto simp add: obtain_progress_def Misc.set_map_filter extract_prog_def extract_progress_def split: option.splits)
                              using temp(5)[unfolded graph_summar_nt_def]
                              apply (metis (no_types, lifting) Pair_inject domI in_op_conn_graph_to_nxt_iff inj_on_eq_iff op_conn.simps)+
                              done
                            apply (clarsimp simp add: monoid_add_class.sum_list_distinct_conv_sum_set split_beta zmset_concat comp_def)


                            apply (subgoal_tac "
 (\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(p''a, ab). graph_to_nxt (summ sg) (fst x, p''a) = Some (nid'', p'') \<and> snd x = p''a) (produ (os (fst x)))))) = 
  zmset
          (map snd
            (filter (\<lambda>(l', t, d). Loc nid'' (Trg p'') = l') (List.map_filter (\<lambda>(p, t, m). case graph_to_nxt (summ sg) (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os nid)))))")

                            defer
                            subgoal
                              apply (subst comm_monoid_add_class.sum.subset_diff[of "{(nid, p''')}"])
                              apply simp_all
                              apply (subst comm_monoid_add_class.sum.neutral)
                              subgoal
                                apply clarsimp
                                using temp(5)[unfolded graph_summar_nt_def]
                                apply (smt (verit, best) case_prodE domI filter_empty_conv inj_on_def list.map_disc_iff prod.inject zmset_emptyI)
                                done
                              apply simp
                              apply (subst map_snd_filter_List_map_filter)
                              apply assumption
                              using temp(5)[unfolded graph_summar_nt_def] apply simp_all
                              done
                            subgoal
                              apply simp
                              apply (rule frontier_less_equal_zcount_pos)
                              apply (simp flip: add.assoc)
                              apply (rule ordered_comm_monoid_add_class.add_pos_nonneg)
                              apply simp_all
                              apply (rule zcount_zmset_ge_0I)
                              apply (auto simp add:  Misc.set_map_filter split: option.splits)
                              using temp(2) temp(5)[unfolded graph_summar_nt_def] apply (smt (verit) in_op_conn_graph_to_nxt_iff old.prod.case op_conn.simps)+
                              done
                            done
                          subgoal
                            apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid'''])
                            apply simp_all
                            apply (clarsimp simp add: c_pts_change_multiplicities obtain_progress_def extract_progress_def filter_map comp_def split_beta split: option.splits)
                            apply (subst (2) filter_False)
                            subgoal
                              apply (auto simp add: obtain_progress_def Misc.set_map_filter extract_prog_def extract_progress_def split: option.splits)
                              using temp(5)[unfolded graph_summar_nt_def]
                              apply (metis (no_types, lifting) domI in_op_conn_graph_to_nxt_iff inj_on_eq_iff op_conn.simps prod.simps(1))+
                              done
                            apply simp
                            apply (clarsimp simp add: monoid_add_class.sum_list_distinct_conv_sum_set split_beta zmset_concat comp_def)
                            apply (subst (asm) comm_monoid_add_class.sum.subset_diff[of "{(nid''', p''')}"])
                            apply simp_all
                            apply (subst (asm) comm_monoid_add_class.sum.neutral)
                            subgoal
                              apply clarsimp
                              using temp(5)[unfolded graph_summar_nt_def]
                              apply (smt (verit, best) case_prodE domI filter_empty_conv inj_on_def list.map_disc_iff prod.inject zmset_emptyI)
                              done
                            apply simp
                            apply (subst map_snd_filter_List_map_filter)
                            apply assumption
                            using temp(5)[unfolded graph_summar_nt_def] apply simp
                            apply (simp flip: zcount_union)
                            apply (drule zcount_gt_0_in_frontierD)
                            apply clarsimp
                            apply (subst (2) filter_False)
                            using frontier_less_equal_iff apply auto
                            done
                          done
                        subgoal
                          using D dataflow_topology.results_in_mono(2) dual_order.trans by blast
                        done
                      subgoal
                        apply (cases "nid''' = nid")
                        subgoal
                          by auto
                        subgoal
                          apply (subst change_multiplicities_extract_prog_updates[where nid=nid])
                          apply assumption+
                          apply (simp add: map_concat comp_def)
                          apply (subgoal_tac "0 < zcount (c_pts (pt_tr sg) (Loc nid'' (Trg p''))) t' \<or> 
        0 < zcount (zmset (concat
             (map (\<lambda>(nid', p'). map snd (filter (\<lambda>(p''a, ab). graph_to_nxt (summ sg) (nid', p''a) = Some (nid'', p'') \<and> p' = p''a) (produ (os nid'))))
               enum_class.enum))) t'")
                          defer
                          subgoal
                            by auto
                          subgoal
                            apply (elim disjE)
                            subgoal
                              apply(rule frontier_less_equal_trans[of _ "t' -+- n'"]; simp?)
                              apply (rule frontier_less_equal_ifrontierI[OF D, of n' "Loc nid'' (Trg p'')", simplified])
                              subgoal
                                by simp
                              subgoal
                                apply (simp add: c_pts_change_multiplicities)
                                apply (subst filter_False)
                                subgoal
                                  unfolding extract_progress_def obtain_progress_def extract_prog_def
                                  apply (auto simp add:  Misc.set_map_filter split: option.splits)
                                  using temp(5)[unfolded graph_summar_nt_def]
                                  apply (metis (no_types, lifting) domI in_op_conn_graph_to_nxt_iff inj_on_eq_iff op_conn.simps prod.simps(1))+
                                  done
                                apply (subst filter_False)
                                subgoal
                                  unfolding extract_progress_def obtain_progress_def extract_prog_def
                                  apply (auto simp add: Misc.set_map_filter split: option.splits)
                                  using temp(5)[unfolded graph_summar_nt_def]
                                  apply (metis (no_types, lifting) domI in_op_conn_graph_to_nxt_iff inj_on_eq_iff op_conn.simps prod.simps(1))+
                                  done
                                subgoal
                                  apply simp
                                  apply (metis frontier_less_equal_zcount_pos)
                                  done
                                done
                              subgoal
                                using D dataflow_topology.results_in_mono(2) dual_order.trans by blast
                              done
                            subgoal
                              apply (clarsimp simp add: zcount_sum monoid_add_class.sum_list_distinct_conv_sum_set  comp_def zmset_concat split_beta)
                              apply (subgoal_tac "\<exists> m. (p''', t', m) \<in> set (produ (os nid'''))")
                              defer
                              subgoal
                                apply (drule sum_pos_ex_elem_pos)
                                apply clarsimp
                                apply (drule zcount_zmset_gt_0_set_Ex)
                                apply clarsimp
                                using temp(5)[unfolded graph_summar_nt_def]
                                apply (metis (mono_tags, lifting) domI fst_eqD inv_on_f_f snd_eqD)
                                done
                              subgoal
                                apply clarsimp
                                subgoal for m''
                                  apply (drule conjunct1[OF prems(15)[unfolded produ_consu_inter_supported_def], rule_format])
                                  apply (elim disjE)
                                  subgoal
                                    apply(subgoal_tac "\<exists> n''. n'' \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid''' (Src p''')) (Loc nid' lp) \<and> n'' \<le> 0 + n'")
                                    defer
                                    subgoal
                                      using GS(2)
                                      apply -
                                      apply(erule allE[where x = nid''])
                                      apply(erule allE[where x = nid'''])
                                      apply(erule allE[where x = p''])
                                      apply(erule allE[where x = p'''])
                                      apply(erule impE, assumption)
                                      apply(drule path_weight_direct_0path[rotated], assumption)
                                      apply(rule graph.path_weight_elem_trans)
                                      apply metis
                                      defer
                                      apply assumption
                                      apply auto
                                      done
                                    apply(erule conjE exE)+
                                    subgoal for n''
                                      apply(rule frontier_less_equal_trans[of _ "t' -+- n''"]; simp?)
                                      apply (rule frontier_less_equal_ifrontierI[of _ n'' "Loc nid''' (Src p''')", simplified, OF D], assumption)
                                      apply (simp add: change_multiplicities_append_alt)
                                      apply (clarsimp simp add: c_pts_change_multiplicities)
                                      apply (subst (2) filter_False)
                                      subgoal
                                        by (auto simp add: Misc.set_map_filter split: option.splits)
                                      apply simp
                                      apply (subst (1) filter_False)
                                      subgoal
                                        by (auto simp add: Misc.set_map_filter map_concat extract_prog_def extract_progress_def split_beta image_iff del: disjCI split: option.splits)
                                      apply simp
                                      using frontier_less_equal_trans frontier_less_equal_zcount_pos apply blast
                                      subgoal
                                        using D dataflow_topology.results_in_mono(2) dual_order.trans by blast
                                      done
                                    done
                                  subgoal
                                    apply clarsimp
                                    subgoal for m''
                                      apply (drule conjunct2[OF conjunct2[OF prems(15)[unfolded produ_consu_inter_supported_def]], rule_format])
                                      apply (elim disjE exE)
                                      subgoal for t'
                                        apply(subgoal_tac "\<exists> n''. n'' \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid''' (Src p''')) (Loc nid' lp) \<and> n'' \<le> 0 + n'")
                                        defer
                                        subgoal
                                          using GS(2)
                                          apply -
                                          apply(erule allE[where x = nid''])
                                          apply(erule allE[where x = nid'''])
                                          apply(erule allE[where x = p''])
                                          apply(erule allE[where x = p'''])
                                          apply(erule impE, assumption)
                                          apply(drule path_weight_direct_0path[rotated], assumption)
                                          apply(rule graph.path_weight_elem_trans)
                                          by auto
                                        apply(erule conjE exE)+
                                        subgoal for n''
                                          apply(rule frontier_less_equal_trans[of _ "t' -+- n''"]; simp?)
                                          apply (rule frontier_less_equal_ifrontierI[of _ n'' "Loc nid''' (Src p''')", simplified, OF D], assumption)
                                          apply (simp add: change_multiplicities_append_alt)
                                          apply (clarsimp simp add: c_pts_change_multiplicities)
                                          apply (subst (2) filter_False)
                                          subgoal
                                            by (auto simp add: Misc.set_map_filter split: option.splits)
                                          apply simp
                                          apply (subst (1) filter_False)
                                          subgoal
                                            by (auto simp add: Misc.set_map_filter map_concat extract_prog_def extract_progress_def split_beta image_iff del: disjCI split: option.splits)
                                          apply simp
                                          using frontier_less_equal_trans frontier_less_equal_zcount_pos apply blast
                                          using dataflow_topology_from_tree.results_in_mono_raw
                                          by (metis (lifting) Graph.graph_def add_increasing2 le_iff_add)
                                        done
                                      subgoal for t1' p1 s1 m1
                                        apply clarsimp
                                          (*     apply(drule sym[of t]; simp) *)
                                        subgoal 
                                          apply(subgoal_tac "(card {t. t \<le> t1' \<and> (\<exists>p m nid. (p, t, m) \<in> set (consu (os nid)))}, dataflow_topology.weight' (summ sg) (-+-) t1' (Loc nid''' (Trg p1)))
  < (card {t. t \<le> t' \<and> (\<exists>p m nid. (p, t, m) \<in> set (consu (os nid)))}, dataflow_topology.weight' (summ sg) (-+-) t' (Loc nid'' (Trg p'')))")
                                          defer
                                          subgoal
                                            apply(cases "t' = t1'")
                                            subgoal
                                              apply simp
                                              apply(subst (2) dataflow_topology.weight'.simps[OF D])
                                              apply simp
                                              unfolding dataflow_topology.zero_predecessors_def[OF D]
                                                (* use graph.path_weight instead of summ*)
                                              apply(subgoal_tac "Loc nid''' (Trg p1) \<in> {loc'. \<exists>s. s \<in>\<^sub>A graph.path_weight (summ sg) loc' (Loc nid'' (Trg p'')) \<and> Loc nid'' (Trg p'') \<noteq> Loc nid''' (Trg p1) \<and> t1' -+- s = t1'}")
                                              defer
                                              subgoal
                                                using GS(2)
                                                apply -
                                                apply(erule allE[where x = nid''])
                                                apply(erule allE[where x = nid'''])
                                                apply(erule allE[where x = p''])
                                                apply(erule allE[where x = p'''])
                                                using GS(1)
                                                apply -
                                                apply(erule allE[where x = nid'''])
                                                apply(erule allE[where x = p1])
                                                apply(erule allE[where x = p'''])
                                                apply(erule allE[where x = 0])
                                                apply simp
                                                apply(rule conjI)
                                                subgoal
                                                  using graph.path_weight_elem_trans[of "summ sg" 0 "Loc nid''' (Trg p1)" "Loc nid''' (Src p''')" 0
                                                      "Loc nid'' (Trg p'')", simplified] 
                                                  by(auto dest!: path_weight_direct_0path)
                                                subgoal
                                                  apply auto
                                                    (* should be a contradiction summ sg (Loc nid''' (Src p''')) (Loc nid''' (Trg p1))*)

                                                  apply (drule path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF D]])
                                                  apply (drule Graph.graph.path_weight_conv_path[OF dataflow_topology.axioms(1)[OF D]])
                                                  apply (drule Graph.graph.path_weight_conv_path[OF dataflow_topology.axioms(1)[OF D]])
                                                  apply (drule Graph.graph.path_weight_conv_path[OF dataflow_topology.axioms(1)[OF D]])
                                                  apply clarsimp
                                                  subgoal for _ ys zs
                                                    using dataflow_topology.no_zero_cycle[OF D, of "Loc nid''' (Trg p1)" "ys @ zs" 0 undefined] apply -
                                                    apply (drule meta_mp)
                                                    apply (rule graph.path_trans[OF dataflow_topology.axioms(1)[OF D]])
                                                    apply assumption+
                                                    apply (drule meta_mp)
                                                    apply (metis (no_types, opaque_lifting) GS(10,2) Nil_is_append_conv empty_path_inversion not_in_empty)
                                                    apply clarsimp
                                                    done
                                                  done
                                                done
                                              apply(rule le_imp_less_Suc)
                                              apply(subst dataflow_topology_from_tree.sum_singleton[symmetric, where f = "dataflow_topology.weight' (summ sg) (-+-) t1'"])
                                              apply(rule ordered_comm_monoid_add_class.sum_mono2)
                                              by auto
                                            apply simp
                                            apply(rule disjI1)
                                            apply(rule psubset_card_mono)
                                            subgoal
                                              apply(erule thin_rl)+
                                              apply(rule finite_subset[of _ "{t. (\<exists>p m nid. (p, t, m) \<in> set (consu (os nid)))}"])
                                              subgoal
                                                by auto
                                              apply(subgoal_tac "{t. \<exists>p m nid. (p, t, m) \<in> set (consu (os nid))} = {t. \<exists>nid p m. (p, t, m) \<in> set (consu (os nid))}")
                                              defer
                                              subgoal
                                                by auto
                                              apply simp
                                              apply(erule thin_rl)
                                              unfolding finite_Collect_bounded_ex[of "\<lambda>_.True" "\<lambda> t nid. \<exists>p m. (p, t, m) \<in> set (consu (os nid))", simplified]
                                              apply safe
                                              subgoal for nid
                                                apply(subgoal_tac "{t. \<exists>p m. (p, t, m) \<in> set (consu (os nid))} = set (map (\<lambda>(_,t,_). t) (consu (os nid)))")
                                                defer
                                                subgoal
                                                  by force
                                                by simp
                                              done
                                            subgoal
                                              apply auto
                                              subgoal
                                                unfolding add.commute[of t1' s1]
                                                by (meson basic_trans_rules(23) graph.le_plus(2))
                                              subgoal
                                                apply(subgoal_tac "t1' -+- s1 \<in> {t. t \<le> t1' -+- s1 \<and> (\<exists>p m nid. (p, t, m) \<in> set (consu (os nid)))}")
                                                defer 
                                                subgoal
                                                  by (metis (no_types, lifting) le_less less_le_not_le mem_Collect_eq)
                                                apply(subgoal_tac "t1' -+- s1 \<notin> {t. t \<le> t1' \<and> (\<exists>p m nid. (p, t, m) \<in> set (consu (os nid)))}")
                                                defer 
                                                subgoal
                                                  apply(rule notI)
                                                  apply(subgoal_tac "t1' -+- s1 \<le> t1'")
                                                  defer
                                                  subgoal
                                                    apply(erule thin_rl[of " t1' -+- s1 \<in> {t. t \<le> t1' -+- s1 \<and> (\<exists>p m nid. (p, t, m) \<in> set (consu (os nid)))} "])
                                                      (* weird stuff idk*)
                                                    unfolding mem_Collect_eq
                                                    apply(erule conjE)
                                                    apply assumption
                                                    done
                                                  apply auto
                                                  apply force
                                                  done
                                                by simp
                                              done
                                            done
                                          apply(subgoal_tac "\<exists>n'. n' \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid''' (Trg p1)) (Loc nid' lp) \<and> n' \<le> n -+- s1")
                                          defer
                                          subgoal

                                            using GS(2)
                                            apply -
                                            apply(erule allE[where x = nid''])
                                            apply(erule allE[where x = nid'''])
                                            apply(erule allE[where x = p''])
                                            apply(erule allE[where x = p'''])
                                            using GS(1)
                                            apply -
                                            apply(erule allE[where x = nid'''])
                                            apply(erule allE[where x = p1])
                                            apply(erule allE[where x = p'''])
                                            apply(erule allE[where x = s1])
                                            apply simp
                                            apply(drule path_weight_direct_0path[rotated], assumption)
                                            apply(erule exE conjE)+
                                            subgoal for s2'
                                              apply(subgoal_tac "\<exists>t'. t' \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid''' (Trg p1)) (Loc nid'' (Trg p'')) \<and> t'\<le> s2' + 0")
                                              defer
                                              subgoal
                                                apply(rule graph.path_weight_elem_trans)
                                                apply blast+
                                                done
                                              apply(erule exE conjE)+
                                              subgoal for s2''
                                                using graph.path_weight_elem_trans[of "summ sg" s2'' "Loc nid''' (Trg p1)" "Loc nid'' (Trg p'')" n' "Loc nid' lp"]
                                                apply simp
                                                apply(erule exE conjE)+
                                                subgoal for n3
                                                  apply(rule exI[where x = n3])
                                                  apply simp
                                                  apply(rule order.trans)
                                                  apply assumption
                                                  by (metis Groups.add_ac(2) add_mono basic_trans_rules(23))
                                                done
                                              done
                                            done
                                          apply(subgoal_tac "t \<ge> t1' -+- (n -+- s1)")
                                          defer
                                          subgoal
                                            by (metis (no_types, lifting) add.commute add_mono_thms_linordered_semiring(2) basic_trans_rules(23) group_cancel.add2)
                                          apply(erule exE conjE)+
                                          using prems''(1)[of t1' nid''' p1 m1 _ "n -+- s1"]
                                          apply simp
                                          apply (subst (asm) change_multiplicities_extract_prog_updates[where nid=nid])
                                          apply assumption+
                                          apply (simp add: map_concat comp_def)
                                          done
                                        done
                                      done
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
                    apply (subst (asm) filter_False)
                    subgoal
                      by auto
                    apply (simp add: zmset_concat comp_def )
                    apply (rule frontier_less_equal_ifrontier_trans_alt2[of _ n' "Loc nid'' (Trg p'')" _ _ t', simplified, OF D])
                    apply assumption
                    defer
                    apply (meson add_left_mono dual_order.trans)
                    apply (rule frontier_less_equal_ifrontierI[of _ 0  "Loc nid'' (Trg p'')", simplified, OF D])
                    subgoal
                      apply (rule graph.path_weight_refl)
                      apply (rule dataflow_topology.axioms(1)[OF D])
                      done
                    subgoal
                      apply (subst change_multiplicities_extract_prog_updates[where nid=nid])
                      apply assumption+
                      apply (simp add: map_concat comp_def)
                      apply (clarsimp simp add: c_pts_change_multiplicities obtain_progress_def extract_progress_def filter_map comp_def split_beta split: option.splits)
                      apply (subst (2) filter_False)
                      subgoal
                        apply (auto simp add:  Misc.set_map_filter split: option.splits)
                        using temp(5)[unfolded graph_summar_nt_def]
                        apply (metis (no_types, lifting) in_op_conn_graph_to_nxt_iff op_conn.simps)+
                        done
                      apply simp
                      subgoal
                        apply (subst filter_False)
                        subgoal
                          apply (auto simp add:  Misc.set_map_filter extract_prog_def extract_progress_def obtain_progress_def split: option.splits)
                          using temp(5)[unfolded graph_summar_nt_def]
                          apply (metis (no_types, lifting) in_op_conn_graph_to_nxt_iff op_conn.simps)+
                          done
                        apply simp
                        using frontier_less_equal_zcount_pos apply blast
                        done
                      done
                    done
                  done
                done
              subgoal
                apply (subst (asm) obtain_progress_def)
                apply (subst (asm) extract_progress_def)
                apply (clarsimp simp add: image_iff split_beta Misc.set_map_filter split: option.splits; hypsubst_thin?)
                subgoal for p' m
                  apply (drule meta_spec[of _ "Trg p'"])
                  subgoal premises prems'
                    apply (rule prems'(6)[of nid' p' t m 0 0, simplified])
                    using prems'(1-5) apply simp
                    using prems'(1-5) apply simp
                    using prems'(1-5) apply simp
                    apply(rule graph.path_weight_refl)
                    apply (metis D dataflow_topology.axioms(1))
                    done
                  done
                subgoal premises prems' for p'
                  using prems'(1,3-) apply -
                  apply (drule conjunct2[OF conjunct2[OF prems(15)[unfolded produ_consu_inter_supported_def]], rule_format])
                  apply (elim disjE exE)
                  subgoal for t'
                    apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid' (Src p')", simplified])
                    subgoal
                      apply (rule graph.path_weight_refl)
                      apply (rule dataflow_topology.axioms(1)[OF D])
                      done
                    subgoal
                      apply (subst change_multiplicities_extract_prog_updates[where nid=nid])
                      apply assumption+
                      apply (simp add: map_concat comp_def)
                      apply (clarsimp simp add: c_pts_change_multiplicities obtain_progress_def extract_progress_def filter_map comp_def split_beta split: option.splits)
                      apply (subst (2) filter_False)
                      subgoal
                        apply (auto simp add:  Misc.set_map_filter split: option.splits)
                        done
                      apply simp
                      subgoal
                        apply (subst filter_False)
                        subgoal
                          apply (auto simp add:  Misc.set_map_filter extract_prog_def extract_progress_def obtain_progress_def split: option.splits)
                          done
                        apply simp
                        using frontier_less_equal_trans frontier_less_equal_zcount_pos apply blast
                        done
                      done
                    done
                  subgoal for t'' p''' s m''
                    apply clarsimp
                    apply (drule conjunct1[OF temp(5)[unfolded graph_summar_nt_def], rule_format])
                    apply clarsimp
                    subgoal for u
                      apply (rule prems'(2)[of nid' _ _ _ u s])
                      apply assumption+
                      done
                    done
                  done
                subgoal premises prems' for p' aa b nid'' p''
                  using prems'(1,3-) apply -
                  apply (cases l; simp)
                  subgoal for nid''' lp
                    apply (cases lp; simp)
                    subgoal for p'''
                      apply hypsubst_thin
                      apply (drule spec2[of _ nid'' p''])
                      apply (drule mp)
                      subgoal
                        using graph_to_nxt_Some_alt temp(5) by blast 
                      apply clarsimp
                      apply hypsubst_thin
                      apply (drule  conjunct1[OF prems(15)[unfolded produ_consu_inter_supported_def], rule_format])
                      apply (elim disjE)
                      subgoal
                        apply (rule frontier_less_equal_ifrontier_trans[OF D, of 0 "Loc nid' (Src p')", simplified])
                        subgoal
                          by (meson D GS(2) dataflow_topology.axioms(1) graph_to_nxt_Some_alt path_weight_direct_0path temp(5))
                        subgoal
                          apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid' (Src p')", simplified])
                          subgoal
                            apply (rule graph.path_weight_refl)
                            apply (rule dataflow_topology.axioms(1)[OF D])
                            done
                          subgoal
                            apply (subst change_multiplicities_extract_prog_updates[where nid=nid])
                            apply assumption+
                            apply (simp add: map_concat comp_def)
                            apply (clarsimp simp add: c_pts_change_multiplicities obtain_progress_def extract_progress_def filter_map comp_def split_beta split: option.splits)
                            apply (subst (2) filter_False)
                            subgoal
                              apply (auto simp add:  Misc.set_map_filter split: option.splits)
                              done
                            apply simp
                            subgoal
                              apply (subst filter_False)
                              subgoal
                                apply (auto simp add:  Misc.set_map_filter extract_prog_def extract_progress_def obtain_progress_def split: option.splits)
                                done
                              apply simp
                              using frontier_less_equal_trans frontier_less_equal_zcount_pos apply blast
                              done
                            done
                          done
                        done
                      subgoal
                        apply clarsimp
                        subgoal for m''
                          apply (drule conjunct2[OF conjunct2[OF prems(15)[unfolded produ_consu_inter_supported_def]], rule_format])
                          apply (elim disjE exE)
                          subgoal for t'
                            (*           apply (rule frontier_less_equal_trans[rotated])
                             apply assumption *)
                            apply (rule frontier_less_equal_ifrontier_trans[OF D, of 0 "Loc nid' (Src p')", simplified])
                            subgoal
                              by (meson D GS(2) dataflow_topology.axioms(1) graph_to_nxt_Some_alt path_weight_direct_0path temp(5))
                            apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid' (Src p')", simplified])
                            subgoal
                              apply (rule graph.path_weight_refl)
                              apply (rule dataflow_topology.axioms(1)[OF D])
                              done
                            subgoal
                              apply (subst change_multiplicities_extract_prog_updates[where nid=nid])
                              apply assumption+
                              apply (simp add: map_concat comp_def)
                              apply (clarsimp simp add: c_pts_change_multiplicities obtain_progress_def extract_progress_def filter_map comp_def split_beta split: option.splits)
                              apply (subst (2) filter_False)
                              subgoal
                                apply (auto simp add:  Misc.set_map_filter split: option.splits)
                                done
                              apply simp
                              subgoal
                                apply (subst filter_False)
                                subgoal
                                  apply (auto simp add:  Misc.set_map_filter extract_prog_def extract_progress_def obtain_progress_def split: option.splits)
                                  done
                                apply simp
                                using frontier_less_equal_trans frontier_less_equal_zcount_pos apply blast
                                done
                              done
                            done
                          subgoal for t' p'' s m'
                            apply clarsimp
                            subgoal 
                              apply (drule conjunct1[OF temp(5)[unfolded graph_summar_nt_def], rule_format])
                              apply clarsimp
                              subgoal for u
                                (*       apply (drule sym[of t])
                                apply simp *)
                                apply (rule frontier_less_equal_ifrontier_trans[OF D, of 0 "Loc nid' (Src p')", simplified])
                                subgoal
                                  by (meson D GS(2) dataflow_topology.axioms(1) graph_to_nxt_Some_alt path_weight_direct_0path temp(5))
                                apply (rule prems'(2)[of nid' _ _ _ u s])
                                apply assumption+
                                done
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
              apply (drule prems(14)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, rule_format])
              apply assumption+
              apply simp
              done
            done
          done
        done
      done
    done
  done

section \<open>Cleaning, Singletons, and Reordered Drops\<close>

text \<open>Variants of the main lemma: cleaned inputs, singleton productions,
  individual capability drops, and reordering of the change list.\<close>
lemma dataplane_tracker_inv_clean_input:
  "(\<forall>nid. intsum (os nid) = intsum (os' nid) \<and>
    ocaps (os nid) = ocaps (os' nid) \<and>
    consu (os nid) = consu (os' nid) \<and>
    inter (os nid) = inter (os' nid) \<and>
    produ (os nid) = produ (os' nid) \<and>
    outpu (os nid) = outpu (os' nid) \<and>
    front (os nid) = front (os' nid)) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg"
  unfolding dataplane_tracker_inv_def Src_caps_inv_def Trg_caps_inv_def
    outputs_at_target_def extract_prog_def extract_progress_def obtain_progress_def
    front_inv_def change_deltas_inv_def extract_prog_changes_above_impl_inv_def
    produ_consu_inter_supported_def
  by (auto split: prod.splits cong: if_cong)

lemma dataplane_tracker_inv_produce_singleton:
  fixes p :: \<open>'p :: {enum, linorder}\<close>
  assumes \<open>dataflow_topology (summ sg) (-+-)\<close> \<open>graph_summar_nt (summ sg) (subgraph.nxt sg) os\<close>
    \<open>subgraph.nxt sg = graph_to_nxt (summ sg)\<close> \<open>dataplane_tracker_inv os cbufs sg\<close>
    \<open>t \<in> set (ocaps (os nid) p)\<close> \<open>os' = os(nid := produces (os nid) [(x, Cap t p)])\<close>
  shows \<open>dataplane_tracker_inv os' cbufs sg\<close>
proof -
  let ?produs = \<open>[(p, t, 1)]\<close>
  let ?oputs = \<open>(\<lambda>_. [])(p := [(x, t)])\<close>
  have \<open>\<forall>p. snd ` set (?oputs p) \<subseteq> set (ocaps (os nid) p)\<close> using assms(5) by fastforce
  moreover have \<open>\<forall>p. to_zmset (map snd (?oputs p))
  = zmset (map snd (filter (\<lambda>x. p = fst x) ?produs))\<close> by (simp add: update_zmultiset_singleton(2))
  ultimately have \<open>dataplane_tracker_inv (os(nid := (os nid)\<lparr>
  outpu := \<lambda>p. outpu (os nid) p @ ?oputs p,
  produ := produ (os nid) @ ?produs,
  inter := inter (os nid) @ concat (map (\<lambda>(_ :: 'p). []) enum_class.enum)\<rparr>))
  cbufs sg\<close> (is \<open>dataplane_tracker_inv ?os' _ _\<close>)
    using dataplane_tracker_inv_produces_drops[OF assms(1) refl refl refl refl refl _ _ _ _ assms(2-4),
        where nid=nid and drops=\<open>\<lambda>_. []\<close> and produs=\<open>?produs\<close> and oputs=\<open>?oputs\<close>]
    by (simp add: assms(5))
  moreover have \<open>?os' = os'\<close> by (simp add: assms(6) produces_def fun_eq_iff split: if_splits)
  ultimately show ?thesis by blast
qed

lemma dataplane_tracker_inv_drop_caps_all:
  assumes \<open>dataflow_topology (summ sg) (-+-)\<close> \<open>graph_summar_nt (summ sg) (subgraph.nxt sg) os\<close>
    \<open>subgraph.nxt sg = graph_to_nxt (summ sg)\<close> \<open>dataplane_tracker_inv os cbufs sg\<close>
    \<open>os' = os(nid := drop_caps (os nid) (map (\<lambda>t. Cap t p) (ocaps (os nid) p)))\<close>
  shows \<open>dataplane_tracker_inv os' cbufs sg\<close>
proof -
  let ?drops = \<open>(\<lambda>_. [])(p := ocaps (os nid) p)\<close>
  let ?f = \<open>\<lambda>p'. map (\<lambda>os. (p', os, - 1)) (?drops p')\<close>
  have \<open>dataplane_tracker_inv (os(nid := (os nid)\<lparr>
  ocaps := \<lambda>p'. list_diff (ocaps (os nid) p') (?drops p'),
  input := \<lambda>p'. filter (\<lambda>(_, t). t \<notin> set (?drops p')) (input (os nid) p'),
  inter := inter (os nid) @ concat (map ?f Enum.enum)\<rparr>))
  cbufs sg\<close> (is \<open>dataplane_tracker_inv ?os' _ _\<close>)
    using dataplane_tracker_inv_produces_drops[OF assms(1) refl refl refl refl refl _ _ _ _ assms(2-4),
        where nid=nid and drops=\<open>?drops\<close> and produs=Nil and oputs=\<open>\<lambda>_. []\<close>] by force
  moreover have \<open>ocaps (?os' nid) = ocaps (os' nid)\<close>
    by (simp add: assms(5) fun_eq_iff ocaps_drop_caps_all)
  moreover have \<open>inter (?os' nid) = inter (os' nid)\<close>
    using concat_map_empty_except_1[OF Enum.enum_distinct, where f=\<open>?f\<close> and x=p]
    by (simp add: assms(5) drop_caps_def comp_def)
  ultimately show ?thesis
    using dataplane_tracker_inv_clean_input[where os=\<open>?os'\<close> and os'=os'] assms(5) by fastforce
qed

lemma dataplane_tracker_inv_drop_cap:
  fixes p :: \<open>'p :: {enum, linorder}\<close>
  assumes \<open>dataflow_topology (summ sg) (-+-)\<close> \<open>graph_summar_nt (summ sg) (subgraph.nxt sg) os\<close>
    \<open>subgraph.nxt sg = graph_to_nxt (summ sg)\<close> \<open>dataplane_tracker_inv os cbufs sg\<close>
    \<open>t \<in> set (ocaps (os nid) p)\<close> \<open>os' = os(nid := drop_caps (os nid) [Cap t p])\<close>
  shows \<open>dataplane_tracker_inv os' cbufs sg\<close>
proof -
  let ?drops = \<open>(\<lambda>_. [])(p := [t])\<close>
  let ?f = \<open>\<lambda>p'. map (\<lambda>os. (p', os, - 1)) (?drops p')\<close>
  have \<open>dataplane_tracker_inv (os(nid := (os nid)\<lparr>
  ocaps := \<lambda>p'. list_diff (ocaps (os nid) p') (?drops p'),
  input := \<lambda>p'. filter (\<lambda>(_, t). t \<notin> set (?drops p')) (input (os nid) p'),
  inter := inter (os nid) @ concat (map ?f Enum.enum)\<rparr>))
  cbufs sg\<close> (is \<open>dataplane_tracker_inv ?os' _ _\<close>)
    using dataplane_tracker_inv_produces_drops[OF assms(1) refl refl refl refl refl _ _ _ _ assms(2-4),
        where nid=nid and drops=\<open>?drops\<close> and produs=Nil and oputs=\<open>\<lambda>_. []\<close>]
    by (simp add: assms(5))
  moreover have \<open>ocaps (?os' nid) = ocaps (os' nid)\<close>
    by (simp add: assms(6) fun_eq_iff drop_caps_singleton)
  moreover have \<open>inter (?os' nid) = inter (os' nid)\<close>
    using concat_map_empty_except_1[OF Enum.enum_distinct, where f=\<open>?f\<close> and x=p]
    by (simp add: assms(6) drop_caps_singleton)
  ultimately show ?thesis
    using dataplane_tracker_inv_clean_input[where os=\<open>?os'\<close> and os'=os' and sg=sg]
    by (simp add: assms(6) drop_caps_singleton)
qed

lemma change_multiplicities_cons_to_middle:
  "change_multiplicities su (x # ys1 @ ys2) c = change_multiplicities su (ys1 @ x # ys2) c"
proof -
  have eq1: "change_multiplicities su (x # ys1 @ ys2) c =
             change_multiplicities su (ys1 @ ys2) (change_multiplicities su [x] c)"
    by (metis append_Cons append_Nil change_multiplicities_append_alt)
  also have "\<dots> = change_multiplicities su ys2 (change_multiplicities su ys1 (change_multiplicities su [x] c))"
    by (metis change_multiplicities_append_alt)
  also have "\<dots> = change_multiplicities su ys2 (change_multiplicities su [x] (change_multiplicities su ys1 c))"
    by (metis change_multiplicities_append_alt change_multiplicities_comm)
  also have "\<dots> = change_multiplicities su (ys1 @ x # ys2) c"
    by (metis append_Cons append_Nil change_multiplicities_append_alt)
  finally show ?thesis .
qed

lemma change_multiplicities_mset_eq:
  "mset xs = mset ys \<Longrightarrow> change_multiplicities su xs c = change_multiplicities su ys c"
proof (induct xs arbitrary: ys c)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have "x \<in> set ys"
    using Cons.prems by (metis list.set_intros(1) set_mset_mset)
  then obtain ys1 ys2 where ys: "ys = ys1 @ x # ys2"
    by (auto dest: split_list)
  with Cons.prems have ms: "mset xs = mset (ys1 @ ys2)" by simp
  have ih: "change_multiplicities su xs c' = change_multiplicities su (ys1 @ ys2) c'" for c'
    using Cons.hyps[OF ms] .
  have "change_multiplicities su (x # xs) c =
        change_multiplicities su xs (change_multiplicities su [x] c)"
    by (metis append_Cons append_Nil change_multiplicities_append_alt)
  also have "\<dots> = change_multiplicities su (ys1 @ ys2) (change_multiplicities su [x] c)"
    using ih by simp
  also have "\<dots> = change_multiplicities su (x # ys1 @ ys2) c"
    by (metis append_Cons append_Nil change_multiplicities_append_alt)
  also have "\<dots> = change_multiplicities su (ys1 @ x # ys2) c"
    using change_multiplicities_cons_to_middle .
  finally show ?case using ys by simp
qed

lemma dataplane_tracker_inv_clean_reorder_inter:
  assumes E: "\<forall>nid. intsum (os nid) = intsum (os' nid) \<and>
     ocaps (os nid) = ocaps (os' nid) \<and>
     consu (os nid) = consu (os' nid) \<and>
     mset (operator_state.inter (os nid)) = mset (operator_state.inter (os' nid)) \<and>
     produ (os nid) = produ (os' nid) \<and>
     outpu (os nid) = outpu (os' nid) \<and>
     front (os nid) = front (os' nid)"
  shows "dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg"
proof -
  let ?os0 = "\<lambda>nid. (os' nid)\<lparr>inter := operator_state.inter (os nid)\<rparr>"
  have clean_eqs:
    "\<forall>nid. intsum (os nid) = intsum (?os0 nid) \<and>
           ocaps (os nid) = ocaps (?os0 nid) \<and>
           consu (os nid) = consu (?os0 nid) \<and>
           operator_state.inter (os nid) = operator_state.inter (?os0 nid) \<and>
           produ (os nid) = produ (?os0 nid) \<and>
           outpu (os nid) = outpu (?os0 nid) \<and>
           front (os nid) = front (?os0 nid)"
    using E by auto
  have step1: "dataplane_tracker_inv os cbufs sg \<longleftrightarrow> dataplane_tracker_inv ?os0 cbufs sg"
    using dataplane_tracker_inv_clean_input[OF clean_eqs] .
  have ms_eq:
    "\<And>nid. mset (operator_state.inter (?os0 nid)) = mset (operator_state.inter (os' nid))"
    using E by auto
  have set_eq:
    "\<And>nid. set (operator_state.inter (?os0 nid)) = set (operator_state.inter (os' nid))"
    using ms_eq by (metis set_mset_mset)
  have nonInter_eq:
    "\<And>nid. intsum (?os0 nid) = intsum (os' nid) \<and>
           ocaps (?os0 nid) = ocaps (os' nid) \<and>
           consu (?os0 nid) = consu (os' nid) \<and>
           produ (?os0 nid) = produ (os' nid) \<and>
           outpu (?os0 nid) = outpu (os' nid) \<and>
           front (?os0 nid) = front (os' nid) \<and>
           input (?os0 nid) = input (os' nid)"
    by auto
  have progress_mset_eq:
    "\<And>nid'. mset (extract_progress nid' nt (snd (obtain_progress (?os0 nid')))) =
            mset (extract_progress nid' nt (snd (obtain_progress (os' nid'))))"
    for nt
    unfolding extract_progress_def obtain_progress_def
    using ms_eq nonInter_eq
    by (simp add: mset_map)
  have extract_prog_mset_eq:
    "\<And>xs. mset (extract_prog xs nt ?os0) = mset (extract_prog xs nt os')" for nt
    unfolding extract_prog_def
    using progress_mset_eq
    by (induct_tac xs) (auto simp: mset_concat)
  have cm_eq:
    "\<And>xs c. change_multiplicities (summ sg) (extract_prog xs (nxt sg) ?os0) c =
            change_multiplicities (summ sg) (extract_prog xs (nxt sg) os') c"
    using change_multiplicities_mset_eq[OF extract_prog_mset_eq] .
  have ext_progress_set_eq:
    "\<And>nid' nt. set (extract_progress nid' nt (snd (obtain_progress (?os0 nid')))) =
               set (extract_progress nid' nt (snd (obtain_progress (os' nid'))))"
    using progress_mset_eq by (metis mset_eq_setD)
  have outputs_eq:
    "outputs_at_target (summ sg) ?os0 = outputs_at_target (summ sg) os'"
    unfolding outputs_at_target_def
    by (auto simp: fun_eq_iff Let_def split: prod.splits)
  have step2: "dataplane_tracker_inv ?os0 cbufs sg \<longleftrightarrow> dataplane_tracker_inv os' cbufs sg"
    unfolding dataplane_tracker_inv_def Src_caps_inv_def
      front_inv_def change_deltas_inv_def extract_prog_changes_above_impl_inv_def
      changes_above_impl_inv_def
      produ_consu_inter_supported_def
    apply (rule iffI)
    subgoal
      apply clarsimp
      subgoal for caps
        apply (rule exI[of _ caps])
        using nonInter_eq set_eq cm_eq ext_progress_set_eq outputs_eq
        by (clarsimp split: prod.splits cong: if_cong)
      done
    subgoal
      apply clarsimp
      subgoal for caps
        apply (rule exI[of _ caps])
        using nonInter_eq set_eq cm_eq ext_progress_set_eq outputs_eq
        by (clarsimp split: prod.splits cong: if_cong)
      done
    done
  show ?thesis using step1 step2 by simp
qed

lemma dataplane_tracker_inv_produces_drops_alt:
  fixes drops :: "'p :: {enum,linorder} \<Rightarrow> 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} list"
  assumes D: "dataflow_topology (summ sg) (-+-)"
  shows
    "noutput = (\<lambda> p . outpu (os nid) p @ oputs p) \<Longrightarrow>
   nocaps = (\<lambda> p . list_diff (ocaps (os nid) p) (drops p)) \<Longrightarrow>
   ninput = (\<lambda> p'. if p = p' then drop n (input (os nid) p) else input (os nid) p') \<Longrightarrow> 
   nprodu = produ (os nid) @ produs \<Longrightarrow>
   mset ninter = mset (operator_state.inter (os nid) @
      concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (map (\<lambda>(_, t, _). t) (filter (\<lambda>x. p = fst x) produs))) Enum.enum) @
      concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p @ map (\<lambda>(_, t, _). t) (filter (\<lambda>x. p = fst x) produs))) Enum.enum)) \<Longrightarrow>
   (\<forall> p. mset (drops p) \<subseteq># mset (ocaps (os nid) p)) \<Longrightarrow>
   (\<forall> (p, t, m) \<in> set produs. m > 0 \<and> (\<exists> t' \<in> set (ocaps (os nid) p). t' \<le> t)) \<Longrightarrow>
   (\<forall> p. \<forall> t \<in> snd ` set (oputs p). (\<exists> t' \<in> set (ocaps (os nid) p). t' \<le> t)) \<Longrightarrow>
   (\<forall> p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))) \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
   nxt sg = graph_to_nxt (summ sg) \<Longrightarrow>
   dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   dataplane_tracker_inv (os(nid := os nid \<lparr>outpu := noutput, ocaps := nocaps, input := ninput, produ := nprodu, inter := ninter\<rparr>)) cbufs sg"
proof -
  assume NOut: "noutput = (\<lambda> p . outpu (os nid) p @ oputs p)"
  assume NOcaps: "nocaps = (\<lambda> p . list_diff (ocaps (os nid) p) (drops p))"
  assume NInput: "ninput = (\<lambda> p'. if p = p' then drop n (input (os nid) p) else input (os nid) p')"
  assume NProdu: "nprodu = produ (os nid) @ produs"
  assume NInter: "mset ninter = mset (operator_state.inter (os nid) @
      concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (map (\<lambda>(_, t, _). t) (filter (\<lambda>x. p = fst x) produs))) Enum.enum) @
      concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p @ map (\<lambda>(_, t, _). t) (filter (\<lambda>x. p = fst x) produs))) Enum.enum))"
  assume Drops: "\<forall> p. mset (drops p) \<subseteq># mset (ocaps (os nid) p)"
  assume Produs: "\<forall> (p, t, m) \<in> set produs. m > 0 \<and> (\<exists> t' \<in> set (ocaps (os nid) p). t' \<le> t)"
  assume Oputs: "\<forall> p. \<forall> t \<in> snd ` set (oputs p). (\<exists> t' \<in> set (ocaps (os nid) p). t' \<le> t)"
  assume Oputs_produs: "\<forall> p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))"
  assume G: "graph_summar_nt (summ sg) (nxt sg) os"
  assume Nxt: "nxt sg = graph_to_nxt (summ sg)"
  assume Inv: "dataplane_tracker_inv os cbufs sg"
  let ?ts = "\<lambda>p. map (\<lambda>(_, t, _). t) (filter (\<lambda>x. p = fst x) produs)"
  let ?osM = "os(nid := os nid\<lparr>
      ocaps := (\<lambda>p. ocaps (os nid) p @ ?ts p),
      inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (?ts p)) Enum.enum)\<rparr>)"
  have minted: "dataplane_tracker_inv ?osM cbufs sg"
    apply (rule dataplane_tracker_inv_mints_many_ports[OF D])
      apply (rule Inv)
     apply (rule G)
    using Produs apply (auto split: prod.splits)
    done
  have G_minted: "graph_summar_nt (summ sg) (nxt sg) ?osM"
    using G by (auto simp add: graph_summar_nt_def)
  have Produs_exact:
    "\<forall>(p, t, m)\<in>set produs. 0 < m \<and> t \<in> set (ocaps (?osM nid) p)"
    using Produs by (fastforce simp add: image_iff split: prod.splits)
  have Oputs_exact:
    "\<forall>p. snd ` set (oputs p) \<subseteq> set (ocaps (?osM nid) p)"
  proof (intro allI subsetI)
    fix p t
    assume t_in: "t \<in> snd ` set (oputs p)"
    have pos: "zcount (to_zmset (map snd (oputs p))) t > 0"
      using t_in by (metis image_iff list.set_map zcount_to_zmset_gt_0)
    have "zcount (zmset (map snd (filter (\<lambda>x. p = fst x) produs))) t > 0"
      using Oputs_produs pos by simp
    then obtain m where prod_t: "(p, t, m) \<in> set produs" and "0 < m"
      using gt_0_zcount_msetD[of p produs t] by (auto simp add: comp_def)
    then have "t \<in> set (map (\<lambda>(_, t, _). t) (filter (\<lambda>x. p = fst x) produs))"
      by force
    then show "t \<in> set (ocaps (?osM nid) p)"
      by simp
  qed
  have Drops_minted:
    "\<forall>p. mset (drops p @ ?ts p) \<subseteq># mset (ocaps (?osM nid) p)"
    using Drops by auto
  let ?finput = "\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drops p @ ?ts p)) (input (os nid) p)"
  let ?fcaps = "\<lambda>p. list_diff (ocaps (os nid) p @ ?ts p) (drops p @ ?ts p)"
  let ?ninter_can = "operator_state.inter (os nid) @
      concat (map (\<lambda>p. map (\<lambda>t. (p, t, 1)) (?ts p)) Enum.enum) @
      concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p @ ?ts p)) Enum.enum)"
  let ?osPD_can = "os(nid := os nid\<lparr>outpu := noutput, ocaps := ?fcaps, input := ?finput, produ := nprodu, inter := ?ninter_can\<rparr>)"
  have inv_pd_raw:
    "dataplane_tracker_inv
      (?osM(nid := ?osM nid\<lparr>
        outpu := noutput,
        ocaps := (\<lambda>p. list_diff (ocaps (?osM nid) p) (drops p @ ?ts p)),
        input := (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drops p @ ?ts p)) (input (?osM nid) p)),
        produ := nprodu,
        inter := ?ninter_can\<rparr>)) cbufs sg"
    apply (rule dataplane_tracker_inv_produces_drops[OF D, where oputs=oputs and produs=produs and drops="\<lambda>p. drops p @ ?ts p"])
               using NOut apply simp
              apply (rule refl)
             apply (rule refl)
            using NProdu apply simp
           apply simp
          using Drops_minted apply simp
         using Produs_exact apply simp
        using Oputs_exact apply simp
       using Oputs_produs apply simp
      apply (rule G_minted)
     apply (rule Nxt)
    apply (rule minted)
    done
  have inv_pd: "dataplane_tracker_inv ?osPD_can cbufs sg"
    using inv_pd_raw by simp
  let ?osTargetCaps_can = "os(nid := os nid\<lparr>outpu := noutput, ocaps := ?fcaps, input := ninput, produ := nprodu, inter := ?ninter_can\<rparr>)"
  have same_input:
    "\<forall>nid. intsum (?osPD_can nid) = intsum (?osTargetCaps_can nid) \<and>
      ocaps (?osPD_can nid) = ocaps (?osTargetCaps_can nid) \<and>
      consu (?osPD_can nid) = consu (?osTargetCaps_can nid) \<and>
      inter (?osPD_can nid) = inter (?osTargetCaps_can nid) \<and>
      produ (?osPD_can nid) = produ (?osTargetCaps_can nid) \<and>
      outpu (?osPD_can nid) = outpu (?osTargetCaps_can nid) \<and>
      front (?osPD_can nid) = front (?osTargetCaps_can nid)"
    by auto
  have inv_target_caps: "dataplane_tracker_inv ?osTargetCaps_can cbufs sg"
    using iffD1[OF dataplane_tracker_inv_clean_input[OF same_input, of cbufs sg]] inv_pd
    by (metis fun_upd_apply)
  have caps_mset:
    "\<forall>p. mset (?fcaps p) = mset (nocaps p)"
    using Drops NOcaps by (auto simp add: multiset_eq_iff)
  let ?osTarget_can = "os(nid := os nid\<lparr>outpu := noutput, ocaps := nocaps, input := ninput, produ := nprodu, inter := ?ninter_can\<rparr>)"
  have same_ocaps:
    "\<forall>nid. intsum (?osTargetCaps_can nid) = intsum (?osTarget_can nid) \<and>
      (\<forall>p. mset (ocaps (?osTargetCaps_can nid) p) = mset (ocaps (?osTarget_can nid) p)) \<and>
      consu (?osTargetCaps_can nid) = consu (?osTarget_can nid) \<and>
      inter (?osTargetCaps_can nid) = inter (?osTarget_can nid) \<and>
      produ (?osTargetCaps_can nid) = produ (?osTarget_can nid) \<and>
      input (?osTargetCaps_can nid) = input (?osTarget_can nid) \<and>
      outpu (?osTargetCaps_can nid) = outpu (?osTarget_can nid) \<and>
      front (?osTargetCaps_can nid) = front (?osTarget_can nid)"
    using caps_mset by auto
  have clean_ocaps:
    "dataplane_tracker_inv ?osTargetCaps_can cbufs sg \<longleftrightarrow> dataplane_tracker_inv ?osTarget_can cbufs sg"
    apply (rule dataplane_tracker_inv_clean_reorder_ocaps)
    using same_ocaps by blast
  have inv_target_can:
    "dataplane_tracker_inv ?osTarget_can cbufs sg"
    using clean_ocaps inv_target_caps by simp
  let ?osTarget = "os(nid := os nid\<lparr>outpu := noutput, ocaps := nocaps, input := ninput, produ := nprodu, inter := ninter\<rparr>)"
  have inter_bridge:
    "\<forall>nid'. intsum (?osTarget_can nid') = intsum (?osTarget nid') \<and>
      ocaps (?osTarget_can nid') = ocaps (?osTarget nid') \<and>
      consu (?osTarget_can nid') = consu (?osTarget nid') \<and>
      mset (operator_state.inter (?osTarget_can nid')) = mset (operator_state.inter (?osTarget nid')) \<and>
      produ (?osTarget_can nid') = produ (?osTarget nid') \<and>
      outpu (?osTarget_can nid') = outpu (?osTarget nid') \<and>
      front (?osTarget_can nid') = front (?osTarget nid')"
    using NInter by auto
  have inv_target:
    "dataplane_tracker_inv ?osTarget cbufs sg"
    using iffD1[OF dataplane_tracker_inv_clean_reorder_inter[OF inter_bridge, of cbufs sg]] inv_target_can
    by blast
  show "dataplane_tracker_inv (os(nid := os nid \<lparr>outpu := noutput, ocaps := nocaps, input := ninput, produ := nprodu, inter := ninter\<rparr>)) cbufs sg"
    using inv_target .
qed


section \<open>Releasing and Adding Capabilities\<close>

text \<open>Invariant preservation when capabilities are released or added
  after production.\<close>
lemma dataplane_tracker_inv_release_caps:
  assumes D: "dataflow_topology (summ sg) (-+-)"
    and Inv: "dataplane_tracker_inv os cbufs sg"
    and G: "graph_summar_nt (summ sg) (nxt sg) os"
    and Nxt: "nxt sg = graph_to_nxt (summ sg)"
  shows "dataplane_tracker_inv (os(nid := release_caps (os nid) p)) cbufs sg"
proof -
  let ?used = "concat (map (\<lambda>(p', s). map (((+) s) \<circ> snd) (input (os nid) p'))
    (concat (map (\<lambda>p'. map (\<lambda>s. (p', s)) (intsum (os nid) p' p)) Enum.enum)))"
  let ?drops = "\<lambda>p'. if p' = p then list_diff (ocaps (os nid) p) ?used else []"
  let ?osD = "os(nid := os nid\<lparr>
    outpu := outpu (os nid),
    ocaps := (\<lambda>p'. list_diff (ocaps (os nid) p') (?drops p')),
    input := (\<lambda>p'. filter (\<lambda>(_, t). t \<notin> set (?drops p')) (input (os nid) p')),
    produ := produ (os nid),
    inter := operator_state.inter (os nid) @ concat (map (\<lambda>p'. map (\<lambda>t. (p', t, - 1)) (?drops p')) Enum.enum)\<rparr>)"
  have invD: "dataplane_tracker_inv ?osD cbufs sg"
    apply (rule dataplane_tracker_inv_produces_drops[OF D, where oputs="\<lambda>_. []" and produs="[]" and drops="?drops"])
               apply simp
              apply simp
             apply simp
            apply simp
           apply simp
          apply (auto simp add: mset_list_diff split: if_splits)[1]
         apply simp
        apply simp
       apply simp
      apply (rule G)
     apply (rule Nxt)
    apply (rule Inv)
    done
  have inter_mset:
    "mset (concat (map (\<lambda>p'. map (\<lambda>t. (p', t, - 1)) (?drops p')) Enum.enum)) =
     mset (map (\<lambda>t. (p, t, - 1)) (?drops p))"
  proof -
    have aux:
      "distinct xs \<Longrightarrow> p \<in> set xs \<Longrightarrow>
        mset (concat (map (\<lambda>p'. map (\<lambda>t. (p', t, - 1)) (?drops p')) xs)) =
        mset (map (\<lambda>t. (p, t, - 1)) (?drops p))" for xs
    proof (induct xs)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs)
      then show ?case
      proof (cases "x = p")
        case True
        then show ?thesis
          using Cons.prems by auto
      next
        case False
        then show ?thesis
          using Cons by auto
      qed
    qed

    show ?thesis
      using aux[of Enum.enum] by simp
  qed
  have same:
    "\<forall>nid'. intsum (?osD nid') = intsum ((os(nid := release_caps (os nid) p)) nid') \<and>
      ocaps (?osD nid') = ocaps ((os(nid := release_caps (os nid) p)) nid') \<and>
      consu (?osD nid') = consu ((os(nid := release_caps (os nid) p)) nid') \<and>
      mset (operator_state.inter (?osD nid')) = mset (operator_state.inter ((os(nid := release_caps (os nid) p)) nid')) \<and>
      produ (?osD nid') = produ ((os(nid := release_caps (os nid) p)) nid') \<and>
      outpu (?osD nid') = outpu ((os(nid := release_caps (os nid) p)) nid') \<and>
      front (?osD nid') = front ((os(nid := release_caps (os nid) p)) nid')"
    using inter_mset
    unfolding release_caps_def drop_caps_def trace_simp Let_def
    by (auto simp add: mset_list_diff multiset_eq_iff filter_map comp_def split: if_splits)

  show ?thesis
    using iffD1[OF dataplane_tracker_inv_clean_reorder_inter[OF same, of cbufs sg]] invD
    by blast
qed

lemma dataplane_tracker_inv_release_caps_update:
  assumes D: "dataflow_topology (summ sg) (-+-)"
    and Inv: "dataplane_tracker_inv (os(nid := os')) cbufs sg"
    and G: "graph_summar_nt (summ sg) (nxt sg) (os(nid := os'))"
    and Nxt: "nxt sg = graph_to_nxt (summ sg)"
  shows "dataplane_tracker_inv (os(nid := release_caps os' p)) cbufs sg"
  using dataplane_tracker_inv_release_caps[OF D Inv G Nxt, where nid=nid and p=p]
  by simp

lemma dataplane_tracker_inv_add_caps_produces_drop_caps_update:
  assumes D: "dataflow_topology (summ sg) (-+-)"
    and Inv: "dataplane_tracker_inv (os(nid := os')) cbufs sg"
    and G: "graph_summar_nt (summ sg) (nxt sg) (os(nid := os'))"
    and Nxt: "nxt sg = graph_to_nxt (summ sg)"
    and batch_caps:
      "\<And>x cap. (x, cap) \<in> set batch \<Longrightarrow>
        \<exists>t'\<in>set (ocaps os' (out cap)). t' \<le> time cap"
  shows "dataplane_tracker_inv
    (os(nid := drop_caps (produces (add_caps os' (map snd batch)) batch) (map snd batch)))
    cbufs sg"
proof -
  let ?produs = "map (\<lambda>(x, cap). (out cap, time cap, 1)) batch"
  let ?oputs = "\<lambda>p. map (\<lambda>(x, cap). (x, time cap)) (filter (\<lambda>(x, cap). out cap = p) batch)"
  let ?target = "drop_caps (produces (add_caps os' (map snd batch)) batch) (map snd batch)"
  have enum_no_insert:
    "p0 \<notin> set ps \<Longrightarrow>
      mset (concat (map (\<lambda>p. if p0 = p then x # f p else f p) ps)) =
      mset (concat (map f ps))" for p0 ps x f
    by (induct ps) auto
  have enum_insert:
    "p0 \<in> set ps \<Longrightarrow> distinct ps \<Longrightarrow>
      mset (concat (map (\<lambda>p. if p0 = p then x # f p else f p) ps)) =
      add_mset x (mset (concat (map f ps)))" for p0 ps x f
  proof (induct ps)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    show ?case
    proof (cases "p0 = p")
      case True
      then show ?thesis
        using Cons.prems enum_no_insert[of p ps x f] by simp
    next
      case False
      then show ?thesis
        using Cons by auto
    qed
  qed


  have group_caps:
    "mset (concat (map (\<lambda>p. map (\<lambda>t. (p, t, m)) (map time (filter (\<lambda>cap. out cap = p) caps))) Enum.enum)) =
     mset (map (\<lambda>cap. (out cap, time cap, m)) caps)" for caps m
  proof (induct caps)
    case Nil
    then show ?case by simp
  next
    case (Cons cap caps)
    let ?f = "\<lambda>p. map (\<lambda>t. (p, t, m)) (map time (filter (\<lambda>cap. out cap = p) caps))"
    have "mset (concat (map (\<lambda>p. map (\<lambda>t. (p, t, m)) (map time (filter (\<lambda>cap. out cap = p) (cap # caps)))) Enum.enum)) =
      mset (concat (map (\<lambda>p. if out cap = p then (p, time cap, m) # ?f p else ?f p) Enum.enum))"
      by (rule arg_cong[where f=mset], rule arg_cong[where f=concat], rule map_cong[OF refl], simp)
    also have "\<dots> = mset (concat (map (\<lambda>p. if out cap = p then (out cap, time cap, m) # ?f p else ?f p) Enum.enum))"
      by (rule arg_cong[where f=mset], rule arg_cong[where f=concat], rule map_cong[OF refl], simp)

    also have "\<dots> = add_mset (out cap, time cap, m) (mset (concat (map ?f Enum.enum)))"
      using enum_insert[of "out cap" Enum.enum "(out cap, time cap, m)" ?f]
      by (auto simp add: Enum.enum_class.in_enum Enum.enum_class.enum_distinct)
    also have "\<dots> = mset (map (\<lambda>cap. (out cap, time cap, m)) (cap # caps))"
      using Cons.hyps by simp
    finally show ?case .
  qed
  have group_produs:
    "mset (concat (map (\<lambda>p. map (\<lambda>x. (p, fst (snd x), m))
      (filter (\<lambda>x. p = fst x) (map (\<lambda>(x, cap). (out cap, time cap, 1)) batch))) Enum.enum)) =
     mset (map (\<lambda>x. (out (snd x), time (snd x), m)) batch)" for m
    using group_caps[of m "map snd batch"]
    by (simp add: filter_map comp_def split_beta eq_commute)

  have inv_abs0:
    "dataplane_tracker_inv
      ((os(nid := os'))(nid := ((os(nid := os')) nid)\<lparr>
        outpu := (\<lambda>p. outpu ((os(nid := os')) nid) p @ ?oputs p),
        ocaps := (\<lambda>p. list_diff (ocaps ((os(nid := os')) nid) p) ((\<lambda>_. []) p)),
        input := (\<lambda>p'. if out (snd (hd batch)) = p'
          then drop 0 (input ((os(nid := os')) nid) (out (snd (hd batch))))
          else input ((os(nid := os')) nid) p'),
        produ := produ ((os(nid := os')) nid) @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) cbufs sg"
    apply (rule dataplane_tracker_inv_produces_drops_alt[OF D,
          where os="os(nid := os')" and nid=nid and oputs="?oputs" and produs="?produs"
            and drops="\<lambda>_. []" and n=0 and p="out (snd (hd batch))"])
               apply simp
              apply simp
             apply simp
            apply simp
           apply (simp add: drop_caps_def produces_def add_caps_def group_caps comp_def split_beta)
          apply (simp add: group_produs)

         using batch_caps apply (auto split: prod.splits)[1]
        using batch_caps apply (auto split: prod.splits)[1]
       using batch_caps apply (auto split: prod.splits)[1]

      apply (simp add: zmset_map_one filter_map comp_def split_beta eq_commute)
      apply (rule allI)
      apply (rule arg_cong[where f=to_zmset])
      apply (rule arg_cong[where f="map (\<lambda>x. time (snd x))"])
      apply (rule filter_cong[OF refl])
      apply (simp split: prod.splits)


      apply (rule G)
     apply (rule Nxt)
    apply (rule Inv)
    done
  have input_abs_eq:
    "(\<lambda>p'. if out (snd (hd batch)) = p'
          then drop 0 (input ((os(nid := os')) nid) (out (snd (hd batch))))
          else input ((os(nid := os')) nid) p') = input os'"
    by (rule ext) simp


  have inv_abs:
    "dataplane_tracker_inv
      (os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) cbufs sg"
    using inv_abs0 input_abs_eq by simp



  have same:
    "\<forall>nid'. intsum ((os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) nid') = intsum ((os(nid := ?target)) nid') \<and>
      (\<forall>p. mset (ocaps ((os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) nid') p) = mset (ocaps ((os(nid := ?target)) nid') p)) \<and>
      consu ((os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) nid') = consu ((os(nid := ?target)) nid') \<and>
      inter ((os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) nid') = inter ((os(nid := ?target)) nid') \<and>
      produ ((os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) nid') = produ ((os(nid := ?target)) nid') \<and>
      input ((os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) nid') = input ((os(nid := ?target)) nid') \<and>
      outpu ((os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) nid') = outpu ((os(nid := ?target)) nid') \<and>
      front ((os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) nid') = front ((os(nid := ?target)) nid')"
    unfolding drop_caps_def produces_def add_caps_def
    by (auto simp add: mset_list_diff group_caps comp_def split_beta multiset_eq_iff split: prod.splits)
  have clean:
    "dataplane_tracker_inv
      (os(nid := os'\<lparr>
        outpu := (\<lambda>p. outpu os' p @ ?oputs p),
        ocaps := ocaps os',
        input := input os',
        produ := produ os' @ ?produs,
        inter := operator_state.inter ?target\<rparr>)) cbufs sg \<longleftrightarrow>
     dataplane_tracker_inv (os(nid := ?target)) cbufs sg"
    apply (rule dataplane_tracker_inv_clean_reorder_ocaps)
    using same by blast
  show ?thesis
    using clean inv_abs by simp

qed


end
