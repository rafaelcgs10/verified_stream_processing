theory Produces

imports
  General
  Dataplane.Timely_Stream
  Dataplane.MyProduct_Instances
  Dataplane.AntichainOrder
  "HOL-Library.Product_Lexorder"
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

definition "backtracks su P T = (\<forall> t l. t \<in> set (T l) \<longrightarrow> (\<exists> l' t' s. l \<noteq> l' \<and> s \<in>\<^sub>A su l' l \<and> t = t' -+- s \<and> t' \<in> set (T l')) \<or> P l t)"

lemma find_timestamp:
  "backtracks su P T \<Longrightarrow>
   t \<in> set (T l) \<Longrightarrow>
   \<exists> l'. l' \<in> find_timestamp su P T l t \<and> (\<exists> t' s. P l' t' \<and> t' -+- s \<le> t \<and> s \<in>\<^sub>A graph.path_weight su l' l)"
  oops
    (*   apply (induction su P T V l t arbitrary: rule: find_timestamp.induct)
  subgoal for su P T V l t
    apply (subst find_timestamp.simps)
    apply (auto split: if_splits)
    subgoal
      apply (subst (asm) (2) backtracks_def)
      apply (drule spec2, drule mp, assumption)
      apply (auto split: if_splits)
      apply (intro exI conjI)
        apply assumption
       apply (rule refl)
      subgoal premises prems for l' t' s
        using prems(2-) apply -
        apply (rule prems(1))
           apply (rule refl)
        using prems apply blast
          apply (rule refl)
        subgoal
        apply (auto 0 0 simp add: backtracks_def)
        subgoal for t''
          apply hypsubst_thin
          apply (rule exI[of _ l'])
          apply (intro conjI impI)
           apply auto
          apply (rule exI[of _ t'])
          apply (rule exI[of _ s])
          apply (intro conjI)
            apply simp
            apply simp
          oops
 *)



inductive srcs_to_trg for P su where
  direct: "su (Loc snid (Src sp)) (Loc nid (Trg p)) \<noteq> {}\<^sub>A \<Longrightarrow> P nid p t m \<Longrightarrow> srcs_to_trg P su snid nid p t m"
| step: "su (Loc snid' (Src sp)) (Loc nid (Trg p)) \<noteq> {}\<^sub>A \<Longrightarrow> snid' \<noteq> snid \<Longrightarrow>
  (\<forall> p' s. s \<in>\<^sub>A su (Loc snid' (Trg p')) (Loc snid' (Src sp)) \<longrightarrow> (\<forall> t' m'. t = t' -+- s \<longrightarrow> P snid' p' t' m' \<longrightarrow> srcs_to_trg P su snid snid' p' t' m')) \<Longrightarrow> srcs_to_trg P su snid nid p t m"

thm graph.path_weight_refl


lemma graph_induct:
  assumes G: "Graph.graph weights"
    and "S \<inter> V = {}"
  shows
    "(\<forall> V. (\<forall> l' \<in> V. \<forall> l. weights l l' \<noteq> {}\<^sub>A \<longrightarrow> l \<in> S \<union> V) \<longrightarrow> P V) \<Longrightarrow>
   (\<forall> V l l'. l \<notin> S \<union> V \<longrightarrow> l' \<in> V \<longrightarrow> weights l l' \<noteq> {}\<^sub>A \<longrightarrow> P (insert l V) \<longrightarrow> P V) \<Longrightarrow>
   P V"
  using assms(2) apply -
  apply (induct "card (UNIV - V)" arbitrary:  V)
  subgoal for V
    apply (subgoal_tac "V = UNIV")
    subgoal
      by clarsimp
    subgoal
      by auto
    done
  subgoal for n V
    apply (cases "(\<forall> l' \<in> V. \<forall> l. weights l l' \<noteq> {}\<^sub>A \<longrightarrow> l \<in> S \<union> V)")
    subgoal
      by metis
    subgoal premises prems
      using prems(6) apply -
      apply clarsimp
      subgoal for l' l
        using prems(1,2) apply -
        apply (drule meta_spec[of _ "insert l V"])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
        using prems(3) apply fast
        apply (drule meta_mp)
        using prems(4) apply fast
        apply (rule prems(4)[rule_format, of l])
           apply (auto simp add: prems(5))
        done
      done
    done
  done

lemma graph_induct':
  assumes G: "Graph.graph weights"
    and "S \<inter> V = {}"
  shows
    "(\<forall> V. (\<forall> l' \<in> V. \<forall> l. weights l l' \<noteq> {}\<^sub>A \<longrightarrow> l \<in> S \<union> V) \<longrightarrow> P V) \<Longrightarrow>
   (\<forall> V l l'. l \<notin> S \<union> V \<longrightarrow> l' \<in> V \<longrightarrow> weights l l' \<noteq> {}\<^sub>A \<longrightarrow> P (insert l V) \<longrightarrow> P V) \<Longrightarrow>
   P V"
  oops

lemma
  "\<not> srcs_to_trg P su nid nid' p t m \<Longrightarrow>
  (\<forall> p' s nid'' p''. s \<in>\<^sub>A graph.path_weight su (Loc nid (Src p')) (Loc nid'' (Trg p')) \<longrightarrow> \<not> (\<exists> t' m. t = t' -+- s))"
  oops

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
                    inter := operator_state.inter (os nid) @ concat (map (\<lambda>p. map (\<lambda>os. (p, os, - 1)) (drops p)) enum_class.enum), nfron := V\<rparr>)))
         (pt_tr sg))
       (Loc nid' lp))
     t")
               defer
              subgoal premises prems' for lp p'' t' m' nid'' n n'
                using prems'(3-4,6-)
                apply -
                apply(induction "(card {t. t \<le> t' \<and> (\<exists> p m nid. (p, t, m) \<in> set (consu (os nid)))},Produces.dataflow_topology.weight' (summ sg) (-+-) t' (Loc nid'' (Trg p'')))" arbitrary: p'' t' m' nid'' n n' rule: less_induct)
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
                            using frontier_less_equal_iff2 apply auto
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
                                      apply clarsimp
                                      apply (elim disjE)
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
                                      subgoal for t1
                                        apply clarsimp
                                          (*     apply(drule sym[of t]; simp) *)
                                        subgoal for t1' p1 s1 m1
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
                                                by(rule add_increasing; simp)
                                              subgoal
                                                apply(subgoal_tac "t1' -+- s1 \<in> {t. t \<le> t1' -+- s1 \<and> (\<exists>p m nid. (p, t, m) \<in> set (consu (os nid)))}")
                                                 defer 
                                                subgoal
                                                  by auto
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
                                            by (metis add.commute dataflow_topology_from_tree.followed_by_summary)
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
                  apply clarsimp
                  apply (elim disjE)
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
                  subgoal for t'
                    apply clarsimp
                    subgoal for t'' p''' s m''
                      apply (drule conjunct1[OF temp(5)[unfolded graph_summar_nt_def], rule_format])
                      apply clarsimp
                      subgoal for u
                        apply (drule sym[of t])
                        apply simp
                        apply (rule prems'(2)[of nid' _ _ _ u s])
                             apply assumption+
                        apply auto
                        done
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
                          apply clarsimp
                          apply (elim disjE)
                          subgoal for t'
                            apply (rule frontier_less_equal_trans[rotated])
                             apply assumption
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
                          subgoal for t'
                            apply clarsimp
                            subgoal for t'' p''' s m''
                              apply (drule conjunct1[OF temp(5)[unfolded graph_summar_nt_def], rule_format])
                              apply clarsimp
                              subgoal for u
                                apply (drule sym[of t])
                                apply simp
                                apply (rule frontier_less_equal_ifrontier_trans[OF D, of 0 "Loc nid' (Src p')", simplified])
                                subgoal
                                  by (meson D GS(2) dataflow_topology.axioms(1) graph_to_nxt_Some_alt path_weight_direct_0path temp(5))
                                apply (rule prems'(2)[of nid' _ _ _ u s])
                                     apply assumption+
                                apply auto
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

end



