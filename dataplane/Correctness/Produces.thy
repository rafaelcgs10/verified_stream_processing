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
  "outputs_at_target su (os(nid := (os nid)\<lparr> inter := A \<rparr>)) = outputs_at_target su os"
  "outputs_at_target su (os(nid := (os nid)\<lparr> produ := B \<rparr>)) = outputs_at_target su os"
  "outputs_at_target su (os(nid := (os nid)\<lparr> ocaps := C \<rparr>)) = outputs_at_target su os"
  "outputs_at_target su (os(nid := (os nid)\<lparr> input := D \<rparr>)) = outputs_at_target su os"
  "outputs_at_target su (os(nid := (os nid)\<lparr> inter := E \<rparr>)) = outputs_at_target su os"
  "outputs_at_target su (os(nid := (os nid)\<lparr> nfron := F \<rparr>)) = outputs_at_target su os"
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

find_consts  "('a \<times> 'b) set \<Rightarrow> bool" name: inj

(* 
lemma graph_to_nxt_Src_from_Trg:
  "(\<forall> nid p. card (Src_from_Trg su nid p) \<le> 1) \<Longrightarrow>
   (\<forall> nid p. card (Trg_from_Src su nid p) \<le> 1) \<Longrightarrow>
   graph_to_nxt su ((nid' :: 'nid :: enum), (p' :: 'p :: enum)) = Some (nid :: 'nid, p :: 'p) \<longleftrightarrow> Src_from_Trg su nid p = {(nid', p' :: 'p)}"
  unfolding graph_to_nxt_def Src_from_Trg_def
  apply (auto simp add: card_eq_Suc_0_ex1 le_eq_less_or_eq)
  subgoal for nid p
    by (metis (mono_tags, lifting) find_SomeD(1) is_empty_antichain_simp old.prod.case old.prod.inject)
 *)

lemma eq_singletonD:
  "{x. P x} = {x} \<Longrightarrow> P x"
  by auto

lemma in_op_conn_graph_to_nxt_iff:
  "single_valued (op_conn su) \<Longrightarrow>
   graph_to_nxt su (nid, p) = Some (nid', p') \<longleftrightarrow> ((nid, p), nid', p') \<in> op_conn su"
  unfolding graph_to_nxt_def op_conn_def
  apply (auto simp add: is_empty_antichain_iff split: prod.splits)
  subgoal
    apply (auto simp add: single_valued_def dest!: find_SomeD' split: prod.splits)
    done
  subgoal
    apply (rule find_Some_singleton)
    apply (auto simp add: single_valued_def split: prod.splits)
    done
  done

lemma graph_to_nxt_not_Ex_op_conn[simp]:
  "graph_to_nxt su (nid, p) = None \<longleftrightarrow>
   \<not> (\<exists> nid' p'. ((nid, p), nid', p') \<in> op_conn su)"
  unfolding graph_to_nxt_def op_conn_def
  apply (auto simp add: is_empty_antichain_iff find_None_iff dest!: find_SomeD' split: prod.splits)
  done

lemma
    "outputs_at_target su (os((nid :: 'n :: enum) := (os nid)\<lparr> outpu := (\<lambda>(p :: 'p). oputs p) \<rparr>)) (nid', p') =
     (let S = {p''. su (Loc nid (Src p'')) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A} in if S \<noteq> {} then oputs (Set.the_elem S) else outputs_at_target su os (nid', p'))"
  unfolding outputs_at_target_def
  apply (clarsimp split: prod.splits if_splits)
  subgoal for a
    unfolding  le_eq_less_or_eq
    apply (auto simp add: card_eq_0_iff card_1_singleton_iff)
    subgoal for p nid'
      apply hypsubst_thin
      apply (rule FalseE)
      oops

lemma
  "single_valued ((op_conn su)\<inverse>) \<Longrightarrow>
   summ sg (Loc nid'' (Src p'')) (Loc nid' (Trg p')) \<noteq> {}\<^sub>A \<Longrightarrow>
   the_elem {(nid'', p''). ((nid'', p''), nid', p') \<in> op_conn (summ sg)} = (nid, p) \<Longrightarrow>
   ((nid, p), nid', p') \<in> op_conn su"
  unfolding graph_to_nxt_def op_conn_def the_elem_def
  apply (auto simp add: single_valued_def dest!: split: prod.splits)
  subgoal
    oops


lemma dataplane_tracker_inv_produces_drops:
  fixes drops :: "'p :: {enum,linorder} \<Rightarrow> 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot} list"
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
     | Loc nid' (Trg p') \<Rightarrow>  caps l + zmset (map snd (filter (\<lambda> (p'', _, _). (graph_to_nxt (summ sg)) (nid, p'') = Some (nid', p')) produs)))"])
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
               apply (auto split: prod.splits simp add: op_conn_def )
              subgoal
                apply (drule GS(8)[unfolded op_conn_def single_valued_def, simplified, rule_format])
                 apply assumption
                apply auto
                apply hypsubst_thin
                apply (subst (asm) the_elem_image_unique[where f=id, simplified])
                  apply blast
                 apply clarsimp
                using GS(8)[unfolded op_conn_def single_valued_def, simplified, rule_format] apply blast
                apply auto
                done
              subgoal
                apply (subst (asm) the_elem_image_unique[where f=id, simplified])
                  apply blast
                 apply clarsimp
                using GS(8)[unfolded op_conn_def single_valued_def, simplified, rule_format] apply blast
                apply auto
                done
              done
            apply simp
            done
          subgoal
            apply (subst filter_False)
             apply simp_all
            subgoal
              apply (auto split: prod.splits simp add: op_conn_def )
              apply (subst (asm) the_elem_image_unique[where f=id, simplified])
                apply blast
               apply clarsimp
              using GS(8)[unfolded op_conn_def single_valued_def, simplified, rule_format] apply blast+
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
          apply (auto simp add:  c_pts_change_multiplicities split: location.splits port.splits; hypsubst_thin)
          subgoal for nid' p'
          




end