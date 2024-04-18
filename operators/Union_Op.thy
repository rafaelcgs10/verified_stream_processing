theory Union_Op
  imports
    "../Watermarked_Stream"
    "../Llists_Processors"
    "../Sum_Order"
    "../Antichain"
    "HOL-Library.Code_Lazy"
begin

section \<open>union_op\<close>

(* FIXME: move me *)
lemma monotone_subset:
  "monotone lxs WM1 \<Longrightarrow>
   WM2 \<subseteq> WM1 \<Longrightarrow>
   monotone lxs WM2"
  apply (coinduction arbitrary: lxs WM1 WM2 rule: monotone.coinduct)
  apply (erule monotone.cases)
    apply auto
  done

definition "producible (wm::_::order) WM = (\<exists> wm' \<in> WM. wm \<le> case_sum Inr Inl (wm'::'a + ('a::order)))"
definition "unproduced_watermarks WM = {(wm::_::order) \<in> WM. \<not> producible wm WM}"

lemma producible_empty[simp]:
  "\<not> producible wm {}"
  unfolding producible_def
  apply auto
  done

lemma producible_unionI[intro]:
  "producible wm A \<or> producible wm B \<Longrightarrow>
   producible wm (A \<union> B)"
  unfolding producible_def
  apply auto
  done

lemma producible_unionE:
  "producible wm (A \<union> B) \<Longrightarrow>
   producible wm A \<or> producible wm B"
  unfolding producible_def
  apply auto
  done

lemma unproduced_watermarks_unproduced_watermarks_simp[simp]:
  "unproduced_watermarks (unproduced_watermarks WM) = unproduced_watermarks WM"
  unfolding unproduced_watermarks_def producible_def
  by auto

lemma not_in_unproduced_watermarks:
  "wm \<notin> unproduced_watermarks WM \<Longrightarrow>
   wm \<notin> WM \<or> (wm \<in> WM \<and> producible wm WM)"
  unfolding unproduced_watermarks_def producible_def
  apply  auto
  done

lemma in_unproduced_watermarks:
  "wm \<in> WM \<Longrightarrow>
   \<not> producible wm WM \<Longrightarrow>
   wm \<in> unproduced_watermarks WM"
  unfolding unproduced_watermarks_def producible_def
  apply auto
  done

lemma is_producible:
  "wm \<in> WM \<Longrightarrow>
   wm \<notin> unproduced_watermarks WM \<Longrightarrow> 
   producible wm WM"
  unfolding unproduced_watermarks_def producible_def
  apply auto
  done

lemma in_unproduce_watermarks_2:
  "\<forall>wm' \<in> WM. \<not> wm \<le> (case_sum Inr Inl wm') \<Longrightarrow>
   wm \<le> wm' \<Longrightarrow>
   wm' \<in> WM \<Longrightarrow>
   wm' \<in> unproduced_watermarks WM"
  unfolding unproduced_watermarks_def producible_def
  apply auto
  done

lemma unproduced_watermarks_not_producible[simp]:
  "\<forall>wm\<in>unproduced_watermarks WM. \<not> producible wm WM"
  unfolding unproduced_watermarks_def producible_def
  apply auto
  done

lemma in_unproduced_watermarks_3:
  "maximal_complete WM \<Longrightarrow>
   \<not> producible wm (maximal_antichain_set WM) \<Longrightarrow>
   wm \<in> unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def producible_def maximal_antichain_set_def maximal_complete_def
  apply simp
  apply (smt (verit) Inl_leq Inr_leq dual_order.trans less_eq_sum.cases old.sum.simps(5) old.sum.simps(6))
  done

lemma in_unproduced_watermarks_union:
  "wm' \<in> unproduced_watermarks (WM' \<union> WM) \<Longrightarrow>
   wm' \<in> unproduced_watermarks WM' \<or> wm' \<in> unproduced_watermarks WM"
  unfolding unproduced_watermarks_def producible_def
  apply auto
  done

lemma in_not_in_unproduced_watermarks_insert:
  "t' \<in> unproduced_watermarks (insert wm WM) \<Longrightarrow>
   t' \<notin> unproduced_watermarks WM \<Longrightarrow>
   t' = wm"
  unfolding unproduced_watermarks_def producible_def maximal_antichain_set_def maximal_complete_def
  apply auto
  done

lemma producible_insert_same[simp]:
  "producible wm (insert wm WM) \<longleftrightarrow> producible wm WM"
  unfolding producible_def
  apply (intro iffI)
   apply (simp_all split: sum.splits)
  done

lemma producible_not_in_unproduced_watermarks:
  "producible wm WM \<Longrightarrow>
  wm \<notin> unproduced_watermarks WM"
  by force

lemma unproduced_watermarks_insert_2:
  "\<not> producible wm WM \<Longrightarrow>
   unproduced_watermarks (insert wm WM) = insert wm (unproduced_watermarks {wma \<in> WM. \<not> producible wma (insert wm WM)})"
  unfolding unproduced_watermarks_def producible_def
  apply (auto split: sum.splits)
  done

lemma producible_union[simp]:
  "producible wm (A \<union> B) = producible wm A \<or> producible wm B"
  unfolding producible_def
  apply auto
  done

lemma not_producible_union:
  "(\<not> producible wm (A \<union> B)) \<Longrightarrow> (\<not> producible wm A) \<and> (\<not> producible wm B)"
  unfolding producible_def
  apply simp
  done

lemma producible_insert_simp[simp]:
  "producible wm' (insert wm WM) \<longleftrightarrow> producible wm' WM \<or> wm' \<le> (case_sum Inr Inl wm)"
  unfolding producible_def
  apply auto
  done

lemma producible_subset:
  "producible wm WM' \<Longrightarrow>
   WM' \<subseteq> WM \<Longrightarrow>
   producible wm WM"
  unfolding producible_def
  apply auto
  done

lemma producible_maximal_antichain_set[simp]:
  assumes "maximal_complete WM"
  shows "producible wm (maximal_antichain_set WM) \<longleftrightarrow> producible wm WM"
proof -
  have "producible wm WM"
    if "producible wm (maximal_antichain_set WM)"
    using that assms
    unfolding producible_def maximal_antichain_set_def maximal_complete_def
    apply (simp split: sum.splits)
    using  sum.exhaust apply metis
    done
  moreover have "producible wm (maximal_antichain_set WM)"
    if "producible wm WM"
    using that assms
    unfolding producible_def maximal_antichain_set_def maximal_complete_def
    apply (simp split: sum.splits)
    apply (elim bexE)
    subgoal for wm'
      apply (drule bspec[of _ _ wm'])
       apply simp
      apply (elim bexE)
      subgoal for wm''
        apply (rule exI[of _ wm''])
        apply (smt (verit, ccfv_threshold) Inl_Inr_False less_eq_sum.cases order.trans sum_simps(10) sum_simps(9))
        done
      done
    done
  ultimately show ?thesis
    by (intro iffI conjI)
qed

lemma not_producible_maximal_antichain_set[simp]:
  "maximal_complete WM \<Longrightarrow>
   (\<not> producible wm (maximal_antichain_set WM)) \<longleftrightarrow> \<not> producible wm WM"
  using producible_maximal_antichain_set by blast

lemma unproduced_watermarks_conj_elim[simp]:
  "unproduced_watermarks {x \<in> WM. \<not> producible x WM \<and> P x} =
   {x \<in> unproduced_watermarks WM. P x}"
  unfolding unproduced_watermarks_def producible_def
  apply (auto split: sum.splits)
  done

lemma in_unproduced_watermarks_5:
  "\<not> wm' \<le> case_sum Inr Inl wm \<Longrightarrow>
   wm' \<in> unproduced_watermarks WM \<Longrightarrow>
   wm' \<in> unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def producible_def
  apply (auto split: sum.splits)
  done


lemma in_unproduced_watermarks_eq_not_prodible:
  "wm \<in> unproduced_watermarks WM \<longleftrightarrow> (\<not> producible wm WM \<and> wm \<in> WM)"
  unfolding unproduced_watermarks_def
  apply auto
  done

lemma unproduced_watermarks_insert_3[simp]:
  "{x. x = wm \<and> \<not> producible x (insert wm WM)} \<union> {x \<in> unproduced_watermarks WM. \<not> producible x (insert wm WM)} =
   unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def
  apply (auto 2 1)
  done

lemma unproduced_watermarks_insert_insert:
  "maximal_complete WM \<Longrightarrow>
   \<not> producible wm (maximal_antichain_set (insert wm WM)) \<Longrightarrow>
   \<forall>x\<in>unproduced_watermarks WM. \<not> producible x (maximal_antichain_set (insert wm WM)) \<Longrightarrow>
   insert wm (unproduced_watermarks WM) = unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def
  apply simp
  using producible_insert_same producible_insert_simp apply blast
  done

primcorec union_op  where
  "union_op buf1 buf2 = Logic (\<lambda> ev. case ev of
      Data tt d \<Rightarrow>
        let t = (case_sum id id) tt in
        (union_op buf1 buf2, [Data t d])
    | Watermark tt \<Rightarrow>
        let buf1' = tt#buf1 in
        let buf2' = maximal_antichain_set (insert tt buf2) in
        let dW = {wm \<in> set buf1'. producible wm buf2'} in
        (union_op ([wm \<leftarrow> buf1'. wm \<notin> dW]) buf2',
         map (case_sum Watermark Watermark) [wm \<leftarrow> buf1'. wm \<in> dW])) LNil"

lemma set_aux_simp[simp]:
  "{x. x = y \<or> P x} = insert y {x. P x}"
  apply auto
  oops

lemma produce_inner_union_monotone_Inl_Data:
  assumes "produce_inner (union_op buf1 buf2, lxs) = Some (Inl (op, Data t d, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "monotone lxs WM"
    and "buf2 = maximal_antichain_set WM"
    and "set buf1 = unproduced_watermarks WM"
    and "maximal_complete WM"
  shows "wms xs = {} \<and>
   monotone (llist_of (Data t d#xs)) (Inl -` (WM - set buf1) \<union> Inr -` (WM - set buf1)) \<and>
   (\<forall> wm \<in> set buf1. \<not> producible wm (set buf1)) \<and>
   (\<exists> n buf1' buf2'. lxs' = ldropn n lxs \<and> 0 < n \<and>
     monotone lxs' ((Watermark -` lset (ltake n lxs)) \<union> WM) \<and>
     buf2' = maximal_antichain_set ((Watermark -` lset (ltake n lxs)) \<union> buf2) \<and>
     buf1' = ((rev (List.map_filter (case_event (\<lambda> _ _. None)
               (\<lambda> wm . Some wm)) 
               ((list_of (ltake n lxs))))) @ buf1) \<and>
     op = (union_op buf1' buf2') \<and>
    (\<forall> wm \<in> Watermark -` lset (ltake n lxs). \<not> producible wm (Watermark -` lset (ltake n lxs) \<union> WM)) \<and> 
    (\<forall> wm \<in> set buf1. \<not> producible wm (Watermark -` lset (ltake n lxs) \<union> WM)))"
  using assms proof (induct ?P ?R arbitrary: WM buf1 buf2 lxs xs lxs' op t d  rule: produce_inner_alt[consumes 1])
  case (produces h xs lxs lxs' op' buf1 buf2 WM)
  then show ?case apply -
    apply (simp split: sum.splits event.splits)
    subgoal
      apply (intro conjI)
      subgoal
        apply (erule LConsData)
        apply clarsimp
        apply (rule LConsL)
         apply (intro ballI)
         apply simp
         apply (smt (verit, del_insts) Inl_leq dual_order.trans not_in_unproduced_watermarks producible_def sum.case_eq_if sum.collapse(1) sum_simps(10) sum_simps(11))
        using monotone.LNil apply blast
        done
      subgoal
        apply (rule exI[of _ 1])
        apply (elim conjE)
        apply hypsubst_thin
        apply (auto simp add: ltake_enat_0 append_eq_Cons_conv map_filter_simps split: sum.splits event.splits if_splits)
        done
      done
    subgoal
      apply (erule LConsData)
      apply clarsimp
      apply (intro conjI)
      subgoal
        apply (rule LConsL)
         apply (intro ballI)
         apply simp
         apply (smt (verit) Inl_Inr_False Inl_inject Inl_leq Inr_leq in_unproduce_watermarks_2 less_eq_sum.cases sum.case_eq_if sum.collapse(2))
        using monotone.LNil apply blast
        done
      subgoal
        apply (rule exI[of _ 1])
        apply hypsubst_thin
        apply (auto simp add: ltake_enat_0 append_eq_Cons_conv map_filter_simps split: sum.splits event.splits if_splits)
        done
      done
    done
next
  case (no_production h lxs op' buf1 buf2 xs lxs' op t d WM)
  then show ?case 
    apply -
    apply (simp add: filter_empty_conv split: if_splits event.splits; (elim conjE)?; hypsubst_thin) 
    subgoal for wm
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm WM"])
      apply (drule meta_mp)
       apply (rule arg_cong2[where f=union_op])
        apply simp
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      subgoal
        by (simp add: unproduced_watermarks_insert_insert)
      apply (drule meta_mp)
       apply simp
      apply (elim conjE exE; hypsubst_thin)
      subgoal premises prems for n
        apply (intro conjI)
        subgoal
          using prems(6) apply simp
          done
        subgoal
          using prems(7) apply -
          apply (rule monotone_subset)
           apply assumption
          apply (intro conjI Set.subsetI)
          apply (metis Diff_iff Un_iff insert_iff not_in_unproduced_watermarks producible_insert_simp unproduced_watermarks_not_producible vimage_eq)
          done
        subgoal 
          apply (rule exI[of _ "Suc n"])
          apply (intro conjI)
               apply simp_all
          subgoal
            using prems(9) apply -
            apply (rule monotone_subset)
             apply assumption
            apply auto
            done
          subgoal
            using prems(1,2,3,4,5,6) apply -
            subgoal
              apply (rule arg_cong2[where f=union_op])
              subgoal
                apply (auto simp add: map_filter_simps)
                done
              subgoal
                using maximal_antichain_set_union_aux2 by blast
              done
            done
          subgoal
            by (metis Un_insert_right in_unproduced_watermarks_3 not_producible_maximal_antichain_set prems(10) prems(11) prems(3) prems(4) producible_insert_simp)
          subgoal
            by (metis Un_insert_right in_unproduced_watermarks_5 prems(11) prems(5) producible_insert_simp)
          done
        done
      done
    done
qed

lemma produce_inner_union_monotone_Inl_Watermark:
  assumes "produce_inner (union_op buf1 buf2, lxs) = Some (Inl (op, Watermark wm, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "monotone lxs WM"
    and "buf2 = maximal_antichain_set WM"
    and "set buf1 = unproduced_watermarks WM"
    and "maximal_complete WM"
  shows "monotone (llist_of (Watermark wm#xs)) (Inl -` (WM - set buf1) \<union> Inr -` (WM - set buf1)) \<and>
   (\<forall> wm \<in> set buf1. \<not> producible wm (set buf1)) \<and>
   (\<exists> n buf1' buf2'. lxs' = ldropn n lxs \<and> 0 < n \<and>
     monotone lxs' ((Watermark -` lset (ltake n lxs)) \<union> WM) \<and>
     buf2' = maximal_antichain_set ((Watermark -` lset (ltake n lxs)) \<union> buf2) \<and>
     buf1' = filter (\<lambda> wm. \<not> producible wm buf2') ((rev (List.map_filter (case_event (\<lambda> _ _. None)
               (\<lambda> wm . Some wm)) 
               ((list_of (ltake n lxs))))) @ buf1) \<and>
     op = (union_op buf1' buf2') \<and>
    (\<forall> wm \<in> Watermark -` lset (ltake (n-1) lxs). \<not> producible wm (Watermark -` lset (ltake (n-1) lxs) \<union> WM)) \<and> 
    (\<forall> wm \<in> set buf1. \<not> producible wm (Watermark -` lset (ltake (n-1) lxs) \<union> WM)) \<and>
    wms (Watermark wm#xs) = Inl -` {wm \<in> Watermark -` lset (ltake n lxs) \<union> set buf1. producible wm buf2'} \<union> Inr -` {wm \<in> Watermark -` lset (ltake n lxs) \<union> set buf1. producible wm buf2'})"
  using assms proof (induct ?P ?R arbitrary: WM buf1 buf2 lxs wm xs lxs' op  rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply -
    apply (simp add: filter_empty_conv split: if_splits event.splits; (elim conjE)?; hypsubst_thin) 
    subgoal for wm'
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule arg_cong2[where f=union_op])
        apply simp
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      subgoal
        by (simp add: unproduced_watermarks_insert_insert)
      apply (drule meta_mp)
       apply simp
      apply (elim conjE exE)
      subgoal premises prems for n
        apply (intro conjI)
        subgoal
          apply (rule monotone_subset)
          using prems(6) apply -
           apply assumption
          apply simp
          apply (smt (verit, del_insts) Diff_iff UnCI in_not_in_unproduced_watermarks_insert insertCI not_in_unproduced_watermarks prems(4) subsetI vimageE vimageI)
          done
        subgoal 
          using prems(7) apply simp
          apply (rule exI[of _ "Suc n"])
          apply (intro conjI)
                apply simp_all
          subgoal
            using prems(9,8) apply simp
            done
          subgoal
            using prems(7,10)
            apply hypsubst_thin
            apply (auto 2 1 simp add: map_filter_simps)
            done
          subgoal
            using prems(8,11) apply simp
            apply (cases n)
             apply simp_all
            using in_unproduced_watermarks_3 prems(12) prems(3) prems(4) by fastforce
          subgoal
            using prems(8,12) apply simp
            apply (cases n)
             apply simp_all
            subgoal
              using in_unproduced_watermarks_5 prems(5) by blast
            done
          subgoal
            using prems(8,13,4) 
            apply (simp add: map_filter_simps)
            apply (intro conjI Set.equalityI Set.subsetI)
             apply simp_all
            subgoal
              using in_not_in_unproduced_watermarks_insert by blast
            subgoal
              by (meson in_unproduced_watermarks_eq_not_prodible insert_iff prems(5) producible_insert_simp sum_simps(15))
            done
          done
        done
      done
    done
next
  case (produces h xs lxs lxs' op' buf1 buf2 wm WM)
  then show ?case 
    apply -
    apply hypsubst_thin
    apply (simp split: event.splits)
    apply (elim conjE; hypsubst_thin)
    apply (intro conjI)
    subgoal
      apply (auto 2 1 simp add:  monotone_all_Watermarks split: sum.splits event.splits if_splits)
      done
    subgoal
      apply (rule exI[of _ 1])
      apply (simp add: ltake_enat_0 split: event.splits if_splits sum.splits)
         apply (intro conjI impI allI )
      subgoal 
        apply (rule arg_cong2[where f=union_op])
        subgoal
          by (smt (verit, ccfv_SIG) filter_cong)
        subgoal
          using  producible_maximal_antichain_set by blast
        done
      subgoal
        apply hypsubst_thin
        apply simp
        using maximal_complete_insert producible_insert_same producible_maximal_antichain_set 
        apply fastforce
        done
      subgoal
        apply hypsubst_thin
        apply (intro conjI)
         apply simp_all
         apply (smt (verit, ccfv_SIG) filter_cong)
        apply fastforce
        done
      subgoal
        apply hypsubst_thin
        apply (intro conjI)
         apply (simp_all add: map_filter_simps map_eq_Cons_conv filter_eq_Cons_iff)
         apply (smt (verit, del_insts) filter_cong)
        apply (elim exE conjE disjE)
           apply simp_all
        apply hypsubst_thin
        apply (simp split: sum.splits)
        apply hypsubst_thin
        apply (intro conjI impI allI Set.equalityI Set.subsetI)
         apply simp_all
        subgoal  
          by fastforce
        subgoal
          by (metis Inl_Inr_False Un_iff insertE sum.simps(2) sum_simps(10))
        done
      subgoal
        apply hypsubst_thin
        apply (intro conjI)
         apply (simp_all add: map_filter_simps map_eq_Cons_conv filter_eq_Cons_iff)
         apply (smt (verit, del_insts) filter_cong)
        apply (elim exE conjE disjE)
           apply simp_all
        apply hypsubst_thin
        apply (simp split: sum.splits)
        apply hypsubst_thin
        apply (intro conjI impI allI Set.equalityI Set.subsetI)
         apply simp_all
        subgoal  
          by fastforce
        subgoal
          using Inl_leq by auto
        done
      done
    done
qed

lemma unproduced_simp:
  "{wm \<in> WM''. \<forall>wm'\<in>WM''. (\<forall>x1. wm' = Inl x1 \<longrightarrow> \<not> wm \<le> Inr x1) \<and> (\<forall>x2. wm' = Inr x2 \<longrightarrow> \<not> wm \<le> Inl x2)} =
   {wm \<in> WM''. \<forall>wm'\<in>WM''. \<not> wm \<le> (case wm' of Inl x \<Rightarrow> Inr x | Inr x \<Rightarrow> Inl x)}"
  oops
    (*   by (metis (mono_tags, opaque_lifting) old.sum.simps(5) old.sum.simps(6) sum.exhaust_sel sum.split_sel_asm)
 *)


lemma unproduced_watermarks_simp_aux[simp]:
  "maximal_complete (Watermark -` A \<union> WM) \<Longrightarrow>
   {x. (x = wm \<or> Watermark x \<in> A) \<and> \<not> producible x (maximal_antichain_set (insert wm (Watermark -` A \<union> WM)))} \<union>
   {x \<in> unproduced_watermarks WM. \<not> producible x (maximal_antichain_set (insert wm (Watermark -` A \<union> WM)))} =
   unproduced_watermarks (insert wm (Watermark -` A \<union> WM))"
  apply (subst (1 2) not_producible_maximal_antichain_set)
  unfolding unproduced_watermarks_def
   apply (simp_all split: sum.splits)
  apply auto
  done

(* FIXME: move me to soundness *)
lemma produce_inner_skip_n_productions_op_union_op_Inr:
  assumes "produce_inner (skip_n_productions_op (union_op buf1 bu2) n, lxs) = Some (Inr op)" (is "produce_inner ?P = Some ?R")
  shows "exit op = LNil"
  using assms apply (induct ?P ?R arbitrary: buf1 bu2 lxs n  rule: produce_inner_alt)
   apply (simp_all split: if_splits event.splits sum.splits)
        apply auto[1]
       apply fast
      apply fast
     apply (metis skip_n_productions_op_0)
    apply (smt (verit, best) skip_n_productions_op_0)
   apply (smt (verit, del_insts) skip_n_productions_op_0)
  apply auto
  done

lemma produce_union_op_monotone:
  assumes  "monotone stream_in WM"
    and "buf2 = maximal_antichain_set WM"
    and "set buf1 = unproduced_watermarks WM"
    and "maximal_complete WM"
    and "produce (union_op buf1 buf2) stream_in = stream_out"
  shows "monotone stream_out (Inl -` (WM - set buf1) \<union> Inr -` (WM - set buf1))"
  using assms proof (coinduction arbitrary: WM stream_in buf1 stream_out buf2 rule: strict_monotone_coinduct_strict_monotone_prepend_cong1)
  case (MONO WM' stream_in buf1 stream_out buf2)
  then show ?case 
  proof (cases rule: monotone.cases[OF MONO(1)])
    case (1 WM)
    from MONO this show ?thesis by simp
  next
    case (2 lxs wm WM'')
    from MONO this show ?thesis 
    proof (cases "produce_inner ((union_op buf1 (maximal_antichain_set WM'')), (LCons (Watermark wm) lxs))")
      case None
      from this MONO 2 show ?thesis 
        by (simp split: if_splits list.splits)
    next
      case (Some r)
      then show ?thesis 
      proof (cases r)
        case (Inl p)
        then show ?thesis 
        proof (cases p)
          case (fields op' x xs lxs')
          from this MONO 2 Some show ?thesis
          proof (cases x)
            case (Data t d)
            from this fields MONO 2 Some Inl show ?thesis 
              apply -
              apply (rule disjI2)
              apply (rule disjI2)
              apply hypsubst_thin
              apply (frule produce_inner_union_monotone_Inl_Data[where WM="WM''"])
                  apply simp
                 apply (rule refl)
                apply assumption+
              apply (elim conjE exE)
              apply hypsubst_thin
              apply (subst produce.code)
              apply (simp del: produce_LCons produce_inner_simps)
              subgoal for n
                apply (intro conjI)
                subgoal
                  by (meson LConsData)
                subgoal
                  apply (rule disjI1)
                  apply (rule monotone_prepend_cong_prepend)
                  subgoal
                    apply (cases n)
                     apply blast
                    subgoal for n'
                      apply (rule monotone_prepend_cong_base)
                      apply (simp del: produce_LCons produce_inner_simps)
                      apply (rule exI)+
                      apply (intro conjI)
                          prefer 5
                          apply (rule refl)
                      subgoal
                        apply (simp del: produce_LCons produce_inner_simps)
                        apply (intro conjI Set.equalityI Set.subsetI)
                         apply (simp_all del: produce_LCons produce_inner_simps)
                        subgoal
                          by (metis in_unproduced_watermarks_eq_not_prodible producible_unionI vimage_eq)
                        subgoal
                          by fastforce
                        done
                      subgoal
                        by blast
                      subgoal
                        apply (simp del: produce_LCons produce_inner_simps add: map_filter_simps)
                        apply (intro conjI Set.equalityI Set.subsetI)
                         apply (simp_all del: produce_LCons produce_inner_simps)
                        subgoal
                          by (metis Un_iff in_unproduced_watermarks_eq_not_prodible insertCI producible_insert_same producible_insert_simp vimage_eq)
                        subgoal
                          by (metis in_not_in_unproduced_watermarks_insert in_unproduced_watermarks_eq_not_prodible in_unproduced_watermarks_union vimageD)
                        done
                      subgoal
                        apply (rule maximal_complete_insert)
                        apply (subst Un_commute)
                        apply (rule maximal_complete_union_finite)
                        subgoal 
                          apply (rule finite_vimageI)
                           apply (rule lfinite_imp_finite_lset)
                           apply (meson enat_ord_code(4) lfinite_ltake)
                          apply (meson event.inject(2) inj_onI)
                          done
                        apply assumption
                        done
                      done
                    done
                  subgoal
                    by auto
                  done
                done
              done
          next
            case (Watermark wm')
            from this fields MONO 2 Some Inl show ?thesis
              apply -
              apply (rule disjI2)
              apply (rule disjI1)
              apply hypsubst_thin
              apply (frule produce_inner_union_monotone_Inl_Watermark[where WM="WM''"])
                  apply simp
                 apply (rule refl)
                apply simp
               apply force
              apply (elim conjE exE)
              apply (subst produce.code)
              apply (simp del: produce_LCons produce_inner_simps)
              subgoal for n 
                apply (rule disjI1)
                apply (rule monotone_prepend_cong_prepend)
                subgoal
                  apply (rule monotone_prepend_cong_base)
                  apply (simp del: produce_LCons produce_inner_simps)
                  apply (rule exI)+
                  apply (intro conjI)
                      prefer 5
                      apply (rule refl)
                  subgoal
                    apply hypsubst_thin
                    apply (simp del: produce_LCons produce_inner_simps flip: Un_insert_left)
                    apply (subst (1 2 3 4 5 6) producible_maximal_antichain_set)
                    subgoal
                      apply (subst Un_commute)
                      apply (rule maximal_complete_union_finite)
                       apply simp
                       apply (rule finite_vimageI)
                        apply (simp_all add: inj_def lfinite_imp_finite_lset)
                      done
                    subgoal
                      apply (subst Un_commute)
                      apply (rule maximal_complete_union_finite)
                       apply simp
                       apply (rule finite_vimageI)
                        apply (simp_all add: inj_def lfinite_imp_finite_lset)
                      done
                    subgoal premises prems
                      apply (intro conjI impI allI Set.equalityI Set.subsetI)
                       apply simp_all
                      using in_unproduced_watermarks_eq_not_prodible apply blast
                      using in_unproduced_watermarks_eq_not_prodible apply blast
                      done
                    done
                  subgoal
                    by simp
                  subgoal
                    apply hypsubst_thin
                    subgoal 
                      apply (simp  del: produce_LCons produce_inner_simps flip: Un_insert_left)
                      apply (subst (1 2) producible_maximal_antichain_set)
                      subgoal
                        apply (subst Un_commute)
                        apply (rule maximal_complete_union_finite)
                         apply (rule finite_vimageI)
                          apply (simp_all add: inj_def lfinite_imp_finite_lset)
                        done
                      subgoal
                        apply (intro Set.equalityI Set.subsetI)
                        subgoal
                          apply (simp del: produce_LCons produce_inner_simps)
                          apply (meson Un_iff in_unproduced_watermarks_eq_not_prodible vimage_eq)
                          done
                        subgoal
                          apply (simp del: produce_LCons produce_inner_simps)
                          apply (meson in_unproduced_watermarks_eq_not_prodible in_unproduced_watermarks_union vimageD)
                          done
                        done
                      done
                    done
                  subgoal
                    apply hypsubst_thin
                    subgoal
                      subgoal
                        apply (subst Un_commute)
                        apply (rule maximal_complete_union_finite)
                         apply (rule finite_vimageI)
                          apply (simp_all add: inj_def lfinite_imp_finite_lset)
                        done
                      done
                    done
                  done
                subgoal
                  by simp
                done
              done
          qed
        qed
      next
        case (Inr p)
        from this MONO 2 Some show ?thesis 
          apply -
          apply (rule disjI1)
          apply hypsubst_thin
          apply (frule produce_inner_skip_n_productions_op_union_op_Inr[where n=0, simplified])
          apply (subst produce.code)
          apply simp 
          done
      qed
    qed
  next
    case (3 WM'' t lxs' d)
    then show ?thesis 
    proof (cases "produce_inner ((union_op buf1 (maximal_antichain_set WM'')), (LCons (Data t d) lxs'))")
      case None
      from MONO this show ?thesis by force
    next
      case (Some r)
      then show ?thesis 
      proof (cases r)
        case (Inl p)
        then show ?thesis 
        proof (cases p)
          case (fields op' x xs lxs'')
          then show ?thesis 
          proof (cases x)
            case (Data t d)
            from this 3 Inl Some fields MONO show ?thesis 
              apply -
              apply hypsubst_thin
              apply (rule disjI2)+
              apply (frule produce_inner_union_monotone_Inl_Data[where WM=WM''])
                  apply (meson LConsL)
                 apply (rule refl)+
                apply simp
               apply fast
              apply (elim conjE exE)
              subgoal for n buf1' buf2'
                apply hypsubst_thin
                apply (simp del: produce_LCons produce_inner_simps)
                apply (intro conjI)
                subgoal
                  by (meson LConsData)
                subgoal
                  apply (rule disjI1)
                  apply (rule monotone_prepend_cong_prepend)
                  subgoal
                    apply (rule monotone_prepend_cong_base)
                    apply simp
                    apply (rule exI)+
                    apply (intro conjI)
                        prefer 5
                        apply (rule refl)
                    subgoal
                      apply (intro Set.equalityI Set.subsetI)
                      subgoal
                        apply (simp del: produce_LCons produce_inner_simps)
                        apply (metis is_producible producible_unionI vimageI2)
                        done
                      subgoal
                        apply (simp del: produce_LCons produce_inner_simps)
                        apply (meson in_unproduced_watermarks_eq_not_prodible in_unproduced_watermarks_union vimageE)
                        done
                      done
                    subgoal
                      by blast
                    subgoal
                      apply (intro Set.equalityI Set.subsetI)
                      subgoal
                        apply (simp del: produce_LCons produce_inner_simps)
                        apply (metis Un_iff in_unproduced_watermarks_eq_not_prodible vimage_eq)
                        done
                      subgoal
                        apply (simp del: produce_LCons produce_inner_simps)
                        apply (meson in_unproduced_watermarks_eq_not_prodible in_unproduced_watermarks_union vimageD)
                        done
                      done
                    subgoal
                      apply (subst Un_commute)
                      apply (rule maximal_complete_union_finite)
                       apply (metis List.finite_set enat_ord_code(4) lfinite_ltake set_list_of set_map_filter_case_event_Watermark)
                      apply simp
                      done
                    done
                  subgoal
                    by auto
                  done
                done
              done
          next
            case (Watermark wm)
            from this 3 fields MONO Some Inl show ?thesis by auto
          qed
        qed
      next
        case (Inr b)
        from this 3 MONO Some show ?thesis by auto
      qed
    qed
  qed
qed

subsection \<open>Soundness\<close> 
lemma produce_inner_union_op_Data:
  assumes  "produce_inner (union_op buf1 buf2, lxs) = Some (Inl (lgc', Data t d, xs, lzs))" (is "produce_inner ?P = Some ?R")
  shows "Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  using assms apply (induct ?P ?R arbitrary: buf1 buf2 lxs lgc' rule: produce_inner_alt[consumes 1])
   apply (auto split: event.splits if_splits sum.splits)
  done

lemma produce_inner_skip_n_productions_op_union_op_Data:
  assumes "produce_inner (skip_n_productions_op (union_op buf1 buf2) n, lxs) = Some (Inl (op', Data t d, xs, lzs))" (is "produce_inner ?P = Some ?R")
  shows "Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  using assms apply (induct ?P ?R arbitrary: n buf1 buf2 lxs op' t d lzs xs rule: produce_inner_alt[consumes 1])
   apply (simp split: event.splits if_splits sum.splits prod.splits)
  subgoal
    by blast
  subgoal
    by (metis skip_n_productions_op_0)
  subgoal
    by blast
  subgoal
    by blast
  subgoal
    by (smt (verit, best) skip_n_productions_op_0)
  subgoal
    by (smt (verit, best) skip_n_productions_op_0)
  subgoal
    apply (simp add: not_less nth_via_drop' split: sum.splits if_splits list.splits event.splits)
        apply hypsubst_thin
    subgoal
      by (metis Suc_le_eq bot_nat_0.not_eq_extremum diff_is_0_eq' diff_le_self drop0 event.inject(1) length_Cons length_drop less_Suc0 list.inject list.size(3))
    subgoal
      apply hypsubst_thin
      apply (drule nth_via_drop')
      apply auto
      done
    subgoal
      by (simp add: drop_map)
    subgoal
      by (metis (no_types, lifting) drop_Cons' drop_map event.distinct(1) list.inject map_case_sum_Watermark)
    subgoal
      by (metis (no_types, lifting) drop_Cons' drop_map event.distinct(1) list.inject map_case_sum_Watermark)
    done
  done

lemma produce_inner_union_op_Inr:
  assumes "produce_inner (union_op buf1 buf2, lxs) = Some (Inr op)" (is "produce_inner ?P = Some ?R")
  shows "exit op = LNil \<and> (\<forall> x \<in> lset lxs. \<not> is_Data x)"
  using assms apply (induct ?P ?R arbitrary: buf1 buf2 lxs op rule: produce_inner_alt)
   apply (auto split: if_splits event.splits sum.splits)
  done 

lemma skip_n_productions_op_union_op_Data_soundness:
  "produce (skip_n_productions_op (union_op buf1 buf2) n) lxs = LCons (Data t d) lzs \<Longrightarrow> 
   Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  apply (subst (asm) produce.code)
  apply (simp split: option.splits prod.splits sum.splits; hypsubst_thin)
   apply (simp add: produce_inner_skip_n_productions_op_union_op_Data)
  using produce_inner_skip_n_productions_op_union_op_Inr apply force
  done 

lemma union_op_Data_soundness:
  "Data t d \<in> lset (produce (union_op buf1 buf2) lxs) \<Longrightarrow> 
   Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  apply (subst (asm) lset_conv_lnth)
  apply simp
  apply (elim exE conjE)
  subgoal for n
    using skip_n_productions_op_union_op_Data_soundness
    apply (metis ldropn_Suc_conv_ldropn produce_skip_n_productions_op_correctness)
    done
  done 

subsection \<open>Completness\<close> 

lemma produce_union_op_Inl_completeness:
  "Data (Inl t) d \<in> lset lxs \<Longrightarrow>
   Data t d \<in> lset (produce (union_op buf1 buf2) lxs)"
  apply (subst (asm) lset_conv_lnth)
  apply simp
  apply (elim exE)
  subgoal for n
    apply (induct n arbitrary: t d lxs buf1 buf2)
    subgoal for t d lxs
      apply (subst produce.code)
      apply (simp split: option.splits)
      subgoal
        apply (cases lxs)
         apply auto
        done
      done
    subgoal for n t d lxs buf1 buf
      apply (cases lxs)
       apply (simp_all add: Suc_ile_eq split: event.splits sum.splits)
      done
    done
  done

lemma produce_union_op_Inr_completeness:
  "Data (Inr t) d \<in> lset lxs \<Longrightarrow>
   Data t d \<in> lset (produce (union_op buf1 buf2) lxs)"
  apply (subst (asm) lset_conv_lnth)
  apply simp
  apply (elim exE)
  subgoal for n
    apply (induct n arbitrary: t d lxs buf1 buf2)
    subgoal for t d lxs
      apply (subst produce.code)
      apply (simp split: option.splits)
      subgoal
        apply (cases lxs)
         apply auto
        done
      done
    subgoal for n t d lxs buf1 buf
      apply (cases lxs)
       apply (simp_all add: Suc_ile_eq split: event.splits sum.splits)
      done
    done
  done

lemma lfinite_produce_union_op:
  "lfinite stream_in \<Longrightarrow>
   produce (union_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   lfinite stream_out"
  apply hypsubst_thin
  apply (induct stream_in arbitrary: buf1 buf2 rule: lfinite.induct)
  subgoal
    by simp
  subgoal for xs x buf1 buf2
    apply(simp split: event.splits list.splits option.splits sum.splits; hypsubst_thin?)
    done
  done

lemma producible_buf_produce_inner_union_op_None_False:
  "Watermark wm \<in> lset lxs \<Longrightarrow>
   producible wm buf2 \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   produce_inner (union_op buf1 buf2, lxs) = None \<Longrightarrow>
   False"
  apply (induct lxs arbitrary: buf1 buf2  rule: lset_induct)
  subgoal for xs buf1 buf2 
    apply (subst (asm) produce_inner.simps)
    apply (auto split: list.splits if_splits)
    done
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (simp split: list.splits if_splits event.splits)
    apply (drule meta_spec)+
    apply (drule meta_mp)
     defer
     apply (drule meta_mp)
      defer
      apply (drule meta_mp)
       apply assumption
      apply simp
    using maximal_complete_insert not_producible_maximal_antichain_set producible_insert_simp apply blast
    apply (metis (mono_tags, lifting) dual_order.refl maximal_antichain_set_def maximal_complete_def mem_Collect_eq)
    done
  done

lemma produce_inner_union_None_not_producible_buffers:
  "maximal_complete buf2 \<Longrightarrow>
   produce_inner (union_op buf1 buf2, stream_in) = None \<Longrightarrow> \<forall>wm\<in>set buf1. \<not> producible wm buf2"
  apply (rule ccontr)
  apply simp
  apply (subst (asm) produce_inner.simps)
  apply (auto simp add: filter_empty_conv split: llist.splits event.splits if_splits list.splits)
  done

lemma produce_inner_union_op_invar_None:
  "produce_inner (union_op buf1 buf2, stream_in) = None \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   produce_inner (union_op buf1 (maximal_antichain_set buf2), stream_in) =
   produce_inner (union_op
     (rev (List.map_filter (case_event (\<lambda> _ _. None) Some) (list_of (ltake (enat n) stream_in))) @ buf1)
     (maximal_antichain_set (Watermark -` lset (ltake (enat n) stream_in) \<union> buf2)),
    ldropn n stream_in)"
  apply (induct n arbitrary: buf1 buf2 stream_in)
  subgoal for buf1 buf2 stream_in
    apply (auto simp add: produce_inner_union_None_not_producible_buffers enat_0 map_filter_simps(2))
    done
  subgoal for n buf1 buf2 stream_in
    apply (subst (asm) (4) produce_inner.simps)
    apply (simp del: produce_inner_simps add: filter_empty_conv map_filter_simps split: llist.splits event.splits list.splits if_splits)
    apply hypsubst_thin
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    apply (drule meta_mp)
    using maximal_complete_maximal_antichain_set apply blast
    apply (simp add:  map_filter_simps)
    done
  done

lemma find_producible_position:
  "Watermark wm \<in> lset lxs \<Longrightarrow>
   producible wm (Watermark -` lset lxs) \<Longrightarrow>
   \<exists> n. Watermark wm \<in> lset (ltake (enat n) lxs) \<and> producible wm (Watermark -` lset (ltake (enat n) lxs)) "
  unfolding producible_def
  apply (simp add: not_less order.order_iff_strict in_lset_conv_lnth split: sum.splits)
  apply (elim bexE conjE)
  apply (simp add: in_lset_conv_lnth)
  apply (elim exE conjE)
  subgoal for n wm' n'
    apply (cases "n < n'")
    subgoal
      apply (rule exI[of _ "Suc n'"])
      apply (intro conjI)
       apply (metis enat_ord_simps(2) less_Suc_eq lnth_ltake)
      apply (rule bexI[of _ wm'])
       apply simp_all
      apply (metis (no_types, lifting) enat_ord_simps(2) in_lset_conv_lnth lessI llength_ltake lnth_ltake min_def)
      done
    subgoal
      apply (simp add: not_less order.order_iff_strict)
      subgoal
        apply (rule exI[of _ "Suc n"])
        apply (intro conjI)
         apply (metis enat_ord_simps(2) lessI lnth_ltake)
        apply (rule bexI[of _ wm'])
         apply simp_all
        apply (metis (no_types, lifting) enat_ord_simps(2) in_lset_conv_lnth llength_ltake lnth_ltake min_def not_less_eq not_less_iff_gr_or_eq)
        done
      done
    done
  done

lemma union_op_maximal_complete:
  "maximal_complete buf2 \<Longrightarrow>
   union_op buf1 buf2 = union_op buf1 (maximal_antichain_set buf2)"
  apply (coinduction arbitrary:  buf1 buf2 rule: op.coinduct)
  apply (simp add: rel_fun_def rel_prod.simps split: event.splits)
  apply (intro allI conjI impI)
  subgoal for buf1 buf2 wm
    apply (intro exI conjI)
      apply (rule refl)
     apply (rule arg_cong2[where f=union_op])
      apply auto
    done
  subgoal for buf1 buf2 wm
    apply (intro exI conjI)
      apply (rule refl)
     apply (rule arg_cong2[where f=union_op])
      apply auto
    done
  subgoal
    by force
  done

lemma producible_stream_produce_inner_union_op_None_False:
  "Watermark wm \<in> lset stream_in \<Longrightarrow>
   produce_inner (union_op buf1 buf2, stream_in) = None \<Longrightarrow>
   producible wm (Watermark -` lset stream_in) \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   False"
  subgoal premises prems
    using prems apply -
    apply (subst (asm) union_op_maximal_complete)
     apply assumption
    apply (frule find_producible_position)
     apply assumption
    apply (elim exE conjE)
    subgoal for n
      apply (subst (asm) produce_inner_union_op_invar_None[where n=n])
      using prems(2) apply assumption
       apply meson
      apply (frule produce_inner_union_None_not_producible_buffers[rotated])
       defer
      subgoal
        apply simp
        apply (smt (verit, ccfv_threshold) List.finite_set Un_commute Un_iff Un_upper1 enat_ord_code(4) lfinite_ltake maximal_complete_union_finite producible_maximal_antichain_set producible_subset set_list_of set_map_filter_case_event_Watermark vimageI)
        done
      subgoal
        using maximal_complete_maximal_antichain_set by blast
      done
    done
  done

lemma produce_union_op_completeness_with_buffer:
  "Watermark x \<in> lset lxs \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   producible x buf2 \<Longrightarrow>
   (case_sum Watermark Watermark) x \<in> lset (produce (union_op buf1 buf2) lxs)"
  apply (induct lxs arbitrary: buf1 buf2 rule: lset_induct)
  subgoal for  buf1 buf2
    apply (subst produce.code)
    apply (auto split: option.splits)
    done
  subgoal for x' xs buf1 buf2
    apply (subst produce.code)
    apply (simp add: filter_empty_conv split: list.splits event.splits option.splits)
    apply (intro allI impI)
    apply (smt (z3) maximal_complete_insert maximal_complete_maximal_antichain_set not_Some_eq option.case(2) produce.code producible_buf_produce_inner_union_op_None_False producible_insert_simp producible_maximal_antichain_set)
    done
  done

lemma produce_union_op_completeness_with_stream:
  "z \<in> lset lxs \<Longrightarrow>
   z = Watermark y \<Longrightarrow>
   x \<le> (case y of Inl x \<Rightarrow> Inr x | Inr x \<Rightarrow> Inl x) \<Longrightarrow>
   Watermark x \<in> lset lxs \<or> x \<in> set buf1 \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   (case_sum Watermark Watermark) x \<in> lset (produce (union_op buf1 buf2) lxs)"
  apply (induct lxs arbitrary: buf1 buf2 rule: lset_induct)
  subgoal for xs buf1 buf2
    apply (simp add: filter_empty_conv split: list.splits option.splits)
    subgoal
      by (metis (no_types, lifting) image_eqI maximal_complete_insert maximal_complete_maximal_antichain_set mem_Collect_eq not_producible_maximal_antichain_set produce_union_op_completeness_with_buffer producible_insert_simp sum_simps(15))
    done
  subgoal for x' lxs buf1 buf2
    apply (simp add: filter_empty_conv split: list.splits option.splits sum.splits event.splits)
     apply (intro impI allI conjI)
    subgoal
      using sum_simps(12) by blast
    subgoal
      by auto
    subgoal
      using sum_simps(12) by blast
    subgoal
      by (metis (mono_tags, lifting) event.inject(2) imageI list.set_intros(2) maximal_complete_maximal_antichain_set mem_Collect_eq old.sum.simps(6) set_filter sum.simps(4))
    subgoal
      using sum_simps(12) by blast
    subgoal
      by (metis (mono_tags, lifting) Inl_Inr_False event.inject(2) imageI maximal_complete_maximal_antichain_set mem_Collect_eq old.sum.simps(6) set_filter)
    subgoal
      using sum_simps(12) by blast
    subgoal
      by (smt (verit, ccfv_SIG) event.inject(2) imageI list.set_intros(1) list.set_intros(2) maximal_complete_maximal_antichain_set mem_Collect_eq old.sum.simps(6) set_filter)
    subgoal
      using sum_simps(12) by blast
    subgoal
      by (smt (verit, ccfv_SIG) event.inject(2) imageI maximal_complete_maximal_antichain_set mem_Collect_eq old.sum.simps(6) set_filter)
    subgoal
      by (smt (verit) Inl_Inr_False event.inject(2) event.simps(4) filter_set image_iff less_eq_sum.cases list.set_intros(1) list.set_intros(2) maximal_complete_maximal_antichain_set mem_Collect_eq member_filter old.sum.simps(5))
    done
  done

lemma produce_inner_union_op_producible_produces_Inl:
  "produce_inner (union_op buf1 buf2, stream_in) = r \<Longrightarrow>
   \<not> lfinite stream_in \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   \<forall>wm. Watermark wm \<in> lset stream_in \<longrightarrow> producible wm (buf2 \<union> Watermark -` lset stream_in) \<Longrightarrow>
   \<exists> y. r = Some (Inl y)"
  apply (cases r)
  subgoal
    apply hypsubst_thin
    apply (cases stream_in)
     apply simp_all
    subgoal for x xs
      apply (subst (asm) (1) produce_inner.simps)
      apply (simp add: filter_empty_conv split: if_splits prod.splits list.splits event.splits llist.splits)
      apply (smt (z3) maximal_complete_insert producible_buf_produce_inner_union_op_None_False producible_def producible_insert_simp producible_stream_produce_inner_union_op_None_False producible_union union_op_maximal_complete vimage_eq)
      done
    done
  subgoal for y
    apply (cases y)
     apply simp_all
    subgoal
      by (metis surj_pair)
    subgoal
      using produce_inner_Some_Inr_lfinite by blast
    done
  done

lemma produce_inner_union_monotone_Inl_Data_2:
  assumes "produce_inner (union_op buf1 buf2, lxs) = Some (Inl (op, Data t d, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "maximal_complete buf2"
  shows "xs = [] \<and>
   (\<exists> n buf1' buf2'. lxs' = ldropn n lxs \<and> 0 < n \<and>
     buf2' = maximal_antichain_set ((Watermark -` lset (ltake n lxs)) \<union> buf2) \<and>
     buf1' = ((rev (List.map_filter (case_event (\<lambda> _ _. None)
               (\<lambda> wm . Some wm)) 
               ((list_of (ltake n lxs))))) @ buf1) \<and>
     op = (union_op buf1' buf2'))"
  using assms apply (induct ?P ?R arbitrary: buf1 buf2 lxs t d xs lxs' op rule: produce_inner_alt)
   prefer 2
  subgoal for h xs lxs lxs' op' buf1 buf2 t d
    apply simp
    apply (intro conjI)
    subgoal
      apply (auto 2 1 split: sum.splits event.splits)
      done
    subgoal
      apply (simp split: sum.splits event.splits)
      subgoal
        apply hypsubst_thin
        apply (rule exI[of _ 1])
        apply simp
        apply (smt (verit, del_insts) Un_commute append_self_conv2 event.simps(5) list_of_LNil lset_LNil ltake_eq_LNil_iff map_filter_empty map_filter_simps(2) rev_is_Nil_conv set_ConsD sup_bot.right_neutral union_op_maximal_complete vimage_empty zero_enat_def)
        done
      subgoal
        apply hypsubst_thin
        apply (rule exI[of _ 1])
        apply simp
        apply (smt (verit, del_insts) Un_commute append_self_conv2 event.simps(5) list_of_LNil lset_LNil ltake_eq_LNil_iff map_filter_empty map_filter_simps(2) rev_is_Nil_conv set_ConsD sup_bot.right_neutral union_op_maximal_complete vimage_empty zero_enat_def)
        done
      done
    done
  subgoal for h lxs op' buf1 buf2 t d xs lxs' op
    apply (simp add: filter_empty_conv split: if_splits event.splits; (elim conjE)?; hypsubst_thin) 
    subgoal for wm
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule arg_cong2[where f=union_op])
        apply simp
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply simp
      apply (elim conjE exE; hypsubst_thin)
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply (auto simp add: map_filter_simps)
        done
      done
    done
  done

lemma produce_inner_union_monotone_Inl_Watermark_2:
  "produce_inner oo = Some r \<Longrightarrow> 
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   oo = (union_op buf1 buf2, lxs) \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   (\<exists> n buf1' buf2' wm. lxs' = ldropn n lxs \<and> 0 < n \<and>
     buf2' = maximal_antichain_set ((Watermark -` lset (ltake n lxs)) \<union> buf2) \<and>
     buf1' = filter (\<lambda> wm. \<not> producible wm buf2') ((rev (List.map_filter (case_event (\<lambda> _ _. None)
               (\<lambda> wm . Some wm)) 
               ((list_of (ltake n lxs))))) @ buf1) \<and>
     op = (union_op buf1' buf2')) \<and>
   (\<forall> x \<in> set xs. \<not> is_Data x)"
  apply (induct oo r arbitrary: buf1 buf2 lxs x xs lxs' op  rule: produce_inner_alt[consumes 1])
    prefer 2
  subgoal for op h x xs lxs lxs' lgc' buf1 buf2 lxs'' xa xsa lxs'a opa
    apply (subst (asm) produce_inner.simps)
    apply simp
    apply (cases lxs'')
     apply simp_all
    apply (elim conjE; hypsubst_thin)
    apply (intro conjI)
     apply (rule exI[of _ 1])
     apply (simp add: split: event.splits if_splits; elim conjE; hypsubst_thin)
    subgoal for wm'
      apply (rule arg_cong2[where f=union_op])
      subgoal
        apply (auto simp add: maximal_antichain_set_single map_filter_simps split: sum.splits)
        done
      subgoal
        by (smt (verit, del_insts) Un_commute append_self_conv2 event.simps(5) list_of_LNil lset_LNil ltake_eq_LNil_iff map_filter_empty map_filter_simps(2) rev_is_Nil_conv set_ConsD sup_bot.right_neutral union_op_maximal_complete vimage_empty zero_enat_def)
      done
    subgoal for wm'
      apply (simp add: ltake_enat_0 maximal_antichain_set_single map_filter_simps split: sum.splits; hypsubst_thin)
       apply (metis (no_types, lifting) filter_cong)+
      done
    subgoal for wm'
      apply (simp add: ltake_enat_0 maximal_antichain_set_single map_filter_simps split: sum.splits; hypsubst_thin)
       apply (smt (verit, ccfv_SIG) filter_cong)+
      done
    subgoal
      apply (auto split: event.splits if_splits sum.splits)
      done
    done
  subgoal for op h lxs lgc' zs buf1 buf2 lxsa x xs lxs' opa
    apply (simp add: filter_empty_conv split: if_splits event.splits; (elim conjE)?; hypsubst_thin) 
    subgoal for wm'
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule arg_cong2[where f=union_op])
        apply simp
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (elim conjE exE)
      apply (intro conjI)
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply (auto simp add: map_filter_simps)
        done
      subgoal
        apply auto
        done
      done
    done
  apply auto
  done

lemma llength_produce_union_op_productive_lfinite:
  "llength (produce (union_op buf1 buf2) stream_in) \<le> enat n \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   \<forall>wm. Watermark wm \<in> lset stream_in \<longrightarrow> producible wm (buf2 \<union> Watermark -` lset stream_in) \<Longrightarrow>
   lfinite stream_in"
  apply (induct n arbitrary: buf1 buf2 stream_in)
  subgoal for buf1 buf2 stream_in
    apply (subst (asm)  produce.code)
    apply (simp split: option.splits sum.splits)
      apply (metis option.distinct(1) produce_inner_union_op_producible_produces_Inl)
    using enat_0 apply fastforce
    using produce_inner_Some_Inr_lfinite apply blast
    done
  subgoal for n buf1 buf2 stream_in
    apply (subst (asm) (2) produce.code)
    apply (simp split: option.splits sum.splits prod.splits)
      apply (metis llength_LNil produce_inner_None_produce_LNil zero_le)
    subgoal for _ _ op' _ x _ xs lxs'
      apply (cases x)
      subgoal for t d
        apply hypsubst_thin
        apply (drule produce_inner_union_monotone_Inl_Data_2)
         apply assumption
        apply (elim exE conjE)
        subgoal for n buf1' buf2'
          apply (drule meta_spec[of _ buf1'])
          apply (drule meta_spec[of _ buf2'])
          apply (drule meta_spec[of _ lxs'])
          apply (drule meta_mp)
          subgoal
            apply simp
            apply (metis eSuc_enat eSuc_ile_mono)
            done
          apply (drule meta_mp)
           apply force
          apply (drule meta_mp)
          subgoal
            apply hypsubst_thin
            apply simp
            apply (intro allI impI)
            subgoal for wm
              apply (drule spec[of _ wm])
              apply (drule mp)
               apply (meson in_lset_ldropnD)
              apply (rule producible_unionI)
              apply (subst producible_maximal_antichain_set)
               apply (subst Un_commute)
               apply (rule maximal_complete_union_finite)
                apply (metis List.finite_set enat_ord_code(4) lfinite_ltake set_list_of set_map_filter_case_event_Watermark)
               apply force
              apply (rule producible_unionE)
              apply (subgoal_tac "buf2 \<union> Watermark -` lset stream_in = Watermark -` lset (ltake (enat n) stream_in) \<union> buf2 \<union> Watermark -` lset (ldropn n stream_in)")
               apply simp
              apply (subst (2) Un_commute)
              apply (subst Un_assoc)
              using ltake_ldropn_merge_lset 
              apply (metis vimage_Un)
              done
            done
          using lfinite_ldropn apply blast
          done
        done
      subgoal for wm
        apply hypsubst_thin
        apply (drule produce_inner_union_monotone_Inl_Watermark_2)
            apply (rule refl)+
         apply assumption
        apply (elim exE conjE)
        subgoal for n buf1' buf2'
          apply (drule meta_spec[of _ buf1'])
          apply (drule meta_spec[of _ buf2'])
          apply (drule meta_spec[of _ lxs'])
          apply (drule meta_mp)
          subgoal
            apply (simp flip: eSuc_enat)
            apply (rule preorder_class.order.trans)
             defer
             apply assumption
            subgoal premises prems
              apply (cases xs)
               apply (simp_all add: llength_shift)
              using enat_le_plus_same(2) ile_eSuc order_trans apply blast
              done
            done
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          subgoal
            apply simp
            apply (intro allI impI)
            subgoal for wm
              apply (drule spec[of _ wm])
              apply (drule mp)
               apply (meson in_lset_ldropnD)
              apply (rule producible_unionI)
              apply (subst producible_maximal_antichain_set)
               apply (subst Un_commute)
               apply (rule maximal_complete_union_finite)
                apply (metis List.finite_set enat_ord_code(4) lfinite_ltake set_list_of set_map_filter_case_event_Watermark)
               apply force
              apply (rule producible_unionE)
              apply (subgoal_tac "buf2 \<union> Watermark -` lset stream_in = Watermark -` lset (ltake (enat n) stream_in) \<union> buf2 \<union> Watermark -` lset (ldropn n stream_in)")
               apply simp
              apply (subst (2) Un_commute)
              apply (subst Un_assoc)
              using ltake_ldropn_merge_lset 
              apply (metis vimage_Un)
              done
            done
          apply auto
          done
        done
      done
    subgoal
      using produce_inner_Some_Inr_lfinite by blast
    done
  done

lemma productive_not_lfinite_produce_union_op_aux:
  "lfinite lxs \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   lxs = produce (skip_n_productions_op (union_op buf1 buf2) n) stream_in \<Longrightarrow>
   \<forall>wm. Watermark wm \<in> lset stream_in \<longrightarrow> producible wm (buf2 \<union> Watermark -` lset stream_in) \<Longrightarrow>
   lfinite stream_in"
  apply (induct lxs arbitrary: buf1 buf2 stream_in n rule: lfinite_induct)
  subgoal for xs buf1 buf2 stream_in n
    apply simp
    apply hypsubst_thin
    apply (subst (asm) produce_skip_n_productions_op_correctness)
    apply simp
    subgoal
      using llength_produce_union_op_productive_lfinite 
      by blast
    done
  subgoal for lxs buf stream_in n
    apply hypsubst_thin
    by (metis lhd_LCons_ltl produce_skip_n_productions_op_LCons)
  done

lemma productive_produce_inner_union_op_produces_some:
  "\<forall>wm. Watermark wm \<in> lset stream_in \<longrightarrow> producible wm (buf2 \<union> Watermark -` lset stream_in) \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   \<exists>y. produce_inner (union_op buf1 buf2, stream_in) = Some y"
  by (meson not_Some_eq produce_inner_None_not_lfinite_aux produce_inner_union_op_producible_produces_Inl)

lemma produce_union_op_not_lfinite:
  "\<not> lfinite stream_in \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   \<forall>wm. Watermark wm \<in> lset stream_in \<longrightarrow> producible wm (buf2 \<union> Watermark -` lset stream_in) \<Longrightarrow>
   \<not> lfinite (produce (union_op buf1 buf2) stream_in)"
  by (metis productive_not_lfinite_produce_union_op_aux skip_n_productions_op_0)

lemma produce_union_op_completeness_Watermark_aux:
  "Watermark x \<in> lset lxs \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   producible x (buf2 \<union> Watermark -` lset lxs) \<Longrightarrow> 
   (case x of Inl x \<Rightarrow> Watermark x | Inr x \<Rightarrow> Watermark x) \<in> lset (produce (union_op buf1 buf2) lxs)"
  apply (drule producible_unionE)
  apply (elim disjE)
  using produce_union_op_completeness_with_buffer apply blast
  unfolding producible_def
  apply (elim bexE conjE)
  subgoal for wm'
    apply (rule produce_union_op_completeness_with_stream[where y=wm'])
        defer
        apply (rule refl)
       apply assumption
      apply simp_all
    done
  done

lemma produce_union_op_completeness_not_lfinite_Watermark:
  "Data t d \<in> lset stream_in \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   productive stream_in \<Longrightarrow>
   \<not> lfinite stream_in \<Longrightarrow>
   (\<forall> wm \<in> Watermark -` lset stream_in. producible wm (buf2 \<union> (Watermark -` lset stream_in))) \<Longrightarrow>
   \<exists> x \<ge> t . (case x of Inl x \<Rightarrow> Watermark x | Inr x \<Rightarrow> Watermark x) \<in> lset (produce (union_op buf1 buf2) stream_in)"
  apply (simp add: in_lset_conv_lnth)
  apply (elim exE conjE)
  subgoal for n
    apply (frule productive_find_bigger_watermark)
       apply assumption+
    apply simp
    apply (elim exE conjE)
    subgoal for n' wm
      using produce_union_op_completeness_Watermark_aux[where x=wm and lxs=stream_in, of buf2 buf1] apply simp
      apply (drule meta_mp)
       apply (metis in_lset_conv_lnth)
      apply (rule exI[of _ wm])
      apply (auto simp add: in_lset_conv_lnth)
      done
    done
  done

lemma produce_union_productive:
  "productive stream_in \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   (\<forall> wm \<in> Watermark -` lset stream_in. producible wm (buf2 \<union> (Watermark -` lset stream_in))) \<Longrightarrow>
   produce (union_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  apply (coinduction arbitrary: stream_in stream_out buf1 buf2 rule: productive_coinduct_prepend_cong1)
  subgoal for stream_in stream_out buf1 buf2
    apply (cases "lfinite stream_in")
    subgoal 
      using lfinite_produce_union_op by fast
    subgoal
      apply simp
      apply (rule disjI2)
      apply (subst (asm) produce.code)
      apply (simp split: option.splits prod.splits llist.splits sum.splits)
      subgoal 
        apply (drule productive_productive')
        apply (erule productive'.cases)
          apply simp
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        subgoal for lxs r
          apply hypsubst_thin
          by (meson llist.set_intros(1) producible_buf_produce_inner_union_op_None_False producible_stream_produce_inner_union_op_None_False producible_union)
        done
      subgoal for x2 x1 op' x2a x x2b xs lxs'
        apply hypsubst_thin
        apply (cases x)
        subgoal for t d
          apply hypsubst_thin
          apply simp
          apply (intro conjI)
          subgoal 
            using produce_union_op_not_lfinite 
            by (metis lfinite_code(2) lfinite_shift produce_inner_Some_produce)
          subgoal 
            apply (subgoal_tac "Data (Inl t) d \<in> lset stream_in \<or> Data (Inr t) d \<in> lset stream_in")
             defer
             apply (meson produce_inner_union_op_Data)
            apply (elim disjE)
            subgoal
              apply (frule produce_union_op_completeness_not_lfinite_Watermark[of _ _ _ _ buf1])
                  apply assumption+
               apply simp
              apply (elim exE conjE)
              subgoal for r
                apply (cases r)
                 apply simp_all
                subgoal for wm
                  apply (rule bexI[of _ wm])
                   apply blast
                  apply blast
                  done
                done
              done
            subgoal
              apply (frule produce_union_op_completeness_not_lfinite_Watermark[of _ _ _ _ buf1])
                  apply assumption+
               apply simp
              apply (elim exE conjE)
              subgoal for r
                apply (cases r)
                 apply simp_all
                subgoal for wm
                  apply (rule bexI[of _ wm])
                   apply blast
                  apply blast
                  done
                done
              done
            done
          subgoal
            apply (rule disjI1)
            apply (rule productive_prepend_cong1_prepend_1)
            subgoal
              apply (rule productive_prepend_cong1_base)
              apply (rule exI[of _ lxs'])
              apply (intro conjI)
              subgoal 
                apply (drule produce_inner_union_monotone_Inl_Data_2)
                 apply assumption+
                apply simp
                apply (metis ldrop_enat productive_ldrop)
                done
              subgoal
                apply (drule produce_inner_union_monotone_Inl_Data_2)
                 apply assumption+
                apply (elim exE conjE)
                apply simp
                apply (intro exI conjI)
                  prefer 3
                  apply (rule refl)
                using maximal_complete_maximal_antichain_set apply blast
                apply (intro allI conjI impI)
                subgoal for n buf1 buf2 wm
                  apply (drule spec[of _ wm])
                  apply (drule mp)
                   apply (meson in_lset_ldropnD)
                  apply (rule producible_unionI)
                  apply (subst producible_maximal_antichain_set)
                   apply (subst Un_commute)
                   apply (rule maximal_complete_union_finite)
                    apply (metis List.finite_set enat_ord_code(4) lfinite_ltake set_list_of set_map_filter_case_event_Watermark)
                   apply force
                  apply (rule producible_unionE)
                  apply (subgoal_tac "buf2 \<union> Watermark -` lset stream_in = Watermark -` lset (ltake (enat n) stream_in) \<union> buf2 \<union> Watermark -` lset (ldropn n stream_in)")
                  subgoal 
                    apply simp
                    apply (metis Un_assoc Un_left_commute ltake_ldropn_merge_lset vimage_Un)
                    done
                  apply (subst (2) Un_commute)
                  apply (subst Un_assoc)
                  using ltake_ldropn_merge_lset 
                  apply (metis vimage_Un)
                  done
                done
              done
            subgoal 
              apply (drule produce_inner_union_monotone_Inl_Data_2)
               apply assumption+
              apply auto
              done
            done
          done
        subgoal for wm
          apply hypsubst_thin
          apply simp
          apply (intro conjI)
          subgoal 
            using produce_union_op_not_lfinite 
            by (metis lfinite_code(2) lfinite_shift produce_inner_Some_produce)
          subgoal
            apply (rule disjI1)
            apply (rule productive_prepend_cong1_prepend_1)
            subgoal
              apply (rule productive_prepend_cong1_base)
              apply (rule exI[of _ lxs'])
              apply (intro conjI)
              subgoal 
                apply (drule produce_inner_union_monotone_Inl_Watermark_2)
                    apply (rule refl)+
                 apply assumption+
                apply simp
                apply (metis ldrop_enat productive_ldrop)
                done
              subgoal
                apply (drule produce_inner_union_monotone_Inl_Watermark_2)
                    apply (rule refl)+
                 apply assumption+
                apply simp
                apply (elim exE conjE)
                apply hypsubst_thin
                subgoal for n
                  apply (intro conjI exI)
                    prefer 3
                    apply (rule refl)
                  subgoal
                    using maximal_complete_maximal_antichain_set by blast
                  subgoal
                    apply (intro exI conjI allI impI)
                    subgoal for wm
                      apply (drule spec[of _ wm])
                      apply (drule mp)
                       apply (meson in_lset_ldropnD)
                      apply (smt (verit, best) List.finite_set enat_ord_code(4) lfinite_ltake ltake_ldropn_merge_lset maximal_complete_union_finite producible_maximal_antichain_set producible_unionE producible_unionI set_list_of set_map_filter_case_event_Watermark sup.commute vimage_Un)
                      done
                    done
                  done
                done
              done
            subgoal 
              apply (drule produce_inner_union_monotone_Inl_Watermark_2)
                  apply (rule refl)+
               apply assumption+
              apply simp
              apply (metis event.disc(1) nth_mem)
              done
            done
          done
        done
      subgoal
        by (meson produce_inner_Some_Inr_lfinite)
      done
    done
  done

lemma finite_produce_union_op_exit_LNil:
  "finite_produce (union_op buf1 buf2) xs = (op', out) \<Longrightarrow> exit op' = LNil"
  apply (induct xs arbitrary: buf1 buf2 op' out)
   apply (simp_all del: produce_LCons produce_inner_simps split: list.splits event.splits prod.splits)
   apply (meson eq_fst_iff)+
  done

end