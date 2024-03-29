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

lemma producible_unionI:
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

lemma [simp]:
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

lemma [simp]:
  "\<forall>wm\<in>unproduced_watermarks WM. \<not> producible wm WM"
  unfolding unproduced_watermarks_def producible_def
  apply auto
  done


lemma in_unproduced_watermarks_3:
  "maximal_complete WM \<Longrightarrow>
   \<not> producible wm (maximal_antichain_set WM) \<Longrightarrow>
   wm \<in> unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def producible_def maximal_antichain_set_def maximal_complete_def
  apply auto
  by (smt (verit) Inl_leq Inr_leq dual_order.trans less_eq_sum.cases old.sum.simps(5) old.sum.simps(6))

lemma in_unproduced_watermarks_union:
  "wm' \<in> unproduced_watermarks (WM' \<union> WM) \<Longrightarrow>
   wm' \<in> unproduced_watermarks WM' \<or> wm' \<in> unproduced_watermarks WM"
  unfolding unproduced_watermarks_def producible_def
  apply auto
  done

lemma unproduced_watermarks_union:
  "\<forall>wma\<in>unproduced_watermarks B. \<not> producible wma A \<Longrightarrow>
   \<forall>wma\<in>unproduced_watermarks A. \<not> producible wma B \<Longrightarrow>
   unproduced_watermarks (A \<union> B) = unproduced_watermarks A \<union> unproduced_watermarks B"
  unfolding unproduced_watermarks_def
  apply auto
       apply (meson Un_iff producible_def)+
  done


lemma in_unproduced_watermarks_4:
  "t \<in> maximal_antichain_set WM \<Longrightarrow>
   wm \<le> t \<Longrightarrow>
   t' \<in> unproduced_watermarks WM \<Longrightarrow>
   t' \<in> unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def producible_def maximal_antichain_set_def maximal_complete_def
  apply auto
  by (smt (verit, del_insts) Inl_leq Inr_leq less_eq_sum.cases old.sum.simps(5) old.sum.simps(6) order.trans)

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
  apply auto
  using less_eq_sum.cases by fastforce

lemma producible_not_in_unproduced_watermarks:
  "producible wm WM \<Longrightarrow>
  wm \<notin> unproduced_watermarks WM"
  by force

lemma unproduced_watermarks_insert_1:
  "producible wm WM \<Longrightarrow>
   unproduced_watermarks (insert wm WM) = unproduced_watermarks {wm' \<in> WM. \<not> wm' \<le> (case_sum Inr Inl wm) \<and> \<not> wm' \<le> wm}"
  unfolding unproduced_watermarks_def producible_def
  apply auto
  by (smt (verit) Inl_Inr_False Inl_leq Inr_leq dual_order.trans less_eq_sum.simps sum.case_eq_if sum.collapse(1) sum.collapse(2) sum.disc(2) sum.sel(1) sum.sel(2))

lemma unproduced_watermarks_insert_2:
  "\<not> producible wm WM \<Longrightarrow>
   unproduced_watermarks (insert wm WM) = insert wm (unproduced_watermarks {wma \<in> WM. \<not> producible wma (insert wm WM)})"
  unfolding unproduced_watermarks_def 
  unfolding unproduced_watermarks_def producible_def
  apply auto
  by (metis insertI1 producible_def producible_insert_same)

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

lemma producible_maximal_antichain_set:
  "maximal_complete WM \<Longrightarrow>
   producible wm (maximal_antichain_set WM) \<longleftrightarrow> producible wm WM"
  unfolding producible_def maximal_antichain_set_def maximal_complete_def
  apply auto
  by (smt (verit) Inl_leq Inr_leq dual_order.trans less_eq_sum.cases old.sum.simps(5) old.sum.simps(6))

lemma not_producible_maximal_antichain_set[simp]:
  "maximal_complete WM \<Longrightarrow>
   (\<not> producible wm (maximal_antichain_set WM)) \<longleftrightarrow> \<not> producible wm WM"
  unfolding producible_def maximal_antichain_set_def maximal_complete_def
  apply auto
  by (smt (verit) Inl_leq Inr_leq dual_order.trans less_eq_sum.cases old.sum.simps(5) old.sum.simps(6))

lemma unproduced_watermarks_conj_elim[simp]:
  "unproduced_watermarks {x \<in> WM. \<not> producible x WM \<and> P x} =
   {x \<in> unproduced_watermarks WM. P x}"
  unfolding unproduced_watermarks_def producible_def
  apply (auto split: sum.splits)
  done

lemma producible_filter_useless:
  "producible wm A \<longleftrightarrow> producible wm {wma \<in> A. \<not> wma < wm}"
  unfolding producible_def
  apply auto
  by (metis Inl_Inr_False dual_order.strict_implies_order isl_def less_eq_sum.cases sum.case_eq_if)

lemma producible_forall:
  "producible wm A \<Longrightarrow>
   (\<forall> wm' \<le> wm. producible wm' A)"
  apply (cases wm)
  unfolding producible_def
   apply auto
  using dual_order.trans apply blast+
  done

lemma not_producible_le_not_producible:
  "\<not> producible wm A \<Longrightarrow>
   wm \<le> wm' \<Longrightarrow>
   \<not> producible wm' A"
  apply (cases wm; cases wm')
  unfolding producible_def
     apply (auto split: sum.splits)
  done

lemma producible_union_extend:
  "producible wm A \<Longrightarrow>
   producible wm (A \<union> B)"
  unfolding producible_def
  apply auto
  done

lemma in_unproduced_watermarks_5:
  "\<not> wm' \<le> case_sum Inr Inl wm \<Longrightarrow>
   wm' \<in> unproduced_watermarks WM \<Longrightarrow>
   wm' \<in> unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def producible_def
  apply (auto split: sum.splits)
  done

lemma unproduced_watermarks_insert_not_producible:
  "\<not> producible wm A \<Longrightarrow>
   unproduced_watermarks (insert wm A) = insert wm (unproduced_watermarks A) - {wm' \<in> A. wm' \<le> (case_sum Inr Inl wm)}"
  unfolding unproduced_watermarks_def 
  apply auto
  using producible_insert_same producible_insert_simp by blast

lemma unproduced_watermarks_insert:
  "unproduced_watermarks (insert (wm::_::order) WM) =
   ((if \<exists> wm' \<in> WM. wm \<le> (case_sum Inr Inl wm')  
      then {wm' \<in> unproduced_watermarks WM. \<not> (case_sum Inr Inl wm') \<le> wm} else 
       (if \<exists> wm' \<in> WM. (case_sum Inr Inl wm') < wm 
        then insert wm ({wm' \<in> unproduced_watermarks WM. \<not> (case_sum Inr Inl wm') < wm})
        else insert wm (unproduced_watermarks WM))))"
  unfolding unproduced_watermarks_def producible_def
  apply (cases "\<exists> wm' \<in> WM. wm \<le> (case_sum Inr Inl wm')")
  subgoal
    apply simp
    apply auto
     apply (smt (verit, best) less_eq_sum.simps sum.case_eq_if sum.disc(1) sum.disc(2) sum.exhaust_sel sum.sel(1) sum.sel(2))
    apply (smt (verit, ccfv_threshold) Inl_Inr_False Inl_leq Inr_leq less_eq_sum.cases old.sum.simps(5) sum.case_eq_if sum.disc(2) sum.sel(1) sum.sel(2))
    done
  subgoal
    apply simp
    apply (cases "\<exists> wm' \<in> WM. (case_sum Inr Inl wm') < wm")
    subgoal
      apply simp
      apply auto
        apply (smt (verit, del_insts) Inl_Inr_False Inl_leq Inr_leq dual_order.strict_implies_order isl_def less_eq_sum.cases sum.case_eq_if sum.sel(1) sum.sel(2) sum.split_sel_asm)
       apply (metis less_eq_sum.simps sum.case_eq_if sum.discI(1) sum.discI(2))
      apply (smt (verit, best) Inl_Inr_False Inl_leq Inr_leq less_eq_sum.cases less_sum_def sum.case_eq_if sum.collapse(2) sum.disc(2) sum.sel(1) sum.sel(2))
      done
    subgoal
      apply auto
      using less_eq_sum.cases apply fastforce
      apply (smt (verit, ccfv_SIG) Inl_inject Inl_leq Inr_leq less_eq_sum.cases less_sum_def sum.case_eq_if sum.disc(1) sum.disc(2) sum.sel(2) sum.split_sel_asm)
      done
    done
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


lemma [simp]:
  "{x. x = y \<or> P x} = insert y {x. P x}"
  apply auto
  done

lemma unproduced_watermarks_insert_insert:
  "maximal_complete WM \<Longrightarrow>
   \<not> producible wm (maximal_antichain_set (insert wm WM)) \<Longrightarrow>
   \<forall>x\<in>unproduced_watermarks WM. \<not> producible x (maximal_antichain_set (insert wm WM)) \<Longrightarrow>
   insert wm (unproduced_watermarks WM) = unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def
  apply auto
  using producible_insert_same producible_insert_simp apply blast
  done

lemma produce_inner_union_monotone_Inl_Data:
  "produce_inner oo = Some r \<Longrightarrow> 
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data t d \<Longrightarrow>
   oo = (union_op buf1 buf2, lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   buf2 = maximal_antichain_set WM \<Longrightarrow>
   set buf1 = unproduced_watermarks WM \<Longrightarrow>
   maximal_complete WM \<Longrightarrow>
   wms xs = {} \<and>
   monotone (llist_of (x#xs)) (Inl -` (WM - set buf1) \<union> Inr -` (WM - set buf1)) \<and>
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
  apply (induct oo r arbitrary: WM buf1 buf2 lxs x xs lxs' op  rule: produce_inner_alt[consumes 1])
    prefer 2
  subgoal for op h x xs lxs lxs' lgc' WM buf1 buf2 lxs'' xa xsa lxs'a opa
    apply (subst (asm) produce_inner.simps)
    apply simp
    apply (cases lxs'')
     apply simp_all
    apply (intro conjI)
    subgoal
      apply (auto 2 1 split: sum.splits event.splits)
      done
    subgoal
      apply (auto 2 1 split: sum.splits event.splits)
      subgoal
        apply hypsubst_thin
        apply (rule LConsL)
         apply (auto 2 1)
        subgoal
          by (meson Inl_leq LConsData)
        subgoal
          by (smt (verit, ccfv_threshold) Data_set_strict_monotone_not_GE Inl_Inr_False Inl_leq Inr_inject Inr_leq in_unproduce_watermarks_2 less_eq_sum.cases lset_intros(1) sum.case_eq_if sum.collapse(1))
        apply (meson monotone.LNil)
        done
      subgoal
        apply hypsubst_thin
        apply (rule LConsL)
         apply (auto 2 1)
        subgoal
          by (smt (verit, ccfv_threshold) Inl_Inr_False Inl_inject Inl_leq Inr_leq LConsData in_unproduce_watermarks_2 less_eq_sum.cases sum.case_eq_if sum.collapse(2))
        subgoal
          by (meson Inr_leq LConsData)
        subgoal
          using monotone.LNil by blast
        done
      done
    subgoal
      apply (rule exI[of _ 1])
      apply (elim conjE)
      apply hypsubst_thin
      apply (simp add: ltake_enat_0 append_eq_Cons_conv map_filter_simps split: sum.splits event.splits if_splits; elim conjE; hypsubst_thin)
       apply blast+
      done
    done
  subgoal for op h lxs lgc' zs WM buf1 buf2 lxsa x xs lxs' opa
    apply (simp add: filter_empty_conv split: if_splits event.splits; (elim conjE)?; hypsubst_thin) 
    subgoal for wm
      apply (drule meta_spec[of _ "insert wm WM"])
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
          apply (auto 2 0)
             apply (metis in_not_in_unproduced_watermarks_insert insert_absorb)+
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
  apply auto
  done

lemma in_unproduced_watermarks_eq_not_prodible:
  "wm \<in> unproduced_watermarks WM \<longleftrightarrow> (\<not> producible wm WM \<and> wm \<in> WM)"
  unfolding unproduced_watermarks_def
  apply auto
  done

lemma produce_inner_union_monotone_Inl_Watermark:
  "produce_inner oo = Some r \<Longrightarrow> 
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   oo = (union_op buf1 buf2, lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   buf2 = maximal_antichain_set WM \<Longrightarrow>
   set buf1 = unproduced_watermarks WM \<Longrightarrow>
   maximal_complete WM \<Longrightarrow>
   monotone (llist_of (x#xs)) (Inl -` (WM - set buf1) \<union> Inr -` (WM - set buf1)) \<and>
   (\<forall> wm \<in> set buf1. \<not> producible wm (set buf1)) \<and>
   (\<exists> n buf1' buf2' wm. lxs' = ldropn n lxs \<and> 0 < n \<and>
     monotone lxs' ((Watermark -` lset (ltake n lxs)) \<union> WM) \<and>
     buf2' = maximal_antichain_set ((Watermark -` lset (ltake n lxs)) \<union> buf2) \<and>
     buf1' = filter (\<lambda> wm. \<not> producible wm buf2') ((rev (List.map_filter (case_event (\<lambda> _ _. None)
               (\<lambda> wm . Some wm)) 
               ((list_of (ltake n lxs))))) @ buf1) \<and>
     op = (union_op buf1' buf2') \<and>
    (\<forall> wm \<in> Watermark -` lset (ltake (n-1) lxs). \<not> producible wm (Watermark -` lset (ltake (n-1) lxs) \<union> WM)) \<and> 
    (\<forall> wm \<in> set buf1. \<not> producible wm (Watermark -` lset (ltake (n-1) lxs) \<union> WM)) \<and>
    wms (x#xs) = Inl -` {wm \<in> Watermark -` lset (ltake n lxs) \<union> set buf1. producible wm buf2'} \<union> Inr -` {wm \<in> Watermark -` lset (ltake n lxs) \<union> set buf1. producible wm buf2'})"
  apply (induct oo r arbitrary: WM buf1 buf2 lxs x xs lxs' op  rule: produce_inner_alt[consumes 1])
    prefer 2
  subgoal for op h x xs lxs lxs' lgc' WM buf1 buf2 lxs'' xa xsa lxs'a opa
    apply (subst (asm) produce_inner.simps)
    apply simp
    apply (cases lxs'')
     apply simp_all
    apply (elim conjE; hypsubst_thin)
    apply (intro conjI)
    subgoal
      apply (auto 2 1 simp add:  monotone_all_Watermarks split: sum.splits event.splits if_splits)
      done
    subgoal
      apply (rule exI[of _ 1])
      apply (simp add: ltake_enat_0 split: event.splits if_splits; elim conjE; hypsubst_thin)
        apply (intro conjI)
      subgoal for wm'
        apply (rule arg_cong2[where f=union_op])
        subgoal
          apply (auto simp add: maximal_antichain_set_single producible_maximal_antichain_set map_filter_simps split: sum.splits; hypsubst_thin)
          done
        subgoal
          using producible_filter_useless producible_maximal_antichain_set by blast
        done
      subgoal for wm'
        apply (auto 2 0 simp add: map_filter_simps)
        subgoal
          using maximal_complete_insert producible_insert_same producible_maximal_antichain_set by blast
        subgoal
          by (meson in_unproduced_watermarks_eq_not_prodible maximal_complete_insert not_producible_maximal_antichain_set producible_insert_same)
        using maximal_complete_insert producible_insert_same producible_maximal_antichain_set apply blast+
        done
      subgoal for wm'
        apply (auto 2 0 simp add:  wms_correct map_filter_simps)
        subgoal
          by (smt (verit, best) filter_cong)
           apply (metis event.inject(2) sum.case_eq_if sum.collapse(1) sum.collapse(2))
          apply (metis event.inject(2) sum.case_eq_if sum.collapse(1) sum.collapse(2))
         apply (metis event.inject(2) sum.case_eq_if sum.collapse(1) sum.collapse(2))
        apply (metis event.inject(2) sum.case_eq_if sum.collapse(1) sum.collapse(2))
        done
      subgoal for wm'
        apply (auto 2 0 simp add: ltake_enat_0 wms_correct map_filter_simps)
        subgoal
          by (smt (verit, best) filter_cong)
                       apply (metis (no_types, lifting) event.inject(2) filter_is_subset list.set_intros(1) subset_code(1) sum.case_eq_if sum.collapse(1) sum.collapse(2))
        subgoal
          by (metis (no_types, lifting) event.inject(2) list.set_intros(1) mem_Collect_eq set_filter sum.case_eq_if sum.collapse(1) sum.collapse(2))
        subgoal
          by (metis (no_types, lifting) event.inject(2) filter_set in_unproduced_watermarks_5 list.set_intros(1) maximal_complete_insert member_filter not_producible_maximal_antichain_set producible_not_in_unproduced_watermarks sum.case_eq_if sum.collapse(1) sum.collapse(2))
        subgoal
          by (smt (verit, del_insts) event.inject(2) filter_set isl_def list.set_intros(1) maximal_complete_insert member_filter not_producible_maximal_antichain_set old.sum.simps(5) old.sum.simps(6) producible_insert_simp sum.collapse(2))
        subgoal
          by (metis (no_types, lifting) event.sel(3) filter_is_subset in_mono set_subset_Cons sum.case_eq_if sum.collapse(1) sum.collapse(2))
        subgoal
          by (metis (no_types, lifting) event.sel(3) mem_Collect_eq set_filter set_subset_Cons subset_code(1) sum.case_eq_if sum.collapse(1) sum.collapse(2))
        subgoal
          by (smt (verit, ccfv_threshold) event.sel(3) insert_iff list.simps(15) maximal_antichain_set_subset mem_Collect_eq producible_insert_simp producible_subset set_filter sum.case_eq_if sum.collapse(1) sum.collapse(2))
        subgoal
          by (smt (z3) dual_order.eq_iff event.sel(3) filter_is_subset in_mono in_unproduced_watermarks_eq_not_prodible insert_iff maximal_complete_insert old.sum.simps(5) old.sum.simps(6) producible_def producible_maximal_antichain_set set_subset_Cons sum.collapse(1) sum.collapse(2))
        subgoal
          by (metis (no_types, lifting) filter_is_subset in_mono set_subset_Cons) 
        subgoal
          by (smt (verit, ccfv_threshold) insert_compr list.simps(15) maximal_complete_insert mem_Collect_eq not_producible_maximal_antichain_set producible_insert_simp set_filter) 
        subgoal
          by (metis (no_types, lifting) filter_set list.set_intros(2) member_filter) 
        subgoal
          by (metis (no_types, lifting) dual_order.refl filter_is_subset in_mono in_unproduced_watermarks_eq_not_prodible insert_absorb maximal_complete_insert not_producible_maximal_antichain_set old.sum.simps(6) producible_insert_simp set_subset_Cons) 
        subgoal
          using maximal_complete_insert not_producible_maximal_antichain_set producible_insert_same by blast 
        subgoal
          by (metis (mono_tags, lifting) event.inject(2) filter_set insert_iff list.simps(15) member_filter old.sum.simps(5))
        subgoal
          using maximal_complete_insert not_producible_maximal_antichain_set producible_insert_same by blast 
        subgoal
          by (metis (no_types, lifting) event.inject(2) filter_set member_filter set_ConsD sum.case_eq_if sum.disc(2) sum.sel(2)) 
        done
      done
    done
  subgoal for op h lxs lgc' zs WM buf1 buf2 lxsa x xs lxs' opa
    apply (simp add: filter_empty_conv split: if_splits event.splits; (elim conjE)?; hypsubst_thin) 
    subgoal for wm'
      apply (drule meta_spec[of _ "insert wm' WM"])
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
          apply (auto 2 0)
             apply (metis in_not_in_unproduced_watermarks_insert insert_absorb)+
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
             apply auto
            using in_unproduced_watermarks_3 prems(12) prems(3) prems(4) by fastforce
          subgoal
            using prems(8,12) apply simp
            apply (cases n)
             apply auto
            subgoal
              using in_unproduced_watermarks_5 prems(5) by blast
            subgoal
              using prems(5) by blast
            done
          subgoal
            using prems(8,13,4) 
            apply (auto 2 1 simp add: map_filter_simps)
                       apply (metis (mono_tags, lifting) in_not_in_unproduced_watermarks_insert)
                      apply (metis (mono_tags, lifting) in_not_in_unproduced_watermarks_insert)
            using in_not_in_unproduced_watermarks_insert apply blast
            using in_not_in_unproduced_watermarks_insert apply blast
                   apply (meson insertI1 is_producible producible_insert_same)
                  apply (meson insertI1 is_producible producible_insert_same)
            using in_unproduced_watermarks_5 prems(5) apply blast
            using in_unproduced_watermarks_5 prems(5) apply blast
               apply (meson insertI1 is_producible producible_insert_same)
              apply (meson insertI1 is_producible producible_insert_same)
            using in_unproduced_watermarks_5 prems(5) apply blast
            using in_unproduced_watermarks_5 prems(5) apply blast
            done
          done
        done
      done
    done
  apply auto
  done

lemma unproduced_simp:
  "{wm \<in> WM''. \<forall>wm'\<in>WM''. (\<forall>x1. wm' = Inl x1 \<longrightarrow> \<not> wm \<le> Inr x1) \<and> (\<forall>x2. wm' = Inr x2 \<longrightarrow> \<not> wm \<le> Inl x2)} =
   {wm \<in> WM''. \<forall>wm'\<in>WM''. \<not> wm \<le> (case wm' of Inl x \<Rightarrow> Inr x | Inr x \<Rightarrow> Inl x)}"
  by (metis (mono_tags, opaque_lifting) old.sum.simps(5) old.sum.simps(6) sum.exhaust_sel sum.split_sel_asm)

lemma set_map_filter_case_event_Watermark[simp]:
  "set (List.map_filter (case_event (\<lambda>_. Map.empty) Some) xs) = Watermark -` (set xs)"
  apply (induct xs)
   apply (auto simp add: map_filter_simps event.splits)
   apply (metis (no_types, lifting) event.case_eq_if event.collapse(2) option.case_eq_if option.sel set_ConsD vimageE)
  apply (simp add: option.case_eq_if)
  done

lemma unproduced_watermarks_union_add_unproduced_watermarks:
  "\<forall> wm \<in> A. \<not> producible wm B \<Longrightarrow>
   unproduced_watermarks (A \<union> B) = 
   unproduced_watermarks (A \<union> unproduced_watermarks B)"
  unfolding unproduced_watermarks_def
  apply auto
      apply (metis (mono_tags, lifting) Un_iff mem_Collect_eq producible_def)
     apply (meson Un_upper2 producible_subset)
    apply (metis (mono_tags, lifting) Un_iff mem_Collect_eq producible_def)
   apply (meson inf_sup_ord(4) producible_subset producible_union)
  by (meson producible_subset producible_union sup.cobounded1)

lemma unproduced_watermarks_insert_3[simp]:
  "{x. x = wm \<and> \<not> producible x (insert wm WM)} \<union> {x \<in> unproduced_watermarks WM. \<not> producible x (insert wm WM)} =
   unproduced_watermarks (insert wm WM)"
  unfolding unproduced_watermarks_def
  apply (auto 2 1)
  done

lemma unproduced_watermarks_simp_aux[simp]:
  "maximal_complete (Watermark -` A \<union> WM) \<Longrightarrow>
   {x. (x = wm \<or> Watermark x \<in> A) \<and> \<not> producible x (maximal_antichain_set (insert wm (Watermark -` A \<union> WM)))} \<union>
   {x \<in> unproduced_watermarks WM. \<not> producible x (maximal_antichain_set (insert wm (Watermark -` A \<union> WM)))} =
   unproduced_watermarks (insert wm (Watermark -` A \<union> WM))"
  apply (subst (1 2) not_producible_maximal_antichain_set)
  subgoal 
    using maximal_complete_insert by blast
  apply simp
  unfolding unproduced_watermarks_def
  apply auto
  using not_producible_union by blast


(* FIXME: move me to soundness *)
lemma produce_inner_skip_n_productions_op_union_op_Inr:
  "produce_inner op_lxs = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   op_lxs = (skip_n_productions_op (union_op buf1 bu2) n, lxs) \<Longrightarrow>
   exit op = LNil"
  apply (induct op_lxs r arbitrary: buf1 bu2 lxs n  rule: produce_inner_alt[consumes 1])
    apply (auto split: if_splits event.splits sum.splits)
    apply (metis skip_n_productions_op_0)
   apply (smt (verit, best) skip_n_productions_op_0)
  apply (smt (verit, del_insts) skip_n_productions_op_0)
  done

lemma produce_union_op_monotone:
  "monotone stream_in WM \<Longrightarrow>
   buf2 = maximal_antichain_set WM \<Longrightarrow>
   set buf1 = unproduced_watermarks WM \<Longrightarrow>
   maximal_complete WM \<Longrightarrow>
   produce (union_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   monotone stream_out (Inl -` (WM - set buf1) \<union> Inr -` (WM - set buf1))"
  apply (coinduction arbitrary: WM stream_in buf1 stream_out buf2 rule: strict_monotone_coinduct_strict_monotone_prepend_cong1)
  apply (erule monotone.cases)
    apply simp
  subgoal for WM' stream_in buf1 stream_out buf2 lxs wm WM''
    apply hypsubst
    apply (subst (asm) produce.code)
    apply (simp del: produce_LCons split: prod.splits option.splits sum.splits)
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (simp add: produce_inner_None_produce_LNil del: produce_LCons split: if_splits list.splits)
      subgoal
        apply hypsubst_thin
        apply (rule disjI1)
        apply (simp add: lnull_def)
        apply (subst produce.code)
        apply (auto 2 0 split: option.splits sum.splits)
        done
      done
    subgoal for x2 x1 op x2a x x2b xs' lxs'
      apply hypsubst_thin
      apply (cases x)
      subgoal for t d
        apply hypsubst_thin
        apply simp
        apply (drule produce_inner_union_monotone_Inl_Data[where WM="WM''"])
               apply (rule refl)+
            apply (simp_all add: unproduced_simp)
        apply (elim conjE exE)
        subgoal for n
          apply (intro conjI impI ballI)
          subgoal for wm'
            apply auto
             apply (meson DiffI LConsData subset_eq sup.cobounded1 vimageI2)
            apply (meson DiffI LConsData in_mono inf_sup_ord(4) vimageI)
            done
          subgoal 
            apply hypsubst_thin
            apply (rule disjI1)
            apply (rule monotone_prepend_cong_prepend)
            subgoal
              apply (cases n)
               apply blast
              subgoal for n'
                apply (rule monotone_prepend_cong_base)
                apply simp
                apply (rule exI[of _ "insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')"])
                apply (rule exI)
                apply (rule exI[of _ "rev (List.map_filter (case_event (\<lambda>_. Map.empty) Some) (list_of (ltake (enat n') lxs))) @ wm #buf1"])
                apply (intro conjI)
                    prefer 5
                    apply (rule arg_cong2[where f=produce])
                     apply (rule arg_cong2[where f=union_op])
                subgoal
                  apply (auto simp add: map_filter_simps)
                  done
                     defer
                     apply (rule refl)
                    defer
                subgoal 
                  by blast
                subgoal
                  apply simp
                  apply (subst unproduced_watermarks_insert_2)
                   apply fastforce
                  apply (rule arg_cong2[where f=insert])
                   apply simp
                  unfolding unproduced_watermarks_def
                  apply (auto 2 1)
                    apply (smt (z3) Un_iff mem_Collect_eq producible_def vimageI)+
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
                subgoal
                  unfolding maximal_antichain_set_def
                  apply (auto 2 1)
                  done
                subgoal
                  apply simp
                  apply (rule arg_cong2[where f=union])
                  subgoal
                    apply (rule arg_cong2[where f=vimage])
                     apply simp
                    apply (auto 2 1)
                     apply (metis Un_upper1 is_producible producible_subset sup_commute)
                    apply (meson Un_upper2 is_producible producible_subset vimageI)
                    done
                  subgoal
                    apply (rule arg_cong2[where f=vimage])
                     apply simp
                    apply (auto 2 1)
                     apply (metis Un_upper1 is_producible producible_subset sup_commute)
                    apply (meson Un_upper2 is_producible producible_subset vimageI)
                    done
                  done
                done
              done
            by (metis (no_types, lifting) LConsData unproduced_watermarks_def)
          done
        done
      subgoal for wm'
        apply hypsubst_thin
        apply simp
        apply (drule produce_inner_union_monotone_Inl_Watermark[where WM="WM''"])
               apply (rule refl)+                 
            apply (simp_all add: unproduced_simp)
        apply (elim conjE exE)
        subgoal premises prems for n 
          apply (rule disjI1)
          apply (rule monotone_prepend_cong_prepend)
          subgoal
            apply (cases n)
            using prems(6)
             apply blast
            subgoal for n'
              apply (rule monotone_prepend_cong_base)
              apply simp
              apply (rule exI)+
              apply (intro conjI)
                  prefer 5
                  apply (rule arg_cong2[where f=produce])
              using prems(8) apply hypsubst
                   apply (rule arg_cong2[where f=union_op])
                    apply (rule refl)
                   defer
                   apply (rule refl)
                  defer
              using prems(7)
                  apply assumption
              subgoal
                apply simp
                using prems(1,2) apply -
                apply simp
                apply (subst unproduced_watermarks_simp_aux)
                 apply (subst Un_commute)
                 apply (rule maximal_complete_union_finite)
                  apply (metis List.finite_set enat_ord_code(4) lfinite_ltake set_list_of set_map_filter_case_event_Watermark)
                 apply auto
                done
              subgoal
                apply (subst Un_commute)
                apply (rule maximal_complete_union_finite)
                 apply (metis List.finite_set enat_ord_code(4) lfinite_ltake set_list_of set_map_filter_case_event_Watermark)
                using prems(2) apply simp
                done
              subgoal
                apply simp
                done
              subgoal
                using prems(5,2) apply -
                apply (simp flip: Un_insert_left)
                apply (subst prems(11))
                apply simp
                apply (subgoal_tac "{y. (Inl y = wm \<or> Watermark (Inl y) \<in> lset (ltake (enat n') lxs) \<or> Inl y \<in> unproduced_watermarks WM'') \<and>
        producible (Inl y) (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))} \<union>
    {y. (Inr y = wm \<or> Watermark (Inr y) \<in> lset (ltake (enat n') lxs) \<or> Inr y \<in> unproduced_watermarks WM'') \<and>
        producible (Inr y) (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))} \<union>
    (Inl -` (WM'' - unproduced_watermarks WM'') \<union> Inr -` (WM'' - unproduced_watermarks WM'')) = 
    ({y. (Inl y = wm \<or> Watermark (Inl y) \<in> lset (ltake (enat n') lxs) \<or> Inl y \<in> unproduced_watermarks WM'') \<and>
        producible (Inl y) (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))} \<union> Inl -` (WM'' - unproduced_watermarks WM'')) \<union>
    ({y. (Inr y = wm \<or> Watermark (Inr y) \<in> lset (ltake (enat n') lxs) \<or> Inr y \<in> unproduced_watermarks WM'') \<and>
        producible (Inr y) (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))} \<union>
    Inr -` (WM'' - unproduced_watermarks WM''))")
                 defer
                 apply fast
                apply (subgoal_tac "Inl -`
    (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'') -
     ({x. (x = wm \<or> Watermark x \<in> lset (ltake (enat n') lxs)) \<and>
          \<not> producible x (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))} \<union>
      {x \<in> set buf1. \<not> producible x (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))})) \<union>
    Inr -`
    (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'') -
     ({x. (x = wm \<or> Watermark x \<in> lset (ltake (enat n') lxs)) \<and>
          \<not> producible x (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))} \<union>
      {x \<in> set buf1. \<not> producible x (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))})) = 
    (Inl -`
    (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'') -
     ({x. (x = wm \<or> Watermark x \<in> lset (ltake (enat n') lxs)) \<and>
          \<not> producible x (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))} \<union>
      {x \<in> set buf1. \<not> producible x (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))}))) \<union>
    (Inr -`
    (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'') -
     ({x. (x = wm \<or> Watermark x \<in> lset (ltake (enat n') lxs)) \<and>
          \<not> producible x (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))} \<union>
      {x \<in> set buf1. \<not> producible x (maximal_antichain_set (insert wm (Watermark -` lset (ltake (enat n') lxs) \<union> WM'')))})))")
                 defer
                 apply fast
                subgoal premises prems2
                  apply (subst prems2(4))
                  apply (subst prems2(5))
                  apply (rule arg_cong2[where f=union])
                  subgoal
                    apply auto
                    using prems(3) is_producible not_producible_union in_unproduced_watermarks_eq_not_prodible apply blast
                       apply (metis (no_types, lifting) List.finite_set Un_insert_right enat_ord_code(4) is_producible lfinite_ltake maximal_complete_union_finite not_producible_union prems2(3) producible_maximal_antichain_set remove_insert_eq set_list_of set_map_filter_case_event_Watermark sup_commute)
                      apply (metis (no_types, lifting) List.finite_set Un_insert_left Un_upper2 enat_ord_code(4) is_producible lfinite_ltake maximal_complete_insert maximal_complete_union_finite prems2(3) producible_maximal_antichain_set producible_subset set_list_of set_map_filter_case_event_Watermark sup_commute)
                     apply (metis (no_types, lifting) List.finite_set Un_insert_left Un_upper2 enat_ord_code(4) is_producible lfinite_ltake maximal_complete_insert maximal_complete_union_finite prems2(3) producible_maximal_antichain_set producible_subset set_list_of set_map_filter_case_event_Watermark sup_commute)
                    using prems(1) apply blast
                    done
                  subgoal
                    apply auto
                    using prems(3) is_producible not_producible_union in_unproduced_watermarks_eq_not_prodible apply blast
                       apply (metis (no_types, lifting) List.finite_set Un_insert_right enat_ord_code(4) is_producible lfinite_ltake maximal_complete_union_finite not_producible_union prems2(3) producible_maximal_antichain_set remove_insert_eq set_list_of set_map_filter_case_event_Watermark sup_commute)
                      apply (metis (no_types, lifting) List.finite_set Un_insert_left Un_upper2 enat_ord_code(4) is_producible lfinite_ltake maximal_complete_insert maximal_complete_union_finite prems2(3) producible_maximal_antichain_set producible_subset set_list_of set_map_filter_case_event_Watermark sup_commute)
                     apply (metis (no_types, lifting) List.finite_set Un_insert_left Un_upper2 enat_ord_code(4) is_producible lfinite_ltake maximal_complete_insert maximal_complete_union_finite prems2(3) producible_maximal_antichain_set producible_subset set_list_of set_map_filter_case_event_Watermark sup_commute)
                    using prems(1) apply blast
                    done
                  done
                done
              done
            done
          using prems(4)
          apply -
          by (metis (no_types, lifting) unproduced_watermarks_def)
        done
      done
    subgoal
      apply (rule disjI1)
      apply (frule produce_inner_skip_n_productions_op_union_op_Inr[where n=0, simplified])
        apply (rule refl)+
      apply (subst produce.code)
      apply simp      
      done
    done
  subgoal for WM' stream_in buf1 stream_out buf2 WM'' t lxs' d
    apply hypsubst
    apply (subst (asm) produce.code)
    apply (simp del: produce_LCons split: prod.splits option.splits sum.splits)
    subgoal 
      using lnull_def produce_inner_None_produce_LNil by blast
    subgoal for x2 x1 op x2a x x2b xs' lxs
      apply (cases x)
      subgoal
        apply hypsubst_thin
        apply (rule disjI2)
        apply (frule produce_inner_union_monotone_Inl_Data[where WM=WM''])
               apply (rule refl)+
            defer
            apply (rule refl)+
           apply blast
          apply blast
         defer
         apply (subst (asm) produce_inner.simps)
         apply auto
           apply hypsubst_thin
           apply (simp add: LConsL)
          apply (metis DiffI LConsData Un_iff vimage_eq)
         apply (metis Diff_iff LConsData Un_iff vimage_eq)
        apply hypsubst_thin
        subgoal for n 
          apply (cases n)
           apply blast
          subgoal for n'
            apply (rule monotone_prepend_cong_prepend)
            subgoal
              apply (rule monotone_prepend_cong_base)
              apply simp
              apply (rule exI)+
              apply (intro conjI)
                  prefer 5
                  apply (rule arg_cong2[where f=produce])
                   apply (rule arg_cong2[where f=union_op])
                    apply (rule refl)+
              subgoal premises prems2
                using prems2(1,11,12,9) apply -
                apply auto
                using is_producible not_producible_union apply blast+
                done
              subgoal
                by auto
              subgoal
                apply auto
                apply (meson Un_iff in_unproduced_watermarks_eq_not_prodible vimageI)
                subgoal
                  by (meson Un_iff in_unproduced_watermarks_eq_not_prodible)
                subgoal
                  by (meson in_unproduced_watermarks_eq_not_prodible in_unproduced_watermarks_union vimageE)
                done
              subgoal
                subgoal
                  apply (subst Un_commute)
                  apply (rule maximal_complete_union_finite)
                  apply (metis List.finite_set enat_ord_code(4) lfinite_ltake set_list_of set_map_filter_case_event_Watermark)
                  apply simp
                  done
                done
              done
            subgoal
              by (metis (mono_tags, lifting) strict_monotone_drop_head)
            done
          done
        done
      subgoal for wm
        apply (subst (asm) produce_inner.simps)
        apply (auto split: sum.splits)
        done
      done
    subgoal
      apply (rule disjI1)
      apply (subst (asm) produce_inner.simps)
      apply (auto split: sum.splits)
      done
    done
  done

subsection \<open>Soundness\<close> 
lemma produce_inner_union_op_Data:
  "produce_inner op_lxs = Some r \<Longrightarrow>
   r = Inl (lgc', x::('t::order, 'b) event, xs, lzs) \<Longrightarrow>
   op_lxs = (union_op buf1 buf2, lxs) \<Longrightarrow>
   x = Data t d \<Longrightarrow>
   Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  apply (induct op_lxs r arbitrary: buf1 buf2 lxs lgc' rule: produce_inner_alt[consumes 1])
  apply (auto split: event.splits if_splits sum.splits)
  done

lemma produce_inner_skip_n_productions_op_union_op_Data:
  "produce_inner op_lxs = Some r \<Longrightarrow>
   op_lxs = (skip_n_productions_op (union_op buf1 buf2) n, lxs) \<Longrightarrow>
   r = Inl (lgc', x::('t::order, 'b) event, xs, lzs) \<Longrightarrow>
   x = Data t d \<Longrightarrow>
   Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  apply (induct op_lxs r arbitrary: n buf1 buf2 lxs lgc' rule: produce_inner_alt[consumes 1])
  apply (auto split: event.splits if_splits sum.splits)
  apply (metis (mono_tags) skip_n_productions_op_0)+
  apply (metis Suc_lessI bot_nat_0.not_eq_extremum drop0 drop_Suc_Cons event.inject(1) list.discI nth_Cons_0)
  apply (metis drop_Cons' drop_Nil event.inject(1) list.inject list.sel(3) not_Cons_self tl_drop)
  apply (metis drop_Cons' drop_Nil event.inject(1) list.distinct(1) list.inject)
  apply (metis drop_Cons' drop_Nil event.inject(1) list.inject list.simps(3))
  apply (auto simp add: not_less dest!: nth_via_drop' split: sum.splits)
  apply (smt (verit, del_insts) Suc_length_conv event.simps(4) ex_map_conv length_map list.simps(9) map_case_sum_Watermark nth_mem set_ConsD)
  apply (metis (no_types, lifting) diff_Suc_1 event.distinct(1) less_Suc_eq_0_disj nth_Cons' nth_map sum.case_eq_if)
  done 

(* lemma produce_inner_skip_n_productions_op_union_op_Inr:
  "produce_inner op_lxs = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   op_lxs = (skip_n_productions_op (union_op buf1 buf2) n, lxs) \<Longrightarrow>
   exit op = LNil"
  apply (induct op_lxs r arbitrary: buf1 buf2 lxs n  rule: produce_inner_alt[consumes 1])
    apply (auto split: if_splits event.splits sum.splits)
    apply (metis skip_n_productions_op_0)
  apply (smt (verit, best) skip_n_productions_op_0)+
  done  *)


lemma produce_inner_union_op_Inr:
  "produce_inner op_lxs = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   op_lxs = (union_op buf1 buf2, lxs) \<Longrightarrow>
   exit op = LNil \<and> (\<forall> x \<in> lset lxs. \<not> is_Data x)"
  apply (induct op_lxs r arbitrary: buf1 buf2 lxs op rule: produce_inner_alt[consumes 1])
  apply (auto 2 1 split: if_splits event.splits sum.splits; hypsubst_thin)
  apply (subst (asm) produce_inner.simps)
  apply auto
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
  apply safe
  subgoal for n
    apply (induct n arbitrary: t d lxs buf1 buf2)
    subgoal for t d lxs
      apply (subst produce.code)
      apply (auto split: option.splits)
      subgoal
        apply (cases lxs)
        apply simp_all
        apply (subst produce_inner.simps)
        apply auto
        done
      subgoal for op
        apply (cases lxs)
        apply simp_all
        subgoal for x lxs'
          apply hypsubst_thin
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        done
      done
    subgoal for n t d lxs buf1 buf2
      apply (subst produce.code)
      apply (auto split: option.splits)
      subgoal
        apply (cases lxs)
        apply simp_all
        apply (subst produce_inner.simps)
        apply (auto split: if_splits event.splits sum.splits)
        subgoal for lxs' t'
          apply (drule meta_spec)
          apply (drule meta_spec)
          apply (drule meta_spec)
          apply (drule meta_spec[of _ "t'#buf1"])
          apply (drule meta_spec[of _ "maximal_antichain_set (insert t' buf2)"])
          apply (drule meta_mp)
          apply assumption
          apply (drule meta_mp)
          using Suc_ile_eq apply blast
          apply (subst (asm) produce.code)
          apply (auto simp add: filter_empty_conv split: option.splits sum.splits list.splits)
          done
        done
      subgoal for wm
        apply (cases lxs)
        apply simp_all
        subgoal for x lxs''
          apply (subst (asm) produce_inner.simps)
          apply (auto simp add: filter_empty_conv Suc_ile_eq split: if_splits event.splits sum.splits list.splits; hypsubst_thin)
          apply (smt (verit, best) finite_produce_to_shift_produce in_lset_shift_eq insert_iff list.simps(15) produce_inner_to_finite_produce)
          subgoal for wm
            apply (frule produce_inner_union_op_Inr)
            apply (rule refl)+
            apply auto
            apply (metis in_lset_conv_lnth is_Data_def)
            done
          done
        done
      done
    done
  done


lemma produce_union_op_Inr_completeness:
  "Data (Inr t) d \<in> lset lxs \<Longrightarrow>
   Data t d \<in> lset (produce (union_op buf1 buf2) lxs)"
  apply (subst (asm) lset_conv_lnth)
  apply safe
  subgoal for n
    apply (induct n arbitrary: t d lxs buf1 buf2)
    subgoal for t d lxs
      apply (subst produce.code)
      apply (auto split: option.splits)
      subgoal
        apply (cases lxs)
        apply simp_all
        apply (subst produce_inner.simps)
        apply auto
        done
      subgoal for op
        apply (cases lxs)
        apply simp_all
        subgoal for x lxs'
          apply hypsubst_thin
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        done
      done
    subgoal for n t d lxs buf1 buf2
      apply (subst produce.code)
      apply (auto split: option.splits)
      subgoal
        apply (cases lxs)
        apply simp_all
        apply (subst produce_inner.simps)
        apply (auto split: if_splits event.splits sum.splits)
        subgoal for lxs' t'
          apply (drule meta_spec)
          apply (drule meta_spec)
          apply (drule meta_spec)
          apply (drule meta_spec[of _ "t'#buf1"])
          apply (drule meta_spec[of _ "maximal_antichain_set (insert t' buf2)"])
          apply (drule meta_mp)
          apply assumption
          apply (drule meta_mp)
          using Suc_ile_eq apply blast
          apply (subst (asm) produce.code)
          apply (auto simp add: filter_empty_conv split: option.splits sum.splits list.splits)
          done
        done
      subgoal for wm
        apply (cases lxs)
        apply simp_all
        subgoal for x lxs''
          apply (subst (asm) produce_inner.simps)
          apply (auto simp add: filter_empty_conv Suc_ile_eq split: if_splits event.splits sum.splits list.splits; hypsubst_thin)
          apply (smt (verit, best) finite_produce_to_shift_produce in_lset_shift_eq insert_iff list.simps(15) produce_inner_to_finite_produce)
          subgoal for wm
            apply (frule produce_inner_union_op_Inr)
            apply (rule refl)+
            apply auto
            apply (metis in_lset_conv_lnth is_Data_def)
            done
          done
        done
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
    apply (subst produce.code)
    apply(auto split: option.splits sum.splits; hypsubst_thin?)
    subgoal 
      apply (subst (asm) produce_inner.simps)
      apply(auto split: list.splits if_splits event.splits sum.splits; hypsubst_thin?)
      apply (meson produce_inner_Some_lfinite_produce_lfinite)
      done
    subgoal
      by (simp add: produce_inner_union_op_Inr)
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
    apply (auto split: list.splits if_splits event.splits)
    apply (drule meta_spec)+
    apply (drule meta_mp)
    defer
    apply (drule meta_mp)
    defer
    apply (drule meta_mp)
    apply assumption
    apply simp
    using maximal_complete_insert not_producible_maximal_antichain_set producible_insert_simp apply blast
    by (metis (mono_tags, lifting) dual_order.refl maximal_antichain_set_def maximal_complete_def mem_Collect_eq)
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
    apply (subst produce_inner.simps)
    apply (auto 2 1 simp add: filter_empty_conv map_filter_simps split: llist.splits event.splits list.splits if_splits)
    subgoal
      by (meson maximal_complete_insert not_producible_maximal_antichain_set producible_insert_same)
    subgoal for lxs x
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply assumption
      apply (drule meta_mp)
      apply (metis (mono_tags, lifting) dual_order.refl maximal_antichain_set_def maximal_complete_def mem_Collect_eq)
      subgoal 
        apply (auto 2 1 simp add:  map_filter_simps)
        done
      done
    done
  done

lemma find_producible_position:
  "Watermark wm \<in> lset lxs \<Longrightarrow>
   producible wm (Watermark -` lset lxs) \<Longrightarrow>
   \<exists> n. Watermark wm \<in> lset (ltake (enat n) lxs) \<and> producible wm (Watermark -` lset (ltake (enat n) lxs)) "
  unfolding producible_def
  apply (auto simp add: in_lset_conv_lnth split: sum.splits)
  subgoal for n wm' n'
    apply (cases "n < n'")
    subgoal
      apply (rule exI[of _ "Suc n'"])
      apply (intro conjI)
      apply (metis enat_ord_simps(2) less_Suc_eq lnth_ltake)
      apply (rule bexI[of _ wm'])
      apply auto
      apply (metis (no_types, lifting) enat_ord_simps(2) in_lset_conv_lnth lessI llength_ltake lnth_ltake min_def)
      done
    subgoal
      apply (auto simp add: not_less order.order_iff_strict)
      subgoal
        apply (rule exI[of _ "Suc n"])
        apply (intro conjI)
        apply (metis enat_ord_simps(2) lessI lnth_ltake)
        apply (rule bexI[of _ wm'])
        apply auto
        apply (metis (no_types, lifting) enat_ord_simps(2) in_lset_conv_lnth llength_ltake lnth_ltake min_def not_less_eq not_less_iff_gr_or_eq)
        done
      subgoal
        by (meson sumE)
      done
    done
  done

lemma union_op_maximal_complete:
  "maximal_complete buf2 \<Longrightarrow>
   union_op buf1 buf2 = union_op buf1 (maximal_antichain_set buf2)"
  apply (coinduction arbitrary:  buf1 buf2 rule: op.coinduct)
  apply (auto simp add: rel_fun_def rel_prod.simps split: event.splits)
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
        apply auto
        by (smt (verit, ccfv_threshold) List.finite_set Un_commute Un_iff Un_upper1 enat_ord_code(4) lfinite_ltake maximal_complete_union_finite producible_maximal_antichain_set producible_subset set_list_of set_map_filter_case_event_Watermark vimageI)
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
    subgoal
      apply (subst produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits)
      done
    subgoal for z
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits if_splits)
      done
    done
  subgoal for x' xs buf1 buf2
    apply (subst produce.code)
    apply (auto split: option.splits)
    subgoal
      apply (subst produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits event.splits)
      apply (metis maximal_complete_insert producible_buf_produce_inner_union_op_None_False producible_insert_simp union_op_maximal_complete)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits event.splits if_splits)

      subgoal for y
        apply hypsubst_thin
        apply (drule meta_spec[of _ "y # buf1"])
        apply (drule meta_spec[of _ "maximal_antichain_set (insert y buf2)"])
        apply (drule meta_mp)
        using maximal_complete_maximal_antichain_set apply blast
        apply (drule meta_mp)
        apply (meson maximal_complete_insert not_producible_maximal_antichain_set producible_insert_simp)
        apply (subst (asm) produce.code)
        apply (auto split: option.splits)
        done
      subgoal
        by (meson maximal_complete_insert maximal_complete_maximal_antichain_set producible_insert_simp producible_maximal_antichain_set productive_drop_head)
      subgoal
        by (smt (verit, ccfv_threshold) maximal_complete_insert producible_insert_simp productive_drop_head union_op_maximal_complete)
      subgoal
        by (meson maximal_complete_insert maximal_complete_maximal_antichain_set producible_insert_simp producible_maximal_antichain_set productive_drop_head)
      done
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
    apply (subst produce.code)
    apply (auto split: option.splits)
    subgoal
      apply (subst produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits)
      using producible_insert_same producible_insert_simp apply blast
      done
    subgoal
      using less_eq_sum.cases by fastforce
    subgoal
      apply (subst produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits)
      apply (metis maximal_complete_insert not_Some_eq producible_buf_produce_inner_union_op_None_False producible_insert_simp union_op_maximal_complete)
      done
    subgoal for z
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits if_splits)
      apply (metis maximal_complete_insert maximal_complete_maximal_antichain_set not_producible_maximal_antichain_set option.simps(5) produce.code produce_union_op_completeness_with_buffer producible_insert_simp)
      subgoal
        using maximal_complete_insert not_producible_maximal_antichain_set producible_insert_same by blast
      subgoal
        by (meson maximal_complete_insert maximal_complete_maximal_antichain_set not_producible_maximal_antichain_set produce_union_op_completeness_with_buffer producible_insert_simp)
      subgoal
        by (meson maximal_complete_insert maximal_complete_maximal_antichain_set not_producible_maximal_antichain_set produce_union_op_completeness_with_buffer producible_insert_simp)
      done
    subgoal
      apply (subst produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto 0 0 simp add: filter_empty_conv split: list.splits if_splits sum.splits)
      subgoal
        using maximal_complete_insert producible_insert_same producible_maximal_antichain_set by blast
      subgoal
        using maximal_complete_insert not_producible_maximal_antichain_set producible_insert_same by blast
      subgoal
        by (metis (mono_tags, lifting) Inr_leq image_eqI maximal_complete_insert mem_Collect_eq not_producible_maximal_antichain_set old.sum.simps(5) old.sum.simps(6) producible_insert_simp)
      subgoal
        by (smt (verit, del_insts) Inl_leq imageI maximal_complete_insert mem_Collect_eq not_producible_maximal_antichain_set old.sum.simps(5) old.sum.simps(6) producible_insert_simp)
      subgoal
        by (metis (mono_tags, lifting) Inr_leq event.inject(2) image_eqI maximal_complete_insert mem_Collect_eq not_producible_maximal_antichain_set old.sum.simps(5) old.sum.simps(6) producible_insert_simp set_ConsD set_filter)
      subgoal
        by (metis (mono_tags, lifting) Inr_leq event.inject(2) image_eqI maximal_complete_insert mem_Collect_eq old.sum.simps(5) old.sum.simps(6) producible_insert_simp producible_maximal_antichain_set set_ConsD set_filter)
      subgoal
        by (smt (verit, ccfv_threshold) Inl_inject Inl_leq image_iff insert_iff list.simps(15) maximal_complete_insert mem_Collect_eq not_producible_maximal_antichain_set old.sum.simps(5) old.sum.simps(6) producible_insert_simp set_filter)
      subgoal
        by (metis (mono_tags, lifting) Inl_leq event.inject(2) image_eqI maximal_complete_insert mem_Collect_eq not_producible_maximal_antichain_set old.sum.simps(5) old.sum.simps(6) producible_insert_simp set_ConsD set_filter)
      done
    done
  subgoal for x' lxs buf1 buf2
    apply (subst produce.code)
    apply (auto split: option.splits)
    subgoal
      by (meson lset_intros(1) lset_intros(2) option.exhaust producible_def producible_stream_produce_inner_union_op_None_False vimage_eq)
    subgoal
      apply hypsubst_thin
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits if_splits)
      apply (drule meta_spec[of _ "x # buf1"])
      apply (drule meta_spec[of _ "maximal_antichain_set (insert x buf2)"])
      apply (drule meta_mp)
      defer
      apply (drule meta_mp)
      apply simp
      apply (auto split: option.splits)
      apply (simp add: produce.code)
      done
    subgoal
      by (metis lset_intros(2) option.exhaust producible_def producible_stream_produce_inner_union_op_None_False vimage_eq)
    subgoal
      apply hypsubst_thin
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits if_splits event.splits)
      subgoal
        by (metis maximal_complete_maximal_antichain_set option.simps(5) produce.code)
      done
    subgoal
      apply hypsubst_thin
      apply (subst produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits if_splits event.splits)
      subgoal for z
        apply (drule meta_spec[of _ "z # buf1"])
        apply (drule meta_spec[of _ "maximal_antichain_set (insert z buf2)"])
        apply (drule meta_mp)
        defer
        apply (drule meta_mp)
        apply simp
        apply (auto simp add: produce_inner_None_produce_LNil)
        done
      done
    subgoal
      apply hypsubst_thin
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: filter_empty_conv split: list.splits if_splits event.splits)
      subgoal
        by (metis (mono_tags, lifting) insert_iff list.simps(15) maximal_complete_insert option.simps(5) produce.code union_op_maximal_complete)
      subgoal
        by (meson maximal_complete_insert not_producible_maximal_antichain_set producible_insert_same)
      subgoal
        by (metis (no_types, lifting) filter_set image_eqI maximal_complete_insert maximal_complete_maximal_antichain_set mem_Collect_eq member_filter not_producible_maximal_antichain_set producible_insert_simp)
      subgoal
        by (metis (mono_tags, lifting) filter_set image_eqI insert_iff list.simps(15) maximal_complete_insert maximal_complete_maximal_antichain_set member_filter not_producible_maximal_antichain_set producible_insert_simp)
      done
    done
  done

lemma produce_inner_union_op_producible_produces_Inl:
  "produce_inner op_lxs = r \<Longrightarrow>
   op_lxs = (union_op buf1 buf2, stream_in) \<Longrightarrow>
   \<not> lfinite stream_in \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   \<forall>wm. Watermark wm \<in> lset stream_in \<longrightarrow> producible wm (buf2 \<union> Watermark -` lset stream_in) \<Longrightarrow>
   \<exists> y. r = Some (Inl y)"
  apply (cases r)
  subgoal
    apply hypsubst_thin
    apply (cases stream_in)
    apply auto
    subgoal for x xs
      apply (subst (asm) (1) produce_inner.simps)
      apply (auto 2 1 simp add: filter_empty_conv split: if_splits prod.splits list.splits event.splits llist.splits)
      by (smt (z3) maximal_complete_insert producible_buf_produce_inner_union_op_None_False producible_def producible_insert_simp producible_stream_produce_inner_union_op_None_False producible_union union_op_maximal_complete vimage_eq)
    done
  subgoal for y
    apply (cases y)
    apply auto
    using produce_inner_Some_Inr_lfinite by blast
  done

lemma produce_inner_union_monotone_Inl_Data_2:
  "produce_inner oo = Some r \<Longrightarrow> 
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data t d \<Longrightarrow>
   oo = (union_op buf1 buf2, lxs) \<Longrightarrow>
   maximal_complete buf2 \<Longrightarrow>
   xs = [] \<and>
   (\<exists> n buf1' buf2'. lxs' = ldropn n lxs \<and> 0 < n \<and>
     buf2' = maximal_antichain_set ((Watermark -` lset (ltake n lxs)) \<union> buf2) \<and>
     buf1' = ((rev (List.map_filter (case_event (\<lambda> _ _. None)
               (\<lambda> wm . Some wm)) 
               ((list_of (ltake n lxs))))) @ buf1) \<and>
     op = (union_op buf1' buf2'))"
  apply (induct oo r arbitrary: buf1 buf2 lxs x xs lxs' op  rule: produce_inner_alt[consumes 1])
  prefer 2
  subgoal for op h x xs lxs lxs' lgc' buf1 buf2 lxs'' xa xsa lxs'a opa
    apply (subst (asm) produce_inner.simps)
    apply simp
    apply (cases lxs'')
    apply simp_all
    apply (intro conjI)
    subgoal
      apply (auto 2 1 split: sum.splits event.splits)
      done
    subgoal
      apply (auto 2 1 split: sum.splits event.splits)
      subgoal
        apply hypsubst_thin
        apply (rule exI[of _ 1])
        apply auto
        subgoal
          by (smt (verit, del_insts) Un_commute append_self_conv2 event.simps(5) list_of_LNil lset_LNil ltake_eq_LNil_iff map_filter_empty map_filter_simps(2) rev_is_Nil_conv set_ConsD sup_bot.right_neutral union_op_maximal_complete vimage_empty zero_enat_def)
        done
      subgoal
        apply hypsubst_thin
        apply (rule exI[of _ 1])
        apply auto
        subgoal
          by (smt (verit, del_insts) Un_commute append_self_conv2 event.simps(5) list_of_LNil lset_LNil ltake_eq_LNil_iff map_filter_empty map_filter_simps(2) rev_is_Nil_conv set_ConsD sup_bot.right_neutral union_op_maximal_complete vimage_empty zero_enat_def)
        done
      done
    done
  subgoal for op h lxs lgc' zs buf1 buf2 lxsa x xs lxs' opa
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
  apply auto
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
        apply (auto simp add: maximal_antichain_set_single producible_maximal_antichain_set map_filter_simps split: sum.splits; hypsubst_thin)
        done
      subgoal
        by (smt (verit, del_insts) Un_commute append_self_conv2 event.simps(5) list_of_LNil lset_LNil ltake_eq_LNil_iff map_filter_empty map_filter_simps(2) rev_is_Nil_conv set_ConsD sup_bot.right_neutral union_op_maximal_complete vimage_empty zero_enat_def)
      done
    subgoal for wm'
      apply (auto simp add: ltake_enat_0 maximal_antichain_set_single producible_maximal_antichain_set map_filter_simps split: sum.splits; hypsubst_thin)
      apply (metis (no_types, lifting) filter_cong)+
      done
    subgoal for wm'
      apply (auto simp add: ltake_enat_0 maximal_antichain_set_single producible_maximal_antichain_set map_filter_simps split: sum.splits; hypsubst_thin)
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
    apply (auto split: option.splits sum.splits)
    apply (metis option.distinct(1) produce_inner_union_op_producible_produces_Inl)
    using enat_0 apply fastforce
    using produce_inner_Some_Inr_lfinite apply blast
    done
  subgoal for n buf1 buf2 stream_in
    apply (subst (asm) (2) produce.code)
    apply (auto split: option.splits sum.splits)
    apply (metis llength_LNil produce_inner_None_produce_LNil zero_le)
    subgoal for op x xs lxs
      apply (cases x)
      subgoal for t d
        apply hypsubst_thin
        apply (drule produce_inner_union_monotone_Inl_Data_2)
        apply (rule refl)+
        apply assumption
        apply (elim exE conjE)
        subgoal for n buf1' buf2'
          apply (drule meta_spec[of _ buf1'])
          apply (drule meta_spec[of _ buf2'])
          apply (drule meta_spec[of _ lxs])
          apply (drule meta_mp)
          subgoal
            apply auto
            apply (metis eSuc_enat eSuc_ile_mono)
            done
          apply (drule meta_mp)
          apply force
          apply (drule meta_mp)
          subgoal
            apply auto
            subgoal for wm
              apply (drule spec[of _ wm])
              apply (drule mp)
              apply (meson in_lset_ldropnD)
              apply hypsubst_thin
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
          apply (drule meta_spec[of _ lxs])
          apply (drule meta_mp)
          subgoal
            apply (auto simp flip: eSuc_enat)
            apply hypsubst_thin
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
            apply auto
            apply hypsubst_thin
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
    apply auto
    apply hypsubst_thin
    apply (subst (asm) produce_skip_n_productions_op_correctness)
    apply auto
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
  apply (auto simp add: in_lset_conv_lnth)
  subgoal for n
    apply (frule productive_find_bigger_watermark)
    apply assumption+
    apply auto
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
                apply (rule refl)+
                apply assumption+
                apply auto
                apply (metis ldrop_enat productive_ldrop)
                done
              subgoal
                apply (drule produce_inner_union_monotone_Inl_Data_2)
                apply (rule refl)+
                apply assumption+
                apply auto
                apply (intro exI conjI)
                prefer 3
                apply (rule refl)
                using maximal_complete_maximal_antichain_set apply blast
                apply auto
                subgoal for n wm
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
              done
            subgoal 
              apply (drule produce_inner_union_monotone_Inl_Data_2)
              apply (rule refl)+
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
                apply auto
                apply (metis ldrop_enat productive_ldrop)
                done
              subgoal
                apply (drule produce_inner_union_monotone_Inl_Watermark_2)
                apply (rule refl)+
                apply assumption+
                apply auto
                apply (intro exI conjI)
                prefer 3
                apply (rule refl)
                using maximal_complete_maximal_antichain_set apply blast
                apply auto
                subgoal for n wm
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
              done
            subgoal 
              apply (drule produce_inner_union_monotone_Inl_Watermark_2)
              apply (rule refl)+
              apply assumption+
              apply auto
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
  apply (auto split: list.splits event.splits prod.splits)
  done

end