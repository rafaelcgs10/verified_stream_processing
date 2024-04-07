theory Batch_Op
  imports
    "../Watermarked_Stream"
    "../Llists_Processors"
    "../Sum_Order"
    "../Antichain"
    "HOL-Library.Code_Lazy"
begin

section \<open>batch_op\<close>

fun batches where
  "batches ((t::_::order)#tss) xs = (let (bs, xs') = batches tss [(t', d) \<leftarrow> xs. \<not> t' \<le> t] in
   (Data t [(t', d) \<leftarrow> xs. t' \<le> t] # bs, xs'))"
| "batches [] xs = ([], xs)"

lemma no_watermark_in_batches[simp]:
  "Watermark wm \<notin> set (fst (batches A buf))"
  apply (induct A buf rule: batches.induct)
   apply (auto split: prod.splits)
  done

lemma sync_batches_le_wm:
  "Data wm batch \<in> set (fst (batches A buf)) \<Longrightarrow>
   \<forall> t \<in> fst ` set batch. t \<le> wm"
  apply (induct A buf arbitrary: buf rule: batches.induct)
   apply (auto split: if_splits prod.splits)
  apply (metis fst_eqD)
  done

lemma sync_batches_from_buf:
  "Data wm batch \<in> set (fst (batches A buf)) \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   (t, d) \<in>  set buf"
  apply (induct A buf arbitrary: buf rule: batches.induct)
   apply (auto split: if_splits prod.splits)
  apply (metis filter_is_subset fst_eqD subsetD)
  done

lemma in_sync_batches_all_Data[simp]:
  "\<forall> x \<in> set (fst (batches A buf)). is_Data x"
  by (metis event.collapse(2) no_watermark_in_batches)

lemma sync_batches_batches_uniques:
  "batch' \<noteq> batch \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   t \<in> fst ` set batch' \<Longrightarrow> 
   Data wm' batch' \<in> set (fst (batches A buf)) \<Longrightarrow>
   Data wm batch \<in> set (fst (batches A buf)) \<Longrightarrow>
   False"
  apply (induct A arbitrary: buf )
   apply (auto simp add: distinct_map  split: event.splits if_splits)
  apply (smt (verit, best) case_prod_unfold event.inject(1) filter_set fst_conv member_filter set_ConsD sync_batches_from_buf)
  done


(* FIXME: move me to utils *)
lemma count_list_1_take:
  "n' < length xs \<Longrightarrow>
   n' \<le> n \<Longrightarrow>
   xs ! n' = x  \<Longrightarrow>
   count_list xs x = 1 \<Longrightarrow>
   count_list (take (Suc n) xs) x = 1"
  apply (induct xs arbitrary: n' n)
   apply auto
   apply (meson count_list_0_iff in_set_takeD)
  subgoal for a xs n' n
    apply (cases n')
     apply auto
    using Suc_less_eq2 le_eq_less_or_eq apply auto
    done
  done

(* FIXME: move me to utils *)
lemma count_list_filter:
  "P x \<Longrightarrow>
   count_list (filter P xs) x = count_list xs x"
  apply (induct xs)
   apply auto
  done
lemma count_list_map_the_case_event:
  "(\<forall> x \<in> set xs. is_Data x) \<Longrightarrow>
   count_list (map (the \<circ> case_event (\<lambda>t d. Some (t, d)) Map.empty) xs) (wm, batch) = count_list xs (Data wm batch)"
  apply (induct xs)
   apply (auto simp add: event.case_eq_if event.expand)
  done
    (* FIXME: move me *)
lemma mset_Collect_fst[simp]:
  "{#x \<in># M. P (fst x) #} = {#(t', d) \<in># M. P t'#}"
  by (simp add: case_prod_beta')


lemma sync_batches_before_n:
  "fst (batches A buf) ! n = Data wm batch \<Longrightarrow>
   n < length (fst (batches A buf)) \<Longrightarrow>
   t \<in> fst ` set buf \<Longrightarrow>
   wm' \<in> set A \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   t \<le> wm' \<Longrightarrow>
   \<exists>n'\<le>n. \<exists>wm' batch'. fst (batches A buf) ! n' = Data wm' batch' \<and> t \<in> fst ` set batch'"
  apply (induct A buf arbitrary: n rule: batches.induct)
   apply (auto 2 1 simp add: rev_image_eqI split_beta split: prod.splits if_splits)
   apply (metis (mono_tags, lifting) bot_nat_0.not_eq_extremum case_prodI filter_set fst_conv image_eqI le_eq_less_or_eq member_filter nth_Cons_0)
  subgoal for wm' wss buf n
    apply (cases n)
    subgoal
      apply auto
      using image_iff apply fastforce
      done
    subgoal for n''
      apply auto
      apply hypsubst_thin
      apply (metis (mono_tags, lifting) Domain.DomainI Suc_le_mono bot_nat_0.extremum case_prod_unfold fst_eq_Domain mem_Collect_eq nth_Cons_0 nth_Cons_Suc set_filter)
      done
    done
  done

lemma t_in_concat_coll_list_eq:
  "Data wm batch \<in> set (fst (batches A buf)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow> t \<le> wm \<Longrightarrow>
   mset (coll_list buf t) = mset (coll_list batch t)"
  unfolding coll_list_def
  apply (induct A buf arbitrary: buf rule: batches.induct)
   apply (auto split: prod.splits if_splits)
   apply (metis (mono_tags, lifting) Pair_inject case_prod_unfold prod.collapse)
  apply (smt (verit, best) case_prod_unfold empty_filter_conv filter_mset_cong fst_conv image_mset_is_empty_iff mset_filter mset_mfilter_simp_cong mset_zero_iff_right)
  done

lemma sync_batches_linorder:
  "fst (batches (maximal_antichain_list (map fst (buf::('t::linorder \<times> _) list))) buf) = (if buf = [] then [] else [Data (Max (fst ` set buf)) buf])"
  apply (induct buf)
   apply (auto simp add: maximal_antichain_linorder case_prod_unfold leI null_rec(1) null_rec(2))
  done

lemma sync_batches_no_empty_batch:
  "distinct A \<Longrightarrow>
   maximal_antichain_spec A \<Longrightarrow>
   set A \<subseteq> fst ` set buf \<Longrightarrow>
   (\<forall> wm \<in> set A. \<exists> t \<in> fst ` set buf. t \<le> wm) \<Longrightarrow>
   Data wm batch \<in> set (fst (batches A buf)) \<Longrightarrow>
   wm \<in> fst ` set batch"
  apply (induct A arbitrary: buf)
   apply (auto split: if_splits prod.splits)
  subgoal for t A buf x1 x2 aa b
    by (smt (verit) case_prod_unfold dual_order.order_iff_strict fst_conv image_iff mem_Collect_eq set_filter subset_iff)
  done

lemma takeWhile_maximal_antichain_sync_batches:
  "maximal_antichain_spec A \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   x \<in> set (takeWhile ((\<noteq>) wm) A) \<Longrightarrow>
   t \<le> x \<Longrightarrow>
   Data wm batch \<in> set (fst (batches A buf)) \<Longrightarrow>
   False"
  apply (induct A arbitrary: buf)
   apply (auto split: if_splits prod.splits)
   apply (metis case_prodD filter_set fst_eqD member_filter sync_batches_from_buf)
  apply (metis fst_conv)
  done

lemma sync_batches_batch_correct:
  "maximal_antichain_spec A \<Longrightarrow>
   distinct A \<Longrightarrow>
   Data wm batch \<in> set (fst (batches A buf)) \<Longrightarrow>
   batch = filter (\<lambda> (t, d). t \<le> wm \<and> (\<forall>x\<in>set (takeWhile ((\<noteq>) wm) A). \<not> t \<le> x)) buf \<and> wm \<in> set A"
  apply (induct A arbitrary: buf)
   apply simp
  subgoal for a A buf
    apply (auto 6 1 simp add: split_beta split: if_splits prod.splits)
    subgoal
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (simp add: split_beta split: prod.splits)
      apply (rule filter_cong)
       apply auto
      done
    done
  done

lemma drop_sync_batches_wm_not_again:
  "wm' \<le> wm \<Longrightarrow>
   maximal_antichain_spec A \<Longrightarrow>
   distinct A \<Longrightarrow>
   drop n (fst (batches A buf)) = Data wm batch # xs \<Longrightarrow>
   Data wm' batch' \<in> set xs \<Longrightarrow>
   False"
  apply (induct A arbitrary: buf n)
   apply (auto split: if_splits prod.splits)
  subgoal for a A buf n aa b
    apply (cases n)
     apply auto
     apply (metis (no_types, lifting) dual_order.order_iff_strict fst_conv sync_batches_batch_correct)
    apply (metis fst_conv)
    done
  done


lemma in_sync_batches:
  "maximal_antichain_spec A \<Longrightarrow>
   (t, d) \<in> set buf \<Longrightarrow>
   wm \<in> set A \<Longrightarrow> t \<le> wm \<Longrightarrow>
   \<exists>wm out. Data wm out \<in> set (fst (batches A buf)) \<and> (t, d) \<in> set out"
  apply (induct A arbitrary: buf)
   apply (auto split: if_splits prod.splits)
   apply (metis case_prodI filter_set member_filter)
  apply (metis case_prodI filter_set fst_conv member_filter)
  done

lemma sync_batches_skip_useless:
  "\<forall> (t, d) \<in> set ys. \<not> (\<exists> wm \<in> set A. t \<le> wm) \<Longrightarrow>
   fst (batches A (ys@xs)) = fst (batches A xs)"
  apply (induct A arbitrary: ys xs)
   apply (auto split: prod.splits)
   apply (metis (mono_tags, lifting) case_prod_unfold filter_False prod.collapse)
  apply (smt (verit, best) case_prodI2 filter_True fst_conv)
  done

lemma sync_batches_monotone:
  "\<forall> t \<in> set A. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   monotone (llist_of (fst (batches A buf))) WM"
  apply (induct A arbitrary: buf WM)
   apply (auto simp add: monotone.LNil split_beta split: prod.splits)
  apply (rule LConsL)
   apply fast
  apply blast
  done

lemma sync_batches_unique_data:
  "distinct A \<Longrightarrow>
   maximal_antichain_spec A \<Longrightarrow>
   set A \<subseteq> fst ` set buf \<Longrightarrow>
   Data wm batch \<in> set (fst (batches A buf)) \<Longrightarrow>
   count_list (map data (fst (batches A buf))) batch = Suc 0"
  apply (induct A buf arbitrary: buf rule: batches.induct)
   apply (auto simp add: distinct_map count_list_0_iff  split: event.splits if_splits prod.splits)
    apply (metis (no_types, lifting) case_prod_conv dual_order.order_iff_strict event.exhaust_sel filter_set fst_conv member_filter no_watermark_in_batches sync_batches_from_buf)
   apply (metis case_prod_conv dual_order.refl filter_set fst_conv member_filter sync_batches_from_buf)
  apply (smt (verit, ccfv_threshold) case_prod_unfold filter_set fst_conv image_iff member_filter nless_le subsetD subsetI)
  done

primcorec batch_op :: "('t::order \<times> 'd) list \<Rightarrow> (('t, 'd) event, ('t, ('t \<times> 'd) list) event) op" where
  "batch_op buf = Logic (\<lambda> ev.
     case ev of
       Data t d \<Rightarrow> (batch_op (buf @ [(t, d)]), [])
     | Watermark wm \<Rightarrow> let (out, buf') = batches [wm] buf in (batch_op buf', [x \<leftarrow> out. data x \<noteq> []] @ [Watermark wm]))
   (let wms = maximal_antichain_list (map fst buf) ;
        (bts, _) = batches wms buf in
        llist_of bts)"

declare batch_op.sel(1)[simp del]


lemma batch_op_sel1[simp]:
  "apply (batch_op buf) = (\<lambda>ev. case ev of Data t d \<Rightarrow> (batch_op (buf @ [(t, d)]), [])
    | Watermark wm \<Rightarrow>
          if \<exists>(t, d)\<in>set buf. t \<le> wm then (batch_op (snd (batches [wm] buf)), [hd (fst (batches [wm] buf)), Watermark wm])
          else (batch_op buf, [Watermark wm]))"
  apply (subst batch_op.sel(1))
  apply (rule ext)
  apply (auto split: if_splits event.splits prod.splits)
  apply (metis case_prodI filter_neq_nil_iff)
  done              

subsection \<open>Auxiliary lemmas\<close> 
lemma batch_op_buf_order_empty_lgc_preserves:
  "apply (batch_op buf) h = (lgc1, []) \<Longrightarrow>
   (\<exists> wm. h = Watermark wm \<and> lgc1 = (batch_op buf) \<and> \<not> (\<exists> (t, d) \<in> set buf . t \<le> wm)) \<or> (\<exists> t d . h = Data t d \<and> lgc1 = (batch_op (buf @ [(t,d)])))"
  apply (auto split: event.splits prod.splits list.splits if_splits)
  done

lemma batch_op_buf_some_out_lgc_preserves:
  "apply (batch_op buf) h = (lgc1, x#xs) \<Longrightarrow>
   (\<exists> wm d. h = Watermark wm \<and> (\<exists> (t, d) \<in> set buf . t \<le> wm) \<and> lgc1 = (batch_op (filter  (\<lambda> (t, _) . \<not> t \<le> wm) buf)) \<and> x = Data wm d \<and> xs = [Watermark wm]) \<or>
   (\<exists> wm . h = Watermark wm \<and> xs = [] \<and> x = Watermark wm \<and> lgc1 = (batch_op buf) \<and> \<not> (\<exists> (t, d) \<in> set buf . t \<le> wm))"
  apply (auto split: event.splits prod.splits list.splits if_splits)
  done

lemma produce_lhd_data:
  "lhd' lxs = Some (Data t d) \<Longrightarrow>
   produce (batch_op (buf @ [(t, d)])) (ltl lxs) = produce (batch_op buf) lxs"
  apply (subst (2) produce.code)
  apply (subst produce_inner.simps)
  apply (auto split: sum.splits llist.splits event.splits option.splits)
   apply (subst produce.code)
   apply simp
  apply (subst produce.code)
  apply simp
  done

lemma produce_inner_Some_inversion:
  "produce_inner (batch_op buf, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs', lxs') \<Longrightarrow>
   (\<exists> n wm t d. wm \<ge> t \<and> lnth lxs n = Watermark wm \<and> n < llength lxs \<and> ((t, d) \<in> set buf \<or> Data t d \<in> lset (ltake (enat n) lxs))) \<or>
   (\<exists> wm . x = Watermark wm \<and> xs' = [])"
  apply (induct "(batch_op buf, lxs)" r arbitrary: buf lxs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs buf
    apply (frule batch_op_buf_order_empty_lgc_preserves)
    apply (elim conjE disjE exE)
    subgoal for wm
      apply hypsubst_thin
      subgoal premises p2
        using p2(2)[where buf="buf"] apply -
        using p2(1) apply -
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
         apply (rule refl)
        apply (elim conjE disjE exE)
        subgoal for n wm t' d'
          apply (metis in_lset_conv_lnth llist.set_intros(2))
          done
        subgoal for n wm t' d'
          apply (metis Extended_Nat.eSuc_mono eSuc_enat llength_LCons llist.set_intros(2) lnth_Suc_LCons ltake_eSuc_LCons)
          done
        apply blast
        done
      done
    subgoal for t d
      apply hypsubst_thin
      subgoal premises p2
        using p2(2)[where buf="buf @ [(t, d)]"] apply -
        using p2(1) apply -
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
         apply (rule refl)
        apply (elim conjE disjE exE)
        subgoal for n wm t' d'
          apply(rule disjI1)
          apply (rule exI[of _ "Suc n"])
          apply (rule exI[of _ wm])
          apply (metis Suc_ile_eq Un_iff eSuc_enat empty_iff empty_set fst_conv iless_Suc_eq llength_LCons llist.set_intros(1) lnth_Suc_LCons ltake_eSuc_LCons set_ConsD set_append)
          done
        subgoal for n wm t' d'
          apply(rule disjI1)
          apply (rule exI[of _ "Suc n"])
          apply (rule exI[of _ wm])
          apply (metis Extended_Nat.eSuc_mono eSuc_enat llength_LCons llist.set_intros(2) lnth_Suc_LCons ltake_eSuc_LCons)
          done
        subgoal for wm
          apply(rule disjI2)
          apply (rule exI[of _ wm])
          apply simp
          done
        done
      done
    done
  subgoal for h buf
    apply (frule batch_op_buf_some_out_lgc_preserves)
    apply (elim conjE disjE exE)
    subgoal for wm
      apply (metis (no_types, lifting) case_prodE in_lset_conv_lnth llist.set_intros(1))
      done
    apply blast
    done
  apply simp
  done

(* FIXME: move to completeness *)
lemma produce_inner_conditions_to_produce_aux:
  "x \<in> lset lxs \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   wm \<ge> t \<Longrightarrow>
   n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   ((t, d) \<in> set buf \<or> (lnth lxs m = Data t d \<and> m < n)) \<Longrightarrow>
   \<exists> buf' wm' batch lxs' . (produce_inner (batch_op buf, lxs) =
   Some (Inl (batch_op buf', Data wm' batch, [Watermark wm'], lxs')) \<and> (n = 0 \<longrightarrow> (t, d) \<in> set buf \<longrightarrow> (t, d) \<in> set batch)) \<or>
   (produce_inner (batch_op buf, lxs) = Some (Inl (batch_op buf', Watermark wm', [], lxs')))"
  apply (induct lxs arbitrary: buf n m t d wm rule: lset_induct)
  subgoal for xs buf
    apply hypsubst_thin
    apply (elim disjE)
    subgoal
      apply (subst (1 2) produce_inner.simps)
      apply (auto simp del: batch_op_sel1 batch_op.simps split: prod.splits list.splits llist.splits event.splits option.splits)
       apply (smt (verit, best) case_prodI event.simps(6) list.simps(3) prod.simps(1) batch_op_sel1 batch_op.sel(2))
      apply (frule batch_op_buf_some_out_lgc_preserves)
      apply (elim exE conjE disjE)
      subgoal for x1 x21 x22 wm' d'
        apply simp
        apply safe
         apply hypsubst_thin
         apply (smt (verit, ccfv_threshold) Pair_inject case_prodI event.inject(1) event.simps(6) list.inject mem_Collect_eq set_filter batch_op.simps)
        apply simp
        done
      subgoal
        apply blast
        done
      done
    subgoal
      apply (subst (1 2) produce_inner.simps)
      apply (auto split: option.splits)
      done
    done
  subgoal for x' xs buf n m t d wm
    apply hypsubst_thin
    apply (subgoal_tac "n \<noteq> 0")
     defer
     apply (metis lnth_0)
    apply (subst (1 2) produce_inner.simps)
    apply (auto split: event.splits prod.splits list.splits llist.splits option.splits)
    subgoal premises p for t' d'
      using p(1,3-) apply -
      using p(2)[where t=t and n="n - 1" and d=d and buf="buf @ [(t', d')]"] apply -
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply fast
      apply (drule meta_mp)
       apply (metis Suc_diff_1 Suc_ile_eq)
      apply (drule meta_mp)
       apply (simp add: lnth_LCons')
      apply (drule meta_mp)
       apply (rule disjI1)
       apply auto
      done
    subgoal for t' d'
      apply (cases n)
       apply auto
      subgoal for n'
        apply (cases m)
         apply auto
         apply (metis Suc_ile_eq Un_iff list.set_intros(1) set_append strict_monotone_drop_head)
        subgoal for m'
          apply hypsubst_thin
          apply (drule meta_spec)
          apply (drule meta_spec[of _ n'])
          apply (drule meta_spec[of _ m'])
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply assumption
          apply (drule meta_mp)
          using Suc_ile_eq apply blast
          apply (drule meta_mp)
           apply blast
          apply (simp add: lnth_LCons')
          apply (drule meta_mp)
           apply (rule disjI2)
           apply simp
          apply auto
          done
        done
      done
    done
  done

(* FIXME: move to completeness *)
lemma produce_inner_conditions_to_produce:
  "monotone lxs WM \<Longrightarrow>
   wm \<ge> t \<Longrightarrow>
   n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   ((t, d) \<in> set buf \<or> (lnth lxs m = Data t d \<and> m < n)) \<Longrightarrow>
   \<exists> buf' wm' batch lxs' . (produce_inner (batch_op buf, lxs) = Some (Inl (batch_op buf', Data wm' batch, [Watermark wm'], lxs')) \<and>
   (n = 0 \<longrightarrow> (t, d) \<in> set buf \<longrightarrow> (t, d) \<in> set batch)) \<or>
   (produce_inner (batch_op buf, lxs) = Some (Inl (batch_op buf', Watermark wm', [], lxs')))"
  apply (rule produce_inner_conditions_to_produce_aux)
       defer
       apply assumption+
  apply (metis in_lset_conv_lnth)
  done

lemma produce_inner_batch_op_op_watermark_inversion:
  "produce_inner (batch_op buf, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   xs = [] \<Longrightarrow>
   \<exists> buf' . op = batch_op buf'"
  apply (induct "(batch_op buf, lxs)" r arbitrary: buf lxs wm op rule: produce_inner_alt[consumes 1])
    apply (auto split: if_splits event.splits)
  done


lemma produce_inner_batch_op_specify_Some:
  "produce_inner (batch_op buf, lxs) = Some (Inl (op, x, xs, lxs')) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> buf' wm d lxs'. produce_inner (batch_op buf, lxs) = Some (Inl (batch_op buf', Data wm d, [Watermark wm], lxs')) \<or> 
   produce_inner (batch_op buf, lxs) = Some (Inl (batch_op buf', Watermark wm, [], lxs'))"
  apply (frule produce_inner_Some_inversion)
   apply safe
        apply (rule refl)+
  subgoal
    apply (drule produce_inner_conditions_to_produce[where buf=buf])
        apply simp_all
     apply (rule disjI1)
     apply assumption
    apply auto
    done
  subgoal for n wm t d
    apply (auto simp add: in_lset_conv_lnth)
    subgoal for m
      apply (drule produce_inner_conditions_to_produce[where buf=buf and n=n and m=m and d=d])
          apply simp_all
      apply (rule disjI2)
      apply (auto simp add: lnth_ltake)
      done
    done
  subgoal for wm
    using produce_inner_batch_op_op_watermark_inversion 
    by blast
  done


lemma not_in_buf_produce_Watermark:
  "\<not> (\<exists> (t, d) \<in> set buf . t \<le> wm) \<Longrightarrow>
   produce (batch_op buf) (LCons (Watermark wm) lxs) = LCons (Watermark wm) (produce (batch_op buf) lxs)"
  apply (subst (1 2) produce.code)
  apply (subst (1) produce_inner.simps)
  apply (auto split: llist.splits event.splits prod.splits list.splits option.splits sum.splits)
  using produce_inner_None_produce_LNil apply blast
  apply (subst produce.code)
  apply (auto split: llist.splits event.splits prod.splits list.splits option.splits sum.splits)  
  done

lemma produce_Data:
  "produce (batch_op buf) (LCons (Data t d) lxs) = produce (batch_op (buf@[(t, d)])) lxs"
  apply (subst (1 2) produce.code)
  apply (subst (1) produce_inner.simps)
  apply (auto split: llist.splits event.splits prod.splits list.splits option.splits)
  done

lemma produce_inner_batch_op_inversion:
  "produce_inner (batch_op buf, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs', lxs') \<Longrightarrow>
   \<exists> buf' n . lgc' = batch_op buf' \<and> lxs' = ldropn n lxs \<and> n > 0"
  subgoal premises prems
    using prems apply -
    apply (induct "(batch_op buf, lxs)" r arbitrary: buf lxs rule: produce_inner_alt)
    using prems apply simp
    subgoal for h lxs lgc'a zs buf
      apply (subst (asm) (1) produce_inner.simps)
      apply (simp split: llist.splits event.splits)
      subgoal for  t d
        apply hypsubst_thin
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply (rule refl)
        apply (metis ldropn_Suc_LCons zero_less_Suc)
        done
      subgoal for wm
        apply hypsubst_thin
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply (rule refl)
        apply (auto split: if_splits prod.splits)
        apply (metis ldropn_Suc_LCons zero_less_Suc)+
        done
      subgoal 
        by (metis Pair_inject list.discI)
      subgoal 
        by (meson Pair_inject list.discI)
      done
    subgoal for h buf
      apply (subst (asm) produce_inner.simps)
      apply (simp split: llist.splits event.splits if_splits)
       apply (metis ldropn_0 ldropn_Suc_LCons zero_less_Suc)
      apply (metis ldropn_0 ldropn_Suc_LCons zero_less_Suc)
      done
    apply auto
    done
  done

lemma produce_inner_batch_op_inversion_2:
  "produce_inner (batch_op buf, lxs) = Some (Inl (lgc', x, xs', lxs')) \<Longrightarrow> \<exists> buf' . lgc' = batch_op buf'"
  using produce_inner_batch_op_inversion by blast

lemma produce_inner_skip_n_productions_op_batch_op_Some_batch:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   \<exists> wm batch. x = Data wm batch \<and> xs = [Watermark wm] \<or> x = Watermark wm \<and> xs = []"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: op buf lxs n rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto split: event.splits if_splits)
      apply (metis skip_n_productions_op_0)+
    done
  subgoal
    apply (auto split: event.splits if_splits)
     apply (metis drop_Cons' drop_Nil list.discI list.inject)
    apply (metis drop_Cons' drop_Nil list.distinct(1) list.inject)
    done
  apply auto
  done

(*FIXME: move me*)
lemma lnth_Suc_concat_map_Data_Watermark:
  "concat (map (\<lambda>wm. [Data wm (P wm), Watermark wm]) xs) ! n = Data wm d \<Longrightarrow>
   n < length (concat (map (\<lambda>wm. [Data wm (P wm), Watermark wm]) xs)) \<Longrightarrow>
   concat (map (\<lambda>wm. [Data wm (P wm), Watermark wm]) xs) ! Suc n = Watermark wm"
  apply (induct xs arbitrary: P n wm d)
   apply auto
  subgoal for a xs out n wm d
    apply (cases n)
     apply auto
    subgoal for n'
      apply (cases n')
       apply auto
      done
    done
  done

lemma produce_skip_n_productions_op_batch_op_n_Data_Suc_n_Watermark:
  "enat n < llength (produce (skip_n_productions_op (batch_op buf) i) lxs) \<Longrightarrow>
   lnth (produce (skip_n_productions_op (batch_op buf) i) lxs) n = Data wm batch \<Longrightarrow>
   lnth (produce (skip_n_productions_op (batch_op buf) i) lxs) (Suc n) = Watermark wm \<or> lfinite lxs"
  apply (induct n arbitrary: i buf wm batch lxs)
  subgoal for i buf wm batch lxs
    apply (subst produce.code)
    apply (subst (asm) (1 2) produce.code)
    apply (auto split: option.splits sum.splits)
    subgoal for op xs lxs'
      using produce_inner_skip_n_productions_op_batch_op_Some_batch[where n=i] apply simp
      apply (subst lnth_shift)
       apply blast
      apply fastforce
      done
    subgoal for xs
      using produce_inner_Some_Inr_lfinite apply blast
      done
    done
  subgoal for n i buf wm batch lxs
    apply (subst produce.code)
    apply (subst (asm) (5) produce.code)
    apply (auto split: option.splits sum.splits)
      apply (simp add: produce_inner_None_produce_LNil)
    subgoal
      apply (drule meta_spec[of _ "Suc i"])
      apply (drule meta_spec[of _ buf])
      apply (drule meta_spec[of _ wm])
      apply (drule meta_spec[of _ batch])
      apply (drule meta_spec[of _ lxs])
      apply (drule meta_mp)
       apply (metis Extended_Nat.eSuc_mono eSuc_enat iless_Suc_eq ldropn_Suc_conv_ldropn leI llength_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_llength_le produce_skip_n_productions_op_correctness)
      apply (drule meta_mp)
      subgoal
        apply (subst produce.code)
        apply (auto split: option.splits sum.splits)
          apply (metis produce_inner_skip_n_productions_op_Some_llength_le produce_inner_skip_n_productions_op_llength_LNil)
         apply (metis produce_inner_skip_n_productions_op_Suc_LCons)
        apply (metis lshift_simps(1) produce_inner_skip_n_productions_op_Some_Some_Some_None)
        done
      apply (metis ldropn_Suc_conv_ldropn leI lnth_Suc_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_llength_le produce_skip_n_productions_op_correctness)
      done
    subgoal for op'
      apply (drule meta_spec[of _ "Suc i"])
      apply (drule meta_spec[of _ buf])
      apply (drule meta_spec[of _ wm])
      apply (drule meta_spec[of _ batch])
      apply (drule meta_spec[of _ lxs])
      apply (drule meta_mp)
       apply (metis add_Suc_shift ldropn_eq_LNil leI less_le_not_le produce_skip_n_productions_op_correctness skip_n_productions_op_sum)
      apply (drule meta_mp)
      subgoal
        apply (subst produce.code)
        apply (auto split: option.splits sum.splits)
        using produce_inner_None_not_lfinite_aux produce_inner_Some_Inr_lfinite apply blast
        using produce_inner_skip_n_productions_op_Some_None_Suc_None apply blast
        subgoal for opp
          apply (frule produce_inner_skip_n_productions_op_Suc_Inr)
           apply (rule refl)
          using produce_inner_Some_Inr_lfinite apply blast
          done
        done
      using produce_inner_Some_Inr_lfinite apply blast
      done
    done
  done

lemma produce_inner_skip_n_productions_op_Some_Data_Watermark_in:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   Watermark wm \<in> lset lxs"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: n buf lxs lxs' xs batch wm lgc' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n buf lxs'a xs lgc'a batch wm
    apply (auto split: if_splits event.splits)
      apply (metis skip_n_productions_op_0)+
    done
  subgoal for h xa xs lxs lxs' lgc' n buf lxs'a xsa batch wm lgc'a
    apply hypsubst_thin
    apply (auto split: if_splits event.splits)
     apply (subgoal_tac "n = 1 \<or> n = 0")
      defer
      apply (metis (mono_tags, lifting) One_nat_def Suc_lessI add.commute bot_nat_0.not_eq_extremum drop_eq_Nil2 leI list.discI list.size(3) list.size(4) plus_1_eq_Suc)
     apply (auto split: if_splits event.splits)
    apply (metis drop_Cons' drop_Nil event.distinct(1) list.distinct(1) nth_Cons_0)
    done
  apply auto
  done

lemma produce_inner_batch_op_Watermark_in:
  "produce_inner (batch_op buf, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   Watermark wm \<in> lset lxs"
  apply (induct "(batch_op buf, lxs)" r arbitrary: lxs lxs' op buf wm batch x xs rule: produce_inner_alt[consumes 1])
    apply (auto split: event.splits if_splits)
  done

lemma in_buf_produce_Watermark:
  "\<exists> (t, d) \<in> set buf . t \<le> wm \<Longrightarrow>
   produce (batch_op buf) (LCons (Watermark wm) lxs) = LCons (Data wm (filter (\<lambda> (t, d) . t \<le> wm) buf)) (LCons (Watermark wm) ((produce (batch_op (filter (\<lambda>(t, _). \<not> t \<le> wm) buf)) lxs)))"
  apply (subst produce.code)
  apply (subst produce_inner.simps)
  apply (simp split: prod.splits list.splits option.splits)
  done

lemma produce_inner_skip_n_productions_op_batch_op_xs:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm]"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: lxs lxs' op buf x xs n rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lxs'a op buf x xs n
    apply (auto simp add:  in_buf_produce_Watermark split: event.splits if_splits)
      apply (metis skip_n_productions_op_0)+
    done
  subgoal for h x xs lxs' lgc' buf n
    apply (auto simp add: in_buf_produce_Watermark split: event.splits if_splits)
     apply (smt (verit, ccfv_threshold) drop_Cons' drop_eq_Nil2 event.distinct(1) event.inject(1) leI length_Cons less_Suc0 list.inject list.size(3))
    apply (metis drop_Cons' drop_Nil event.distinct(1) list.distinct(1) nth_Cons_0)
    done
  apply auto
  done



lemma produce_inner_skip_n_productions_op_in_ts_or_buf_Inr:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   Data wm batch \<in> lset (exit op) \<Longrightarrow>
   t' \<le> wm \<Longrightarrow>
   t' \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t' \<in> ts lxs wm \<or> t' \<in> fst ` set buf"
  subgoal premises prems
    using prems apply -
    apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: lxs op buf n wm batch rule: produce_inner_alt)
    using prems apply simp
      apply (auto 0 0 split: if_splits sum.splits event.splits)
    subgoal
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply (auto split: if_splits)[1]
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply (simp add: rev_image_eqI)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply simp
      apply blast
      done
    subgoal
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply (auto split: if_splits)[1]
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply (simp add: rev_image_eqI)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply (auto split: if_splits)[1]
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply (simp add: rev_image_eqI)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto[1]
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto[1]
       apply (metis fst_conv image_iff)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply (auto split: if_splits)[1]
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply (auto split: if_splits)[1]
       apply (metis fst_conv image_iff)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply (auto split: if_splits)[1]
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal for buf n wm batch b
      apply (simp add: ldrop_llist_of)
      using sync_batches_from_buf apply (metis fst_conv imageI in_set_dropD)
      done
    done
  done

lemma produce_inner_inner_skip_n_productions_batch_op_batch_le:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
  t \<in> fst ` set batch \<Longrightarrow>
   t \<le> wm"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: lxs lxs' op buf x xs n rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto split: if_splits event.splits)
      apply (metis skip_n_productions_op_0)+
    done
  subgoal
    apply (auto split: if_splits event.splits)
     apply (metis (mono_tags, lifting) case_prod_unfold drop0 drop_Suc_Cons event.inject(1) fst_conv less_2_cases list.discI list.inject mem_Collect_eq not_less_iff_gr_or_eq numeral_2_eq_2 set_filter)
    apply (metis list.sel(2) list.sel(3) not_Cons_self tl_drop)
    done
  apply auto
  done

(*FIXME: move these lemmas*)
lemma produce_inner_skip_n_productions_op_batch_op_Inr_not_out_of_the_blue:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<not> (\<exists> d. Data t d \<in> lset lxs) \<Longrightarrow>
   t \<notin> fst ` set buf \<Longrightarrow>
   Data wm batch \<in> lset (exit op) \<Longrightarrow> (t, d) \<in> set batch \<Longrightarrow> False"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: n lxs op buf wm batch rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs n buf op wm batch
    apply (auto split: if_splits event.splits)
    subgoal for t' d
      apply (drule meta_spec[of _ n])
      apply (drule meta_spec[of _ "buf @ [(t', d)]"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply auto[1]
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
       apply assumption
      apply blast
      done
    subgoal for wm t' d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply auto[1]
      apply assumption
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "n - Suc 0"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply auto[1]
      apply assumption
      done
    subgoal for t' d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "buf @ [(t', d)]"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply auto[1]
      apply assumption
      done
    subgoal for wm t' d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply auto[1]
      apply assumption
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply auto[1]
      apply assumption
      done
    done
   apply (auto split: if_splits event.splits)
  apply (metis fst_eqD in_lset_ldropD lset_llist_of rev_image_eqI sync_batches_from_buf)
  done

lemma produce_inner_skip_n_productions_op_batch_op_Inr_in_batch_from_buf_or_lxs:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   Data wm batch \<in> lset (exit op) \<Longrightarrow>  (t, d) \<in> set batch \<Longrightarrow> t \<le> wm \<and> ((t, d) \<in> set buf \<or> Data t d \<in> lset lxs)"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: n lxs op buf wm batch rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs n buf op wm batch
    apply (simp split: if_splits event.splits)
         apply fastforce
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply auto
      done
       apply fast
    subgoal for t' d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "buf @ [(t', d)]"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply auto
      done
    done
   apply (auto simp add: ldrop_llist_of split: if_splits event.splits)
   apply (metis Domain.DomainI fst_eq_Domain in_set_dropD sync_batches_le_wm)
  apply (meson in_set_dropD sync_batches_from_buf)
  done

lemma produce_inner_no_timestamps_out_of_the_blue:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   t \<notin> fst ` set buf \<Longrightarrow>
   \<not> (\<exists> d . Data t d \<in> lset lxs) \<Longrightarrow>
   t \<notin> fst ` set batch"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: lxs lxs' op buf x xs n   rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lxs'a op buf x xs n
    apply (auto split: if_splits event.splits)
    using image_iff apply fastforce 
    using image_iff apply fastforce
       apply (smt (verit, ccfv_threshold) Un_iff append.right_neutral fst_conv image_iff set_ConsD set_append skip_n_productions_op_0)
      apply (metis (no_types, opaque_lifting) Un_insert_right append.right_neutral fst_conv imageI image_insert insert_iff list.set(2) set_append skip_n_productions_op_0)
     apply (smt (verit, best) fst_conv image_iff mem_Collect_eq set_filter skip_n_productions_op_0)
    apply (metis fst_conv imageI skip_n_productions_op_0)
    done
  subgoal for h x xs lxs lxs' lgc' buf n lxs'a op xa xsa
    apply hypsubst_thin
    apply (auto split: if_splits event.splits)
     apply (subgoal_tac "n = 0")
      defer
      apply (metis drop_Cons' drop_Nil list.discI)
     apply auto
     apply (metis list.sel(2) list.sel(3) not_Cons_self tl_drop)
    apply (metis fst_conv imageI)
    done
  apply auto
  done

lemma produce_no_timestamps_out_of_the_blue_aux:
  "produce (skip_n_productions_op (batch_op buf) n) lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   t \<notin> fst ` set buf \<Longrightarrow>
   \<not> (\<exists> d . Data t d \<in> lset lxs) \<Longrightarrow>
   t \<notin> fst ` set batch"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits sum.splits)
   apply (metis (no_types, lifting) fst_eqD produce_inner_no_timestamps_out_of_the_blue produce_inner_skip_n_productions_op_batch_op_xs rev_image_eqI)
  apply (metis fst_conv imageI lset_intros(1) produce_inner_skip_n_productions_op_batch_op_Inr_in_batch_from_buf_or_lxs)
  done

lemma produce_no_timestamps_out_of_the_blue:
  "x \<in> lset lxs' \<Longrightarrow>
   lxs' = produce (skip_n_productions_op (batch_op buf) n) lxs \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   t \<notin> fst ` set buf \<Longrightarrow>
   \<not> (\<exists> d . Data t d \<in> lset lxs) \<Longrightarrow>
   t \<notin> fst ` set batch"
  apply (induct lxs' arbitrary: n rule: lset_induct)
   apply (metis produce_no_timestamps_out_of_the_blue_aux)
  apply (metis produce_skip_n_productions_op_LCons)
  done


lemma produce_inner_skip_n_productions_op_timestamp_not_produced_again_later_aux:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   m > n \<Longrightarrow>
   produce_inner (skip_n_productions_op (batch_op buf) m, lxs) = Some (Inl (lgc', x', xs', lxs'')) \<Longrightarrow>
   x' = Data wm' batch' \<Longrightarrow>
   xs' = [Watermark wm'] \<Longrightarrow>
   t \<notin> fst ` set batch'"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: lxs lxs' op buf x xs n m rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc'a zs buf n lxs'' op x xs m
    apply (simp split: event.splits if_splits option.splits)
    subgoal for t d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "buf @ [(t, d)]"])
      apply (drule meta_spec[of _ "n"])
      apply (drule meta_spec[of _ "lxs''"])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "m"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto
      done
    subgoal for t d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "buf @ [(t, d)]"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "lxs''"])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "m"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec[of _ "lxs''"])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "m - Suc (Suc 0)"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto      
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec[of _ "n - Suc 0"])
      apply (drule meta_spec[of _ "lxs''"])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "m - Suc 0"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto    
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "lxs''"])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "m - Suc (Suc 0)"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto
      done
    subgoal for wm
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "lxs''"])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "m - (Suc 0)"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto
      done
    done
  subgoal for h x xs lxs lxs' lgc'' buf n lxs''' op xa xsa m
    apply hypsubst_thin
    apply (auto split: if_splits event.splits list.splits)
     apply (subgoal_tac "n = 0")
      defer
      apply (metis drop_Cons' drop_Nil list.discI)
     apply auto
     apply (subst (asm) produce_inner.simps)
     apply (auto split: if_splits event.splits list.splits)
      apply hypsubst_thin
      apply (metis list.sel(2) list.sel(3) not_Cons_self tl_drop)
     apply (simp add: drop_Cons')
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits event.splits list.splits)
    subgoal
      using produce_inner_no_timestamps_out_of_the_blue[where wm=wm' and n="m - Suc (Suc 0)" and batch=batch' and
          buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf" and lxs=lxs and op=lgc' and lxs'=lxs'' and t=t] apply simp
      apply (drule meta_spec)+
      apply (drule meta_mp)      
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (simp add: image_iff)
      apply (drule meta_mp)
       apply (meson Data_tail_ahead_of_t)
       apply force
      apply (drule meta_mp)
       apply (meson Data_tail_ahead_of_t LConsR)
      apply force
      done
    subgoal
      using produce_inner_no_timestamps_out_of_the_blue[where wm=wm' and n="0" and batch=batch' and
          buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf" and lxs=lxs and op=lgc' and lxs'=lxs'' and t=t] apply simp
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (simp add: image_iff)
      apply (drule meta_mp)
       apply (meson Data_tail_ahead_of_t)
       apply force
      apply (drule meta_mp)
       apply (meson Data_tail_ahead_of_t LConsR)
      apply force
      done
    apply (metis (mono_tags, lifting) One_nat_def Suc_lessI diff_Suc_1 drop_eq_Nil2 le_eq_less_or_eq length_Cons length_drop list.size(3))
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_timestamp_not_produced_again_later:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some (Inl (op, x, xs, lxs')) \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   n' < n \<Longrightarrow>
   produce_inner (skip_n_productions_op (batch_op buf) n', lxs) = Some (Inl (lgc', x', xs', lxs'')) \<Longrightarrow>
   x' = Data wm' batch' \<Longrightarrow>
   t \<notin> fst ` set batch'"
  apply (metis produce_inner_skip_n_productions_op_batch_op_xs produce_inner_skip_n_productions_op_timestamp_not_produced_again_later_aux)
  done 

lemma produce_inner_batch_op_batch_le:
  "produce_inner (batch_op buf, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
  (t, b) \<in> set batch \<Longrightarrow>
   t \<le> wm"
  apply (induct "(batch_op buf, lxs)" r arbitrary: lxs lxs' op buf x xs rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: event.splits if_splits)
    done
  subgoal for h x xs lxs' lgc' buf
    apply (auto split: event.splits if_splits)
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_batch_op_coll_list_filter_Nil:
  "produce_inner (skip_n_productions_op (batch_op buf) n, LCons (Watermark wm) lxs) = Some (Inl (op, x, xs, lxs')) \<Longrightarrow>
   x = Data wm' batch \<Longrightarrow>
   xs = [Watermark wm'] \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   \<exists>x\<in>set buf. (case x of (t, d) \<Rightarrow> t \<le> wm) \<Longrightarrow>
   Suc (Suc 0) \<le> n \<Longrightarrow>
   coll_list (filter (\<lambda>(t, d). t \<le> wm) buf) t = []"
  using produce_inner_skip_n_productions_op_timestamp_not_produced_again_later[where n'=0 and n=n and lxs="LCons (Watermark wm) lxs" and t=t] apply -
  apply (drule meta_spec)+
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply force
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply simp
  apply (drule meta_mp)
   apply (subst (asm) produce_inner.simps)
   apply (subst produce_inner.simps)
   apply (auto split:)
  apply (drule meta_mp)
   apply (intro conjI)
    apply (rule refl)+
  unfolding coll_list_def
  apply auto
  apply (smt (verit, ccfv_threshold) filter_False imageI mem_Collect_eq)
  done 

subsection \<open>Soundness proofs\<close> 
lemma produce_inner_skip_n_productions_op_batch_op_Inl_soundness:
  "produce_inner (skip_n_productions_op (batch_op buf) n, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', Data wm batch, xs, lxs') \<Longrightarrow>
   Watermarked_Stream.monotone input_stream WM \<Longrightarrow>
   Watermark wm \<in> lset input_stream \<and>
   (\<forall>t\<in>set batch. fst t \<le> wm \<and> ((\<forall>t\<in>set buf. \<forall>wm\<in>WM. \<not> fst t \<le> wm) \<longrightarrow> (\<forall>wm\<in>WM. \<not> fst t \<le> wm))) \<and>
   batch \<noteq> [] \<and> (\<forall>x\<in>set batch. \<forall>x1 x2. x = (x1, x2) \<longrightarrow> Data x1 x2 \<in> lset input_stream \<or> (x1, x2) \<in> set buf)"
  apply (induction "(skip_n_productions_op (batch_op buf) n, input_stream)" r arbitrary: input_stream batch wm n buf rule: produce_inner_alt[consumes 1])
  subgoal for h lxs'a lgc'a n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis LConsData fst_conv)
      done
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis LConsData fst_conv)
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis fst_eqD)
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis fst_eqD)
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    done
  subgoal for h x xsa lxs lxs'a lgc'a n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    subgoal
      apply (subgoal_tac "n = 0 \<or> n = 1")
       defer
       apply (metis One_nat_def Suc_lessI bot_nat_0.not_eq_extremum drop0 drop_Suc list.sel(3) list.simps(3))
      apply (smt (verit, ccfv_threshold) One_nat_def case_prod_unfold diff_Suc_1 drop_Cons' event.distinct(1) event.inject(1) filter_empty_conv filter_set member_filter nth_via_drop)
      done
    apply (metis (mono_tags, opaque_lifting) drop_Cons' drop_Nil event.distinct(1) list.distinct(1) list.sel(1))
    done
  apply auto
  done


lemma produce_inner_skip_n_productions_op_batch_op_Inl_soundness_no_monotone:
  "produce_inner (skip_n_productions_op (batch_op buf) n, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', Data wm batch, xs, lxs') \<Longrightarrow>
   Watermark wm \<in> lset input_stream \<and>
   (\<forall>t\<in>set batch. fst t \<le> wm) \<and>
   batch \<noteq> [] \<and> (\<forall>x\<in>set batch. \<forall>x1 x2. x = (x1, x2) \<longrightarrow> Data x1 x2 \<in> lset input_stream \<or> (x1, x2) \<in> set buf) \<and>
   Watermark wm \<in> lset input_stream \<and>
   xs = [Watermark wm]"
  apply (induction "(skip_n_productions_op (batch_op buf) n, input_stream)" r arbitrary: input_stream batch wm n buf rule: produce_inner_alt[consumes 1])
  subgoal for h lxs'a lgc'a n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    done
  subgoal for h x xsa lxs lxs'a lgc'a n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    subgoal
      apply (subgoal_tac "n = 0 \<or> n = 1")
       defer
       apply (metis One_nat_def Suc_lessI bot_nat_0.not_eq_extremum drop0 drop_Suc list.sel(3) list.simps(3))
      apply auto
      apply (metis case_prodI filter_neq_nil_iff)
      done
    apply (metis (mono_tags, opaque_lifting) drop_Cons' drop_Nil event.distinct(1) list.distinct(1) list.sel(1))
    done
  apply auto
  done


lemma produce_inner_skip_n_productions_op_batch_op_Inl_soundness_no_monotone_2:
  "produce_inner (skip_n_productions_op (batch_op buf) n, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', Watermark wm, xs, lxs') \<Longrightarrow>
   Watermark wm \<in> lset input_stream \<and>
   xs = []"
  apply (induction "(skip_n_productions_op (batch_op buf) n, input_stream)" r arbitrary: input_stream batch wm n buf rule: produce_inner_alt[consumes 1])
  subgoal for h lxs'a lgc'a n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply auto
      done
    done
  subgoal for h x xsa lxs lxs'a lgc'a n buf batch 
    apply (simp split: llist.splits event.splits if_splits)
    subgoal
      apply (subgoal_tac "n = 0 \<or> n = 1")
       defer
      using neq_Nil_conv apply fastforce
      apply auto
      done
    subgoal
      apply auto
      subgoal
        apply (subst (asm) produce_inner.simps)
        apply auto
        apply (metis drop_Cons' drop_Nil event.inject(2) list.distinct(1) nth_Cons_0)
        done
      subgoal
        apply (subst (asm) produce_inner.simps)
        apply auto
        apply (metis drop_Nil list.sel(3) tl_drop)
        done
      done
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_batch_op_Inr_soundness_no_monotone:
  "produce_inner (skip_n_productions_op (batch_op buf) n, input_stream) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   exit op' = LCons (Data wm batch) output_stream \<Longrightarrow>
   (\<forall>t\<in>set batch. fst t \<le> wm) \<and>
   batch \<noteq> [] \<and> (\<forall>x\<in>set batch. \<forall>x1 x2. x = (x1, x2) \<longrightarrow> Data x1 x2 \<in> lset input_stream \<or> (x1, x2) \<in> set buf)"
  apply (induction "(skip_n_productions_op (batch_op buf) n, input_stream)" r arbitrary: input_stream batch wm n buf rule: produce_inner_alt[consumes 1])
  subgoal for h lxs'a lgc'a n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    done
  subgoal for h x xs lxs lxs' lgc' n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    done
  subgoal for n buf batch wm
    apply (auto split: llist.splits event.splits if_splits)
    subgoal 
      by (metis Domain.DomainI fst_eq_Domain in_lset_ldropD lset_intros(1) lset_llist_of sync_batches_le_wm)
    subgoal
      using sync_batches_no_empty_batch[where buf=buf and wm=wm and A="maximal_antichain_list (map fst buf)" and batch=batch] apply simp
      apply (drule meta_mp)
      using maximal_antichain_distinct apply blast
      apply (drule meta_mp)
       apply auto
      apply (drule meta_mp)
       apply auto
      apply (drule meta_mp)
       apply auto
      apply (metis in_lset_ldropD lset_intros(1) lset_llist_of)
      done
    subgoal
      apply (metis in_lset_ldropD llist.set_intros(1) lset_llist_of sync_batches_from_buf)
      done
    done
  done 

lemma produce_inner_skip_n_productions_op_batch_op_Inr_soundness:
  "produce_inner (skip_n_productions_op (batch_op buf) n, input_stream) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   Watermarked_Stream.monotone input_stream WM \<Longrightarrow>
   exit op' = LCons (Data wm batch) output_stream \<Longrightarrow>
   (\<forall>t\<in>set batch. fst t \<le> wm \<and> ((\<forall>t\<in>set buf. \<forall>wm\<in>WM. \<not> fst t \<le> wm) \<longrightarrow> (\<forall>wm\<in>WM. \<not> fst t \<le> wm))) \<and>
   batch \<noteq> [] \<and> (\<forall>x\<in>set batch. \<forall>x1 x2. x = (x1, x2) \<longrightarrow> Data x1 x2 \<in> lset input_stream \<or> (x1, x2) \<in> set buf)"
  apply (induction "(skip_n_productions_op (batch_op buf) n, input_stream)" r arbitrary: input_stream batch wm n buf rule: produce_inner_alt[consumes 1])
  subgoal for h lxs'a lgc'a n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis LConsData fst_conv)
      done
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis LConsData fst_conv)
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis fst_eqD)
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis fst_eqD)
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis fst_eqD)
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (metis fst_eqD)
      done
    done
  subgoal for h x xs lxs lxs' lgc' n buf batch wm
    apply (simp split: llist.splits event.splits if_splits)
    done
  subgoal for n buf batch wm
    apply (auto split: llist.splits event.splits if_splits)
    subgoal 
      by (metis Domain.DomainI fst_eq_Domain in_lset_ldropD lset_intros(1) lset_llist_of sync_batches_le_wm)
    subgoal
      by (metis fst_conv in_lset_ldropD lset_intros(1) lset_llist_of sync_batches_from_buf)
    subgoal
      using sync_batches_no_empty_batch[where buf=buf and wm=wm and A="maximal_antichain_list (map fst buf)" and batch=batch] apply simp
      apply (drule meta_mp)
      using maximal_antichain_distinct apply blast
      apply (drule meta_mp)
       apply auto
      apply (drule meta_mp)
       apply auto
      apply (drule meta_mp)
       apply auto
      apply (metis in_lset_ldropD lset_intros(1) lset_llist_of)
      done    subgoal
      apply (metis in_lset_ldropD llist.set_intros(1) lset_llist_of sync_batches_from_buf)
      done
    done
  done 

lemma produce_skip_n_productions_op_batch_op_batch_op_soundness_LCons:
  "produce (skip_n_productions_op (batch_op buf) n) input_stream = LCons x output_stream \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   (\<forall> t \<in> fst ` set batch . t \<le> wm \<and> ((\<forall> t \<in> fst ` set buf . (\<forall> wm \<in> WM . \<not> t \<le> wm)) \<longrightarrow> (\<forall> wm \<in> WM . \<not> t \<le> wm))) \<and>
   batch \<noteq> [] \<and>
   (\<forall> (t, d) \<in> set batch .  Data t d \<in> lset input_stream \<or> (t, d) \<in> set buf)"
  apply (subst (asm) produce.corec.code)
  apply (simp split: option.splits sum.splits prod.splits)
   apply hypsubst_thin
  subgoal for a b lgc' xa c xs lxs'
    using produce_inner_skip_n_productions_op_batch_op_Inl_soundness apply fast
    done
  subgoal for r op'
    apply hypsubst_thin
    using produce_inner_skip_n_productions_op_batch_op_Inr_soundness apply fast
    done
  done 


abbreviation "DT xs \<equiv> List.map_filter 
     (\<lambda> ev. case ev of Watermark _ \<Rightarrow> None | Data t d \<Rightarrow> Some t) xs"


definition "ws_dt'' xs t = {t'. \<not> t \<le> t' \<and> \<not> t' < t \<and> (\<exists> d. Data t' d \<in> lset (ltakeWhile (\<lambda> ev. case ev of Watermark _ \<Rightarrow> True | Data t'' _ \<Rightarrow> t \<noteq> t'') xs))}"

definition "antichain_from_stream lxs =
  (let xs = filter (\<lambda> ev. case ev of Data t d \<Rightarrow> \<not> (\<exists> wm. Watermark wm \<in> lset lxs \<and> t \<le> wm) | Watermark _ \<Rightarrow> False) (list_of lxs) in
   let tss = map tmp xs in
   maximal_antichain_list tss)"

lemma list_of_lfilter_lfinite:
  "lfinite lxs \<Longrightarrow>
   list_of (lfilter P lxs) = filter P (list_of lxs)"
  by (metis lfilter_llist_of list_of_llist_of llist_of_list_of)

(* FIXME: move me *)
lemma fun_to_case_event[simp]:
  "(\<lambda>x. (\<forall>x11. (\<exists>x12. x = Data x11 x12) \<longrightarrow> P x11 \<and> (\<forall>wm. Watermark wm \<in> lset lxs \<longrightarrow> \<not> x11 \<le> wm)) \<and> (\<forall>x2. x \<noteq> Watermark x2)) = 
   case_event (\<lambda>t' d. P t' \<and> (\<forall>wm. Watermark wm \<in> lset lxs \<longrightarrow> \<not> t' \<le> wm)) (\<lambda>x. False)"
  apply (rule ext)
  apply (auto split: event.splits)
  done

(* FIXME: move me *)
lemma filter_map_filter[simp]:
  "filter P (List.map_filter Q xs) = List.map_filter (\<lambda> x. case Q x of Some y \<Rightarrow> (if P y then Some y else None) | None \<Rightarrow> None) xs"
  apply (induct xs)
   apply (auto simp add: map_filter_simps split: option.splits)
  done

lemma antichain_from_stream_remove_1:
  "Watermark wm \<in> lset lxs \<and> t \<le> wm \<Longrightarrow> 
   lfinite lxs \<Longrightarrow>
   antichain_from_stream lxs = antichain_from_stream (lfilter (\<lambda> ev. case ev of Data t' _ \<Rightarrow> \<not> t' \<le> t | Watermark _ \<Rightarrow> True) lxs)"
  unfolding antichain_from_stream_def Let_def
  apply (auto simp add: list_of_lfilter_lfinite Let_def split: event.splits)
  apply (rule arg_cong[where f=maximal_antichain_list])
  apply (rule map_cong)
   apply simp_all
  apply (rule filter_cong)
   apply (auto split: event.splits) 
  done

lemma antichain_from_stream_Cons_Data:
  "lfinite lxs \<Longrightarrow>
   antichain_from_stream (LCons (Data t d) lxs) = (
   if \<not> (\<exists> wm. Watermark wm \<in> lset lxs \<and> t \<le> wm) \<and> \<not> (\<exists> t' d. Data t' d \<in> lset lxs \<and> t' > t) 
   then t # antichain_from_stream (lfilter (\<lambda> ev. case ev of Data t' _ \<Rightarrow> \<not> t' \<le> t | Watermark _ \<Rightarrow> True) lxs)
   else antichain_from_stream lxs)"
  apply (auto split: if_splits)
  subgoal
    unfolding antichain_from_stream_def Let_def
    apply (auto 0 0 simp add: list_of_lfilter_lfinite Let_def split: event.splits)
     apply (meson dual_order.strict_iff_not event.exhaust)
    apply (simp flip: maximal_antichain_filter)
    apply (rule arg_cong[where f="maximal_antichain_list"])
    apply (simp add: map_filter_map_filter flip: )
    unfolding  List.map_filter_def
    apply auto
    apply (rule map_cong)
     apply (rule filter_cong)
      apply simp
     apply (auto split: event.splits)
    done
  subgoal
    unfolding antichain_from_stream_def Let_def
    apply (auto simp add:  split: event.splits)
    done
  subgoal for t' d
    apply (cases "\<exists> wm. Watermark wm \<in> lset lxs \<and> t \<le> wm")
    subgoal
      apply (elim exE conjE)
      unfolding antichain_from_stream_def Let_def
      apply (auto simp add:  split: event.splits)
      done
    subgoal
      unfolding antichain_from_stream_def Let_def
      apply (subst (1 2) maximal_antichain_remove[where t=t' and t'=t])
      subgoal
        apply auto
        apply (smt (verit, best) dual_order.order_iff_strict dual_order.trans event.sel(1) event.simps(5) imageI mem_Collect_eq)
        done
      subgoal
        apply auto
        apply (smt (verit, best) dual_order.order_iff_strict dual_order.trans event.sel(1) event.simps(5) imageI mem_Collect_eq)
        done
      subgoal
        apply (auto simp add: list_of_lfilter_lfinite split: event.splits simp flip: maximal_antichain_filter)
        done
      done
    done
  done

definition "ws_2 lxs wm = {wm'. wm' \<in> set (takeWhile ((\<noteq>) wm) (antichain_from_stream lxs))}"

lemma ws_2_LCons_Data[simp]:
  "lfinite lxs \<Longrightarrow>
   ws_2 (LCons (Data t d) lxs) wm = (
   if (\<nexists>wm. Watermark wm \<in> lset lxs \<and> t \<le> wm) \<and> (\<nexists>t' d. Data t' d \<in> lset lxs \<and> t < t')
   then (if t = wm then {} else insert t (ws_2 (lfilter (\<lambda>x. case x of Data t' x \<Rightarrow> \<not> t' \<le> t | Watermark x \<Rightarrow> True) lxs) wm))
   else ws_2 lxs wm)"
  unfolding ws_2_def
  apply (auto simp add: antichain_from_stream_Cons_Data split: if_splits)
  done


lemma antichain_from_stream_llist_of_map[simp]:
  "antichain_from_stream (llist_of (map (\<lambda>(x, y). Data x y) buf)) = maximal_antichain_list (map fst buf)"
  unfolding antichain_from_stream_def Let_def
  apply (auto simp add: split_beta split: event.splits  prod.splits)
  apply (rule arg_cong[where f=maximal_antichain_list])
  apply (induct buf)
   apply simp
  subgoal for a buf'
    apply (cases a)
    apply auto
    done
  done

definition "bach_ts lxs t = (
  if Watermark t \<in> lset lxs 
  then {t' \<in> ts lxs t. \<not> (\<exists> wm \<in> ws lxs t . t' \<le> wm)}
  else {t' \<in> ts lxs t. \<not> (\<exists>wm' \<ge> t'. wm' \<in> ws_2 lxs t \<or> Watermark wm' \<in> lset lxs)})"

lemma bach_ts_lshift_1:
  "Watermark wm \<in> lset lxs \<Longrightarrow>
   wm \<noteq> wm' \<Longrightarrow>
   monotone (LCons (Watermark wm') lxs) WM \<Longrightarrow>
   bach_ts (map (\<lambda>(x, y). Data x y) buf @@- LCons (Watermark wm') lxs) wm =
   bach_ts (map (\<lambda>(x, y). Data x y) (filter (\<lambda>(t, _). \<not> t \<le> wm') buf) @@- lxs) wm"
  unfolding bach_ts_def
  apply (auto simp add: split_beta split: if_splits prod.splits)
  by (meson Data_set_strict_monotone_not_GE insertI1)


lemma bach_ts_lshift_2:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   bach_ts (map (\<lambda>(x, y). Data x y) buf @@- LCons (Watermark wm) lxs) wm =
   fst ` set (filter (\<lambda>(t, _). t \<le> wm) buf)"
  unfolding bach_ts_def
  apply (auto simp add: split_beta split: if_splits prod.splits)
  by (simp add: Data_set_strict_monotone_not_GE)


lemma bach_ts_lshift_3:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   bach_ts (map (\<lambda>(x, y). Data x y) (filter (\<lambda>(t, _). \<not> t \<le> wm) buf) @@- lxs) wm = {}"
  unfolding bach_ts_def
  apply (auto simp add: split_beta split: if_splits prod.splits)
   apply (meson Data_set_strict_monotone_not_GE insertI1)+
  done

lemma in_ws_dt'':
  "t \<in> ws_dt'' lxs wm \<Longrightarrow>
   t \<noteq> wm \<and> (\<exists> d. Data t d \<in> lset lxs)"
  unfolding ws_dt''_def
  apply (auto split: event.splits)
  using lset_ltakeWhileD apply fastforce+
  done

lemma antichain_from_stream_filter:
  "lfinite lxs \<Longrightarrow>
   antichain_from_stream lxs =
   antichain_from_stream (lfilter (\<lambda> ev. case ev of Data t d \<Rightarrow> \<not> (\<exists> wm. Watermark wm \<in> lset lxs \<and> t \<le> wm) | Watermark _ \<Rightarrow> False) lxs)"
  unfolding antichain_from_stream_def Let_def
  apply (auto 2 1 simp add: list_of_lshift antichain_from_stream_Cons_Data split_beta split: prod.splits event.splits)
  apply (smt (verit, best) dual_order.refl event.exhaust_sel event.sel(1) event.simps(4) event.split_sel le_boolD lfilter_cong list_of_lfilter_lfinite)
  done

lemma map_Data_filter:
  "map (\<lambda>(x, y). Data x y) (filter (\<lambda>(t, d). \<not> t \<le> wm) buf) =
  filter (\<lambda>ev. case ev of Data t _ \<Rightarrow> \<not> t \<le> wm) (map (\<lambda>(x, y). Data x y) buf)"
  apply (induct buf)
   apply auto
  done

lemma antichain_from_stream_shift_filter:
  "lfinite lxs \<Longrightarrow>
   monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   antichain_from_stream (map (\<lambda>(x, y). Data x y) buf @@- LCons (Watermark wm) lxs) =
   antichain_from_stream (map (\<lambda>(x, y). Data x y) (filter (\<lambda>(t, d). \<not> t \<le> wm) buf) @@- lxs)"
  apply (subst (1 2) antichain_from_stream_filter)
    apply force+
  apply (simp split: event.splits prod.splits)
  apply (rule arg_cong[where f=antichain_from_stream])
  apply (rule arg_cong2[where f=lshift])
  subgoal
    apply (simp add: map_Data_filter)
    apply (rule filter_cong)
     apply simp
    apply auto
    done
  apply (rule lfilter_cong)
   apply simp
  apply auto
  apply (meson Data_set_strict_monotone_not_GE insertI1)
  done


lemma bach_ts_lshift_4:
  "Watermark wm \<notin> lset lxs \<Longrightarrow>
   lfinite lxs \<Longrightarrow>
   wm \<noteq> wm' \<Longrightarrow>
   monotone (LCons (Watermark wm') lxs) WM \<Longrightarrow>
   bach_ts (map (\<lambda>(x, y). Data x y) buf @@- LCons (Watermark wm') lxs) wm =
   bach_ts (map (\<lambda>(x, y). Data x y) (filter (\<lambda> (t, d). \<not> t \<le> wm') buf) @@- lxs) wm"
  unfolding bach_ts_def
  apply (subgoal_tac " Watermark wm \<notin> lset (map (\<lambda>(x, y). Data x y) buf @@- LCons (Watermark wm') lxs)")
  subgoal
    apply (auto 5 1 simp add: split_beta split: prod.splits)
    subgoal for a b x'
      unfolding ws_2_def
      apply (auto 2 1)
      apply (simp add: antichain_from_stream_shift_filter)
      done
    subgoal for a b x'
      unfolding ws_2_def
      apply (auto 2 1)
      apply (simp add: antichain_from_stream_shift_filter)
      done
    subgoal for a b x'
      unfolding ws_2_def
      apply (auto 2 1)
      apply (simp add: antichain_from_stream_shift_filter)
      done
    subgoal for a b x'
      unfolding ws_2_def
      apply (auto 2 1)
      apply (simp add: antichain_from_stream_shift_filter)
      done
    subgoal for a b
      apply (meson Data_set_strict_monotone_not_GE insertI1)
      done
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_batch_op_batch_op_soundness_LCons_stronger_Inl:
  "produce_inner (skip_n_productions_op (batch_op buf) n, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', Data wm batch, xs, lxs') \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   (\<forall>t\<in>set batch. image_mset snd {#(t', d) \<in># mset batch. t' = fst t#} = coll WM input_stream (fst t) + image_mset snd {#(t', d) \<in># mset buf. t' = fst t#}) \<and>
   fst ` set batch = bach_ts ((map (\<lambda> (t,d). Data t d) buf) @@- input_stream) wm \<and>
   Watermark wm \<in> lset input_stream \<and>
   batch \<noteq> [] \<and>
   (\<forall>(t, d)\<in>set batch. t \<le> wm \<and> ((t, d) \<in> set buf \<or> Data t d \<in> lset input_stream)) \<and>
   \<not> (\<exists> t' d'. Data t' d' \<in> lset lxs' \<and> t' \<le> wm) \<and>
   (\<exists> buf' m. lgc' = skip_n_productions_op (batch_op buf') m \<and> m \<le> n \<and> \<not> (\<exists> t' d'. (t', d') \<in> set buf' \<and> t' \<le> wm)) \<and>
   xs = [Watermark wm] \<and>
   (\<forall> t' d. Data t' d \<in> lset lxs' \<longrightarrow> \<not> t' \<le> wm)"
  apply (induction "(skip_n_productions_op (batch_op buf) n, input_stream)" r arbitrary: n WM input_stream batch wm buf rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc'a zs n buf WM batch wm
    apply (simp add: split: llist.splits event.splits if_splits; hypsubst_thin)
    subgoal for t d
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (auto simp add: split_beta split: if_splits event.splits prod.splits)
      done
    subgoal for t d
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (auto simp add: split_beta split: if_splits event.splits prod.splits)
      done
    subgoal for wm'
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm' WM"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (auto 2 1 simp add: split_beta split: if_splits event.splits prod.splits)
         apply (metis (mono_tags, lifting) LConsR case_prod_unfold fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal 
        apply (subgoal_tac "wm \<noteq> wm'")
         defer
        subgoal
          by (metis (no_types, lifting) LConsR image_iff strict_monotone_LCons_Watermark_Data_not_ge)
        apply (subst bach_ts_lshift_1[where WM=WM])
           apply assumption+
         apply simp
        apply fast
        done
      subgoal 
        apply (cases "wm = wm'")
        subgoal
          by (simp add: bach_ts_lshift_3)
        subgoal
          apply (subst (asm) bach_ts_lshift_1[where WM=WM])
             apply assumption+
           apply simp
          apply fast
          done
        done
      apply (metis diff_le_self le_trans)
      done
    subgoal for wm'
      apply (drule meta_spec[of _ "n - Suc  0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm' WM"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (auto simp add: split_beta split: if_splits event.splits prod.splits)
      subgoal 
        apply (subgoal_tac "wm \<noteq> wm'")
         defer
        subgoal
          by (metis (no_types, lifting) LConsR image_iff strict_monotone_LCons_Watermark_Data_not_ge)
        apply (subst bach_ts_lshift_1[where WM=WM])
           apply assumption+
         apply simp
        apply (simp add: case_prod_unfold)
        done
       apply (cases "wm = wm'")
      subgoal
        by (metis filter_False filter_True monotone_LCons_Watermark strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        apply (subst (asm) bach_ts_lshift_1[where WM=WM])
           apply (simp_all  add: case_prod_unfold)
        done
      apply (metis diff_le_self le_trans)
      done
    subgoal for wm'
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm' WM"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (auto 2 1 simp add: split_beta split: if_splits event.splits prod.splits)
      subgoal
        by (metis (mono_tags, lifting) LConsR case_prod_unfold fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        by (smt (z3) Data_tail_ahead_of_t LConsR case_prod_beta filter_cong image_iff bach_ts_lshift_1)
      subgoal
        by (smt (z3) LConsR case_prod_unfold filter_False filter_True filter_cong strict_monotone_LCons_Watermark_Data_not_ge bach_ts_lshift_1)
      subgoal
        by (metis less_eq_nat.simps(1) skip_n_productions_op_0)
      done
    subgoal for wm'
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm' WM"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (auto simp add: split_beta split: if_splits event.splits prod.splits)
      subgoal
        by (smt (z3) LConsR case_prod_unfold filter_True image_iff strict_monotone_LCons_Watermark_Data_not_ge bach_ts_lshift_1)
      subgoal
        by (metis (no_types, lifting) LConsR case_prod_unfold empty_is_image filter_True set_empty bach_ts_lshift_1 bach_ts_lshift_3)
      subgoal
        by (metis le0 skip_n_productions_op_0)
      done
    done
  subgoal for h x xsa lxs lxs'a lgc'a n buf WM batch wm
    apply (subst (asm) produce_inner.simps)
    apply (simp split: if_splits event.splits)
    subgoal for wm
      apply (subgoal_tac "n= 0 \<or> n = 1")
       defer
      subgoal
        by (metis One_nat_def Suc_lessI bot_nat_0.not_eq_extremum drop_eq_Nil2 le_eq_less_or_eq length_Cons list.distinct(1) list.size(3))
      apply (elim disjE)
      subgoal
        apply (auto 0 0 split: prod.splits)
              apply (smt (verit, best) LConsR add_cancel_left_left case_prod_unfold coll_empty filter_mset_cong fst_conv prod.collapse strict_monotone_LCons_Watermark_Data_not_ge)
        subgoal
          by (metis (mono_tags, lifting) LConsR case_prodI filter_set fst_conv imageI member_filter bach_ts_lshift_2)
        subgoal
          using image_iff bach_ts_lshift_2 by fastforce
        subgoal
          by (metis case_prodI filter_neq_nil_iff)
        subgoal
          by (meson Data_tail_ahead_of_t LConsR)
        subgoal
          using case_prodD filter_set member_filter by auto 
        subgoal
          by (meson LConsR strict_monotone_LCons_Watermark_Data_not_ge) 
        done
      subgoal
        apply (auto split: prod.splits)
        done
      done
    subgoal for wm
      apply (subgoal_tac "n= 0")
       defer
      subgoal
        by (metis drop_eq_Nil2 le_eq_less_or_eq length_Cons less_Suc0 list.distinct(1) list.size(3) not_less_iff_gr_or_eq)
      apply hypsubst_thin
      apply (auto split: prod.splits)
      done
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_batch_op_batch_op_soundness_LCons_stronger_Inr:
  "produce_inner (skip_n_productions_op (batch_op buf) n, input_stream) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   lfinite input_stream \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   exit op = LCons (Data wm batch) output_stream \<Longrightarrow>
   (\<forall>t\<in>set batch. image_mset snd {#(t', d) \<in># mset batch. t' = fst t#} = coll WM input_stream (fst t) + image_mset snd {#(t', d) \<in># mset buf. t' = fst t#}) \<and>
   fst ` set batch = bach_ts ((map (\<lambda> (t,d). Data t d) buf) @@- input_stream) wm \<and>
   batch \<noteq> [] \<and>
   (\<exists> d. (Data wm d \<in> lset input_stream \<or> (wm, d) \<in> set buf) \<and> (wm, d) \<in> set batch) \<and>
    Watermark wm \<notin> lset input_stream \<and>
   \<not> (\<exists> t' d'. Data t' d' \<in> lset output_stream \<and> t' \<le> wm) \<and>
   (\<forall>(t, d)\<in>set batch. t \<le> wm \<and> ((t, d) \<in> set buf \<or> Data t d \<in> lset input_stream))"
  apply (induction "(skip_n_productions_op (batch_op buf) n, input_stream)" r arbitrary: n WM input_stream batch wm buf rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs n buf WM batch wm
    apply (simp add: split: llist.splits event.splits if_splits; hypsubst_thin)
    subgoal for t d
      apply (drule meta_spec[of _ n])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ WM])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply (rule refl)
      apply (auto simp add: split_beta split: if_splits event.splits prod.splits)
      done
    subgoal for t d
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ WM])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply (rule refl)
      apply (auto simp add: split_beta split: if_splits event.splits prod.splits)
      done
    subgoal for wm'
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm' WM"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply (rule refl)
      apply (auto 1 1 simp add: split_beta split: if_splits event.splits prod.splits)
      subgoal
        by (smt (z3) LConsR case_prod_unfold filter_mset_cong fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        apply (subst bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply simp
        done
      subgoal
        apply (subst (asm) bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply simp
        done
      subgoal
        by (metis (mono_tags, lifting) LConsR fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        by (metis (mono_tags, lifting) LConsR case_prod_unfold fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        apply (subst bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply simp
        done
      subgoal
        apply (subst (asm) bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply simp
        done
      done
    subgoal for wm'
      apply (drule meta_spec[of _ "n - Suc 0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm' WM"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply (rule refl)
      apply (auto 2 2 simp add: split_beta split: if_splits event.splits prod.splits)
      subgoal
        apply (subst bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        apply (subst (asm) bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        by (metis (mono_tags, lifting) LConsR fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        apply (subst bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        apply (subst (asm) bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      done
    subgoal for wm'
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm' WM"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply (rule refl)
      apply (auto 2 0 simp add: split_beta split: if_splits event.splits prod.splits)
      subgoal
        by (metis (mono_tags, lifting) LConsR case_prod_unfold fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        apply (subst  bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        apply (subst (asm) bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        by (metis (mono_tags, lifting) LConsR fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        by force 
      subgoal
        by (metis (mono_tags, lifting) LConsR case_prod_unfold fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        apply (subst bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        apply (subst (asm) bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        by force 
      done
    subgoal for wm'
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "insert wm' WM"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply (rule refl)
      apply (auto simp add: split_beta split: if_splits event.splits prod.splits)
      subgoal
        apply (subst  bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        apply (subst (asm) bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        by (metis (mono_tags, lifting) LConsR fst_conv strict_monotone_LCons_Watermark_Data_not_ge)
      subgoal
        apply (subst bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      subgoal
        apply (subst (asm) bach_ts_lshift_4[where WM=WM])
            apply assumption+
          apply (meson Data_tail_ahead_of_t LConsR)
         apply simp
        apply (simp add: case_prod_unfold)
        done
      done    done
     apply simp
    subgoal for n buf WM batch wm
      apply auto
      subgoal for t d
        apply (auto simp add: ldrop_llist_of llist_of_eq_LCons_conv)
        using t_in_concat_coll_list_eq[where batch=batch and t=t and buf=buf and wm=wm and A="maximal_antichain_list (map fst buf)"] apply simp
        apply (drule meta_mp)
         apply (metis in_set_dropD list.set_intros(1))
        apply (drule meta_mp)
         apply force
        apply (drule meta_mp)
         apply (metis fst_conv imageI in_set_dropD list.set_intros(1) sync_batches_le_wm)
        unfolding coll_list_def
        apply auto
        apply (metis (mono_tags, lifting) case_prod_unfold filter_mset_cong)
        done
      subgoal for t d
        unfolding bach_ts_def
        apply (auto simp add: split_beta split: if_splits prod.splits)
          apply (metis (no_types, lifting) fst_conv imageI in_lset_ldropD lset_intros(1) lset_llist_of sync_batches_from_buf)
         apply (metis (no_types, lifting) Domain.DomainI fst_eq_Domain in_lset_ldropD lset_intros(1) lset_llist_of sync_batches_le_wm)
        unfolding ws_2_def
        apply (auto simp add: ldrop_llist_of llist_of_eq_LCons_conv)
        apply (rule takeWhile_maximal_antichain_sync_batches[where buf=buf and batch=batch and A="maximal_antichain_list (map fst buf)"])
        using maximal_antichain_correct apply blast
           apply assumption+
        apply (metis (no_types, lifting) in_set_dropD list.set_intros(1))
        done
      subgoal for t'
        apply (auto simp add: ldrop_llist_of llist_of_eq_LCons_conv)
        unfolding bach_ts_def
        apply (auto simp add: split_beta split: if_splits prod.splits)
        unfolding ws_2_def
        apply (auto simp add: ldrop_llist_of llist_of_eq_LCons_conv)
        using sync_batches_batch_correct[where buf=buf and wm=wm and batch=batch and A="maximal_antichain_list (map fst buf)"] apply -
        apply (drule meta_mp)
        using maximal_antichain_correct apply blast
        apply (auto 2 0 simp add: split_beta split: prod.splits)
        apply (simp add: Domain.DomainI fst_eq_Domain)
        apply (smt (verit, ccfv_threshold) Domain.DomainI case_prod_conv filter_set in_set_dropD list.set_intros(1) maximal_antichain_distinct member_filter)
        done
      subgoal
        using sync_batches_no_empty_batch[where buf=buf and wm=wm and A="maximal_antichain_list (map fst buf)" and batch=batch] apply simp
        apply (drule meta_mp)
        using maximal_antichain_distinct apply blast
        apply (drule meta_mp)
         apply auto
        apply (drule meta_mp)
         apply auto
        apply (drule meta_mp)
         apply auto
        apply (metis in_lset_ldropD lset_intros(1) lset_llist_of)
        done
      subgoal
        apply (auto simp add: ldrop_llist_of llist_of_eq_LCons_conv)
        using sync_batches_batch_correct[where buf=buf and wm=wm and batch=batch and A="maximal_antichain_list (map fst buf)"] apply -
        apply (drule meta_mp)
        using maximal_antichain_correct apply blast
        apply (auto simp add: split_beta split: prod.splits)
        apply (smt (verit) antisym_conv2 case_prod_beta filter_set maximal_antichain_covers_all list.set_intros(1) map_eq_set_D maximal_antichain_distinct maximal_antichain_subset member_filter prod.collapse set_drop_subset set_takeWhileD subset_iff)
        done
      subgoal for wm' batch'
        apply (auto simp add: ldrop_llist_of llist_of_eq_LCons_conv)
        using drop_sync_batches_wm_not_again 
        using maximal_antichain_correct maximal_antichain_distinct apply blast
        done
      subgoal
        by (metis Domain.DomainI fst_eq_Domain in_lset_ldropD lset_intros(1) lset_llist_of sync_batches_le_wm)
      subgoal
        by (metis in_lset_ldropD lset_intros(1) lset_llist_of sync_batches_from_buf)
      done
    done

lemma produce_skip_n_productions_op_batch_op_batch_op_soundness_LCons_stronger:
  "produce (skip_n_productions_op (batch_op buf) n) input_stream = LCons x output_stream \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   (\<forall>t\<in>set (map fst batch). coll WM input_stream t + (mset (map snd (filter (\<lambda>(t', d). t' = t) buf))) = mset (map snd (filter (\<lambda>(t', d). t' = t) batch))) \<and>
   fst ` set batch = bach_ts ((map (\<lambda> (t,d). Data t d) buf) @@- input_stream) wm \<and>
   (\<forall> t \<in> set (map fst batch) . t \<le> wm) \<and>
   batch \<noteq> [] \<and>
   (\<forall>(t, d)\<in>set batch. t \<le> wm \<and> ((t, d) \<in> set buf \<or> Data t d \<in> lset input_stream))"
  apply (subst (asm) produce.corec.code)
  apply (simp split: prod.splits option.splits sum.splits)
  subgoal for a b lgc' d xa xs lxs'
    apply hypsubst_thin
    apply (frule produce_inner_skip_n_productions_op_batch_op_batch_op_soundness_LCons_stronger_Inl)
      apply (rule refl)
     apply assumption+
    apply auto
    done
  subgoal for t op
    apply hypsubst_thin
    apply (frule produce_inner_skip_n_productions_op_batch_op_batch_op_soundness_LCons_stronger_Inr)
        apply auto
    using produce_inner_Some_Inr_lfinite apply blast
    done
  done

lemma produce_skip_n_productions_op_batch_op_soundness:
  "x \<in> lset (produce (skip_n_productions_op (batch_op buf) n) lxs) \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> 
   fst ` set batch = bach_ts ((map (\<lambda> (t,d). Data t d) buf) @@- lxs) wm \<and>
   (\<forall> t \<in> set (map fst batch) . coll WM lxs t + (mset (map snd (filter (\<lambda>(t', d). t' = t) buf))) = mset (map snd (filter (\<lambda> (t', d) . t' = t) batch))) \<and>
   (\<forall>t\<in>set (map fst batch). t \<le> wm) \<and>
   batch \<noteq> [] \<and>
   (\<forall>(t, d)\<in>set batch. t \<le> wm \<and> ((t, d) \<in> set buf \<or> Data t d \<in> lset lxs))"
  apply (induct "produce (skip_n_productions_op (batch_op buf) n) lxs" arbitrary: wm batch n rule: llist.set_induct)
  subgoal for z1 z2 n wm batch
    using produce_skip_n_productions_op_batch_op_batch_op_soundness_LCons_stronger[where buf=buf and x=z1 and input_stream=lxs and batch=batch and wm=wm and output_stream=z2 and n=n and WM=WM] apply auto
     apply fastforce+
    done
  subgoal for z1 z2 xa n wm batch
    apply (drule HOL.sym[where s="LCons z1 z2"])
    apply (cases z1)
    subgoal premises p for x11 x12
      apply (rule p(2)[where n="Suc n"])
        apply (subst produce_skip_n_productions_op_LCons[symmetric])
      using p apply -
         apply assumption
      using p apply simp_all
      done
    subgoal premises p for x2
      apply (rule p(2)[where n="Suc n"])
      apply (subst produce_skip_n_productions_op_LCons[symmetric])
      using p apply -
      apply assumption
      using p apply simp_all
      done
    done
  done

lemma produce_batch_op_soundness:
  "Data wm batch \<in> lset (produce (batch_op buf) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> 
   fst ` set batch = bach_ts ((map (\<lambda> (t,d). Data t d) buf) @@- lxs) wm \<and>
   (\<forall> t \<in> set (map fst batch) . coll WM lxs t + (mset (map snd (filter (\<lambda>(t', d). t' = t) buf))) = mset (map snd (filter (\<lambda> (t', d) . t' = t) batch))) \<and>
   (\<forall>t\<in>set (map fst batch). t \<le> wm) \<and>
   batch \<noteq> [] \<and>
   (\<forall>(t, d)\<in>set batch. t \<le> wm \<and> ((t, d) \<in> set buf \<or> Data t d \<in> lset lxs))"
  using produce_skip_n_productions_op_batch_op_soundness[where n=0 and x="Data wm batch"]
  apply (metis (no_types, lifting) skip_n_productions_op_0)
  done

lemma produce_lnth_ldropn:
  "(enat n) < llength (produce op lxs) \<Longrightarrow>
   lnth (produce op lxs) n = x \<longleftrightarrow> (\<exists> lxs'. ldropn n (produce op lxs) = LCons x lxs')"
  by (metis ldropn_Suc_conv_ldropn lhd_LCons)

lemma produce_inner_skip_n_productions_op_Inl_not_ge_WM:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (op, Data t batch, xs, lxs') \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   (\<forall> (t, d) \<in> set buf. \<forall> wm \<in> WM. \<not> t \<le> wm) \<Longrightarrow>
  (t, ba) \<in> set batch \<Longrightarrow> wm \<in> WM \<Longrightarrow> t \<le> wm \<Longrightarrow> False"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: n buf lxs lxs' xs t batch wm op rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs n buf lxs'a xs t batch wm op
    apply (auto split: if_splits event.splits)
    apply (smt (verit, best) LConsData case_prodI2 fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis (no_types, lifting) filter_is_subset in_mono strict_monotone_remove_wm)
    apply blast
    apply (smt (verit, ccfv_threshold) LConsData case_prodI rotate1.simps(2) set_ConsD set_rotate1 skip_n_productions_op_0)
    apply (metis (no_types, lifting) mem_Collect_eq set_filter skip_n_productions_op_0 strict_monotone_remove_wm)
    apply (metis (no_types, lifting) skip_n_productions_op_0 strict_monotone_remove_wm)
    done
  apply (auto split: if_splits event.splits)
  subgoal for xs lxs lxs' n buf t batch wm x2 a b
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits)
    apply (subgoal_tac "n = 0 \<or> n = 1")
    defer
    apply (metis (no_types, lifting) One_nat_def Suc_lessI bot_nat_0.not_eq_extremum drop_eq_Nil2 le_eq_less_or_eq length_Cons list.distinct(1) list.size(3))
    apply auto
    apply hypsubst_thin
    apply blast
    done
  subgoal for xs lxs lxs' n buf t batch wm x2
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits)
    apply (subgoal_tac "n = 0 \<or> n = 1")
    defer
    apply linarith
    apply auto
    done
  done

lemma produce_skip_n_productions_op_not_get_WM:
  "produce (skip_n_productions_op (batch_op buf) n) lxs = LCons (Data t batch) lxs' \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   (\<forall>t\<in>fst ` set buf. \<forall>wm\<in>WM. \<not> t \<le> wm) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   (\<forall> (t, d) \<in> set buf. \<forall> wm \<in> WM. \<not> t \<le> wm) \<Longrightarrow>
   \<forall> wm \<in> WM . \<not> t \<le> wm"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits sum.splits)
  subgoal for op xs lxs' ba wm
    using produce_inner_skip_n_productions_op_Inl_not_ge_WM apply fast
    done
  subgoal for op' b wm
    using Data_set_strict_monotone_not_GE produce_inner_skip_n_productions_op_batch_op_Inr_in_batch_from_buf_or_lxs apply fastforce
    done
  done

lemma lnth_Data_produce_inner_Some_skip_n_productions_op_batch_op_LCons_batch_not_ge:
  "produce_inner (skip_n_productions_op (batch_op buf) i, lxs) = Some r \<Longrightarrow>
   r = Inl (op', Watermark wm, xs, lxs') \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   (\<forall>t\<in>fst ` set buf. \<forall>wm\<in>WM. \<not> t \<le> wm) \<Longrightarrow>
   lnth (xs @@- produce op' lxs') n = Data t batch \<Longrightarrow>
   enat (Suc n) \<le> llength (xs @@- produce op' lxs') \<Longrightarrow>
   (t', bc) \<in> set batch \<Longrightarrow> \<not> t' \<le> wm"
  apply (induct "(skip_n_productions_op (batch_op buf) i, lxs)" r arbitrary: n buf lxs lxs' xs t batch wm op' i rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' lxs' zs ys buf n lxs'a xs t batch wm
    apply hypsubst_thin
    apply (auto 2 0 split: if_splits event.splits)
    apply (metis LConsData fst_conv insertE list.simps(15) rotate1.simps(2) set_rotate1)
    subgoal
      by (metis (no_types, lifting) mem_Collect_eq set_filter strict_monotone_remove_wm)
    subgoal
      using strict_monotone_remove_wm by blast
    subgoal
      by (metis LConsData fst_conv insertE list.simps(15) rotate1.simps(2) set_rotate1 skip_n_productions_op_0)
    subgoal
      by (metis (no_types, lifting) filter_is_subset in_mono skip_n_productions_op_0 strict_monotone_remove_wm)
    subgoal
      by (metis skip_n_productions_op_0 strict_monotone_remove_wm)
    done
  subgoal for h x xs lxs lxs' lgc' buf i n lxs'a xsa t batch wm op
    apply (simp add: split_beta split: if_splits prod.splits list.splits event.splits)
    subgoal for wm'
      apply (subst (asm) produce_inner.simps)
      apply (auto split: if_splits)
      apply hypsubst_thin
      subgoal for a b t' d
        apply (subgoal_tac "i = 1 \<or> i = 0")
        defer
        apply (metis One_nat_def Suc_lessI bot_nat_0.not_eq_extremum drop0 drop_Suc_Cons list.discI)
        apply (elim disjE)    
        subgoal 
          apply hypsubst_thin
          apply auto
          apply (subst (asm) produce_lnth_ldropn)  
          using Suc_ile_eq apply blast
          apply auto
          apply (simp flip: produce_skip_n_productions_op_correctness)
          apply hypsubst_thin
          apply (frule produce_skip_n_productions_op_not_get_WM[where WM=WM])
          using strict_monotone_remove_wm apply blast
          apply auto
          apply (smt (verit, best) Domain.DomainI LConsR case_prod_unfold filter_set fst_eq_Domain image_iff lset_intros(1) member_filter produce_no_timestamps_out_of_the_blue strict_monotone_LCons_Watermark_Data_not_ge)+
          done
        apply (metis drop0 event.simps(4) list.sel(1))
        done
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (subst (asm) produce_inner.simps)
      apply (auto split: if_splits)
      apply hypsubst_thin
      apply (subgoal_tac "i = 1 \<or> i = 0")
      defer
      apply (metis One_nat_def Suc_lessI bot_nat_0.not_eq_extremum)
      apply auto
      apply hypsubst_thin
      apply (subst (asm) produce_lnth_ldropn)  
      using Suc_ile_eq apply blast
      apply auto
      apply (simp flip: produce_skip_n_productions_op_correctness)
      apply (frule produce_skip_n_productions_op_not_get_WM[where WM=WM])
      using strict_monotone_remove_wm apply blast
      apply auto
      apply (smt (verit, best) Domain.DomainI LConsR case_prod_unfold filter_set fst_eq_Domain image_iff lset_intros(1) member_filter produce_no_timestamps_out_of_the_blue strict_monotone_LCons_Watermark_Data_not_ge)+
      done
    done
  apply auto
  done

(* FIXME: move me *)
lemma map_remdups_inj:
  "inj f \<Longrightarrow>
   (drop i (map f (remdups ys))) =
   x # xs \<Longrightarrow>
   x \<in> set xs \<Longrightarrow> False"
  apply (induct ys arbitrary: x i xs)
  apply (auto split: if_splits)
  apply (metis drop_Cons' image_set inj_image_mem_iff insert_absorb list.sel(3) list.set_intros(1) list.simps(15) set_remdups)
  done


lemma lnth_Data_produce_inner_Some_skip_n_productions_op_batch_op_Inr_LCons_batch_not_ge:
  "produce_inner (skip_n_productions_op (batch_op buf) i, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   Watermark wm \<in> lset (exit op') \<Longrightarrow> False"
  apply (induct "(skip_n_productions_op (batch_op buf) i, lxs)" r arbitrary: buf lxs wm op' i rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs buf i wm op'
    apply hypsubst_thin
    apply (auto split: if_splits event.splits)
    apply (metis skip_n_productions_op_0)+
    done
  apply (auto split: if_splits event.splits)
  using in_lset_ldropD apply force
  done

lemma lnth_Data_produce_skip_n_productions_op_batch_op_batch_op_soundness_LCons_batch_not_ge:
  "monotone lxs WM \<Longrightarrow>
   (\<forall>t\<in>fst ` set buf. \<forall>wm\<in>WM. \<not> t \<le> wm) \<Longrightarrow>
   lnth hs n = Data t batch \<Longrightarrow>
   enat (Suc n) \<le> llength hs \<Longrightarrow>
   produce (skip_n_productions_op (batch_op buf) i) lxs = LCons (Watermark wm) hs \<Longrightarrow> \<forall>t\<in>set batch. \<not> fst t \<le> wm"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits split: prod.splits sum.splits)
  subgoal for op' xs lxs' t'' bc
    apply hypsubst_thin
    apply (drule lnth_Data_produce_inner_Some_skip_n_productions_op_batch_op_LCons_batch_not_ge[where t=t and batch=batch and n=n]) 
    apply simp
    apply assumption+
    apply blast
    apply force
    apply auto
    done
  subgoal for op' t' d
    using lnth_Data_produce_inner_Some_skip_n_productions_op_batch_op_Inr_LCons_batch_not_ge apply fastforce
    done
  done

lemma lnth_produce_skip_n_productions_op_batch_op_batch_not_ge:
  "x = Data t batch \<Longrightarrow> 
   monotone lxs WM \<Longrightarrow>
   (\<forall>t\<in>fst ` set buf. \<forall>wm\<in>WM. \<not> t \<le> wm) \<Longrightarrow>
   lnth (produce (skip_n_productions_op (batch_op buf) i) lxs) n = x\<Longrightarrow>
   m < n \<Longrightarrow>
   lnth (produce (skip_n_productions_op (batch_op buf) i) lxs) m = Watermark wm  \<Longrightarrow>
   n < llength (produce (skip_n_productions_op (batch_op buf) i) lxs) \<Longrightarrow>
   (\<forall> t \<in> fst ` set batch .\<not> t \<le> wm)"
  apply (induct n arbitrary: i buf lxs WM t batch m )
  apply fast
  apply simp
  subgoal for n i buf lxs WM t batch m 
    apply (cases "produce (skip_n_productions_op (batch_op buf) i) lxs")
    apply simp
    subgoal for h hs
      apply simp
      apply (cases m)
      apply simp
      subgoal 
        apply hypsubst_thin
        using lnth_Data_produce_skip_n_productions_op_batch_op_batch_op_soundness_LCons_batch_not_ge 
        apply fast
        done
      apply simp
      apply (drule meta_spec[of _ "Suc i"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply assumption
      apply (drule meta_mp)
      apply fast
      apply (drule meta_mp)
      subgoal for n'
        apply hypsubst_thin
        apply (subst (asm) produce_skip_n_productions_op_correctness)
        apply (subst produce_skip_n_productions_op_correctness)
        apply (subst lnth_ldropn)
        apply (smt (verit) Suc_ile_eq add.commute ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn llist.inject)
        apply (metis (mono_tags, lifting) Suc_ile_eq ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn llist.inject)
        done
      apply (drule meta_mp)
      apply assumption
      apply (drule meta_mp)
      subgoal for n'
        apply hypsubst_thin
        apply (subst (asm) produce_skip_n_productions_op_correctness)
        apply (subst produce_skip_n_productions_op_correctness)
        apply (subst lnth_ldropn)
        apply (smt (verit, ccfv_threshold) Suc_ile_eq add.commute enat_ord_simps(2) ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn order_less_subst2 produce_skip_n_productions_op_correctness produce_skip_n_productions_op_LCons)
        apply (smt (verit, ccfv_SIG) Suc_ile_eq enat_ord_simps(2) ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn llist.inject order_less_subst2)
        done
      apply (erule meta_mp)
      using Suc_ile_eq
      by (metis produce_skip_n_productions_op_LCons)
    done
  done 

lemma produce_skip_n_productions_op_Suc_Suc_EX:
  "produce (skip_n_productions_op (batch_op (filter (\<lambda>(t, _). \<not> t \<le> wm) buf)) n) lxs' = LCons (Data wm' batch') lxs'' \<Longrightarrow>
   \<exists> (t, d) \<in> set buf . t \<le> wm \<Longrightarrow>
   \<exists>lxs''. produce (skip_n_productions_op (batch_op buf) (Suc (Suc n))) (LCons (Watermark wm) lxs') = LCons (Data wm' batch') lxs''"
  apply (subst produce_skip_n_productions_op_correctness)
  apply (subst (asm) produce_skip_n_productions_op_correctness)
  apply (subst in_buf_produce_Watermark)
  apply simp
  apply simp
  done

(*FIXME: is this completeness? *)
lemma produce_inner_skip_n_productions_op_batch_op_smaller:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   t \<in> ts lxs wm \<or> t \<in> fst ` set buf \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists>n'\<le>n. \<exists>wm' batch'. 
    (\<exists>lxs'. produce (skip_n_productions_op (batch_op buf) n') lxs = LCons (Data wm' batch') lxs') \<and> t \<in> fst ` set batch'"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: lxs lxs' op buf x xs n  rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs buf n lxs'a op x xs 
    apply (auto 2 0 simp add: in_buf_produce_Watermark simp del: produce_LCons produce_lshift split: event.splits if_splits)
    subgoal
      by (metis (mono_tags, lifting) fst_conv imageI list.set_intros(1) produce_Data produce_skip_n_productions_op_correctness rotate1.simps(2) set_rotate1 strict_monotone_drop_head)
    subgoal
      by (metis produce_Data produce_skip_n_productions_op_correctness strict_monotone_drop_head)
    subgoal
      by (smt (verit, ccfv_threshold) Domain.DomainI Un_iff fst_eq_Domain produce_Data produce_skip_n_productions_op_correctness set_append strict_monotone_drop_head)
    subgoal
      by (metis Domain.DomainI Orderings.order_eq_iff bot_nat_0.extremum fst_eq_Domain list.set_intros(1) produce_Data rotate1.simps(2) set_rotate1 skip_n_productions_op_0 strict_monotone_drop_head)
    subgoal
      by (metis bot_nat_0.extremum_uniqueI produce_Data skip_n_productions_op_0 strict_monotone_drop_head)
    subgoal
      by (metis Domain.DomainI Un_iff bot_nat_0.extremum_uniqueI fst_eq_Domain produce_Data set_append skip_n_productions_op_0 strict_monotone_drop_head)
    subgoal for t d
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply blast
      apply (drule meta_mp)
      apply blast
      apply (auto simp add: produce_skip_n_productions_op_correctness)
      subgoal for n'
        apply (rule exI[of _ "Suc (Suc n')"])
        apply auto
        apply (metis fst_conv image_iff)+
        done
      done
    subgoal for wm' t' d'
      apply hypsubst_thin
      apply (cases "wm \<le> wm'")
      subgoal
        apply (rule exI[of _ 0])
        apply auto
        apply (metis (no_types, lifting) case_prod_unfold fst_conv image_iff mem_Collect_eq order_trans)
        done
      subgoal
        apply (cases "t \<le> t'")
        subgoal
          apply (rule exI[of _ 0])
          apply auto
          apply (metis (no_types, lifting) case_prod_unfold fst_conv image_iff mem_Collect_eq order_trans)
          done
        subgoal
          apply (cases "t \<le> wm'")
          subgoal
            apply (rule exI[of _ 0])
            apply auto
            apply (simp add: Domain.DomainI fst_eq_Domain)
            done
          subgoal
            apply (drule meta_spec)+
            apply (drule meta_mp)
            apply (rule refl)
            apply (drule meta_mp)
            apply (rule refl)
            apply (drule meta_mp)
            apply (rule refl)
            apply (drule meta_mp)
            apply (rule refl)
            apply (drule meta_mp)
            subgoal
              apply (rule disjI2)
              apply auto
              apply force
              done
            apply (drule meta_mp)
            using strict_monotone_drop_head apply blast
            apply (elim conjE exE)
            subgoal for n' wm'' batch' lxs'
              apply (rule exI[of _ "Suc (Suc n')"])
              apply auto
              apply (metis fst_conv image_iff)
              done
            done
          done
        done
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply blast
      apply (drule meta_mp)
      apply blast
      apply (auto simp add: not_in_buf_produce_Watermark produce_Data produce_skip_n_productions_op_correctness split: prod.splits)
      subgoal for n'
        apply (rule exI[of _ "Suc n'"])
        apply (auto simp add: not_in_buf_produce_Watermark produce_Data produce_skip_n_productions_op_correctness split: prod.splits)
        apply (metis Domain.DomainI fst_eq_Domain)+
        done
      done
    subgoal for wm d
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply force
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (auto simp add: not_in_buf_produce_Watermark produce_Data produce_skip_n_productions_op_correctness)
      subgoal for n'
        apply (rule exI[of _ "Suc n'"])
        apply (auto simp add: not_in_buf_produce_Watermark produce_Data produce_skip_n_productions_op_correctness split: prod.splits)
        apply (metis Domain.DomainI fst_eq_Domain)+
        done
      done
    subgoal for wm t d
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (auto simp add:  produce_Data produce_skip_n_productions_op_correctness)
      apply (metis drop0 drop_Suc_Cons less_not_refl lshift_simps(1) strict_monotone_remove_wm)
      done
    subgoal for wm' t' d d'
      apply hypsubst_thin
      apply (cases "wm \<le> wm'")
      subgoal
        apply (rule exI[of _ 0])
        apply simp
        apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq order_trans)
        done
      subgoal
        apply (cases "t \<le> t'")
        subgoal
          apply (rule exI[of _ 0])
          apply simp
          apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq order_trans)
          done
        subgoal
          apply (cases "t \<le> wm'")
          subgoal
            apply (rule exI[of _ 0])
            apply simp
            apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq)
            done  
          subgoal
            apply (drule meta_spec)
            apply (drule meta_spec[of _ 0])
            apply (drule meta_spec)+
            apply (drule meta_mp)
            apply simp
            apply (drule meta_mp)
            apply (rule refl)
            apply (drule meta_mp)
            apply (rule refl)
            apply (drule meta_mp)
            apply (rule refl)
            apply (drule meta_mp)
            subgoal
              apply (rule disjI2)
              apply auto
              apply force
              done
            apply (drule meta_mp)
            using strict_monotone_drop_head apply blast
            apply (elim conjE exE)
            subgoal for n' wm'' batch' lxs'
              apply (rule exI[of _ "Suc (Suc n')"])
              apply auto
              done
            done
          done
        done
      done
    subgoal
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply force
      apply (drule meta_mp)
      apply force
      apply (auto simp add: not_in_buf_produce_Watermark produce_Data produce_skip_n_productions_op_correctness)
      apply (metis Domain.DomainI drop_Suc_Cons drop_eq_Nil2 fst_eq_Domain less_Suc0 less_Suc_eq_le less_not_refl list.size(3) lshift_simps(1))
      done
    subgoal
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply force
      apply (drule meta_mp)
      apply force
      apply (auto simp add: not_in_buf_produce_Watermark produce_Data produce_skip_n_productions_op_correctness)
      apply (metis Domain.DomainI drop0 drop_Suc_Cons fst_eq_Domain less_not_refl lshift_simps(1))
      done
    done
  subgoal for h x xs lxs lxs' lgc' buf n lxs'a op xa xsa
    apply (auto 2 0 simp add: in_buf_produce_Watermark simp del: produce_LCons produce_lshift split: event.splits if_splits)
    apply (subgoal_tac "n = 0")
    prefer 2
    subgoal 
      apply (metis drop_Cons' drop_Nil list.discI)
      done
    subgoal for x2 a b
      apply auto
      apply hypsubst_thin
      apply (meson Data_set_strict_monotone_not_GE insertI1)
      done
    subgoal for x2 a b ba
      apply (subgoal_tac "n = 0")
      prefer 2
      subgoal 
        apply (metis drop_Cons' drop_Nil list.discI)
        done
      apply auto
      apply hypsubst_thin
      apply (auto split: prod.splits)
      using image_iff apply fastforce
      done
    apply (metis drop_Cons' drop_Nil list.sel(3) neq_Nil_conv)
    apply (metis drop_Nil list.sel(3) not_Cons_self tl_drop)
    done
  apply auto
  done 

(*FIXME: this is completeness *)
lemma produce_inner_skip_n_productions_op_batch_op_smaller_Inr:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   (\<exists> d . Data t d \<in> lset lxs) \<or> t \<in> fst ` set buf \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
    exit op = LCons (Data wm batch) lxs' \<Longrightarrow>
   \<exists>n'\<le>n. \<exists>wm' batch'. (\<exists>lxs'. produce (skip_n_productions_op (batch_op buf) n') lxs = LCons (Data wm' batch') lxs') \<and> t \<in> fst ` set batch'"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: n buf lxs op rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs n buf op
    apply (auto 2 0 simp add: in_buf_produce_Watermark simp del: produce_LCons produce_lshift split: event.splits if_splits)
    subgoal
      by (smt (verit, best) fst_conv image_iff in_set_conv_decomp produce_Data produce_skip_n_productions_op_correctness strict_monotone_remove_wm)
    subgoal
      by (metis produce_Data produce_skip_n_productions_op_correctness)
    subgoal
      by (smt (verit, ccfv_threshold) Un_iff fst_conv image_iff produce_Data produce_skip_n_productions_op_correctness set_append strict_monotone_remove_wm)
    subgoal
      by (metis fst_conv imageI in_set_conv_decomp le_zero_eq produce_Data skip_n_productions_op_0)
    subgoal
      by (metis bot_nat_0.extremum_uniqueI produce_Data skip_n_productions_op_0)
    subgoal
      by (metis (no_types, lifting) bot_nat_0.extremum_uniqueI fst_conv imageI list.set_intros(2) produce_Data rotate1.simps(2) set_rotate1 skip_n_productions_op_0)
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec)+
      apply (simp del: produce_LCons produce_lshift)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply blast
      apply (auto simp add:  simp del: produce_LCons produce_lshift)
      subgoal for n' wm' batch' d lxs''
        apply (rule exI[of _ "n' + 2"])
        apply (auto simp add:  simp del: produce_LCons produce_lshift)
        apply (rule exI[of _ wm'])
        apply (rule exI[of _ batch'])
        apply (auto simp add:  simp del: produce_LCons produce_lshift)
        apply (rule exI[of _ lxs''])
        subgoal
          apply (subst (asm) produce.code)
          apply (subst produce.code)
          apply (auto split: option.splits sum.splits; (subst produce_inner.simps)?; auto?)
          apply ((subst (asm) (2) produce_inner.simps)?; (auto split: if_splits)?)+
          done
        apply (metis fst_conv image_iff)
        done
      done
    subgoal for wm
      apply hypsubst_thin
      apply (cases "t \<le> wm")
      subgoal
        apply (rule exI[of _ 0])
        apply (auto simp add:  simp del: produce_LCons produce_lshift)
        apply (subst produce.code)
        apply (subst produce_inner.simps)
        apply auto
        apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq)
        done
      subgoal
        apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
        apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        using image_iff apply fastforce
        apply (auto 2 1 simp add:  simp del: produce_LCons produce_lshift)
        subgoal for n' wm' batch' d lxs''
          apply (rule exI[of _ "n' + 2"])
          apply auto
          apply (metis fst_conv image_iff)
          apply (metis Domain.DomainI fst_eq_Domain)
          done
        done
      done
    subgoal for wm t'
      apply hypsubst_thin
      apply (drule meta_spec[of _ "n - (Suc 0)"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply blast
      apply auto
      subgoal for n' wm' batch' d lxs''
        apply (rule exI[of _ "n' + 1"])
        apply (auto simp add: Domain.DomainI fst_eq_Domain)
        done
      done
    subgoal for wm t'
      apply hypsubst_thin
      apply (drule meta_spec[of _ "n - (Suc 0)"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (simp add: rev_image_eqI)
      apply (auto simp add: Domain.DomainI fst_eq_Domain)
      subgoal for n' wm' batch' d lxs''
        apply (rule exI[of _ "n' + 1"])
        apply (auto simp add: Domain.DomainI fst_eq_Domain)
        done
      done
    subgoal for wm t'
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec)+
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply blast
      apply (auto simp add: Domain.DomainI fst_eq_Domain)
      done
    subgoal for wm' t'
      apply hypsubst_thin
      apply (cases "t \<le> wm'")
      subgoal
        apply (rule exI[of _ 0])
        apply (auto simp add: Domain.DomainI fst_eq_Domain)
        done
      subgoal
        apply (drule meta_spec[of _ "0"])
        apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm') buf"])
        apply (drule meta_spec)+
        apply simp
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply force
        apply auto
        subgoal for wm' batch' d lxs''
          apply (rule exI[of _ "2"])
          apply (auto simp add: Domain.DomainI fst_eq_Domain)
          done
        done
      done
    subgoal for wm' d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply force
      apply auto
      apply (rule exI[of _ 1])
      apply (auto simp add: Domain.DomainI fst_eq_Domain)
      done
    subgoal for wm' d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply force
      apply auto
      apply (rule exI[of _ 1])
      apply (auto simp add: Domain.DomainI fst_eq_Domain)
      done
    done
  apply auto[1]
  subgoal for n buf b
    apply auto
    apply hypsubst_thin
    apply (subgoal_tac "\<exists> wm \<in> set (maximal_antichain_list (map fst buf)). t \<le> wm")
    defer
    apply (metis Domain.DomainI Domain_fst maximal_antichain_covers_all)
    apply auto
    subgoal for b wm'
      using sync_batches_before_n[where A="maximal_antichain_list (map fst buf)" and wm=wm and batch=batch and buf=buf and n=n and t=t and wm'=wm'] apply simp
      apply (drule meta_mp)
      apply (metis ldrop_llist_of llist_of_eq_LCons_conv nth_via_drop)
      apply (drule meta_mp)
      apply (metis drop_all ldrop_llist_of leI le_numeral_extra(3) list.size(3) llength_LCons llength_llist_of not_eSuc_ilei0 zero_enat_def)
      apply (drule meta_mp)
      apply force
      apply (drule meta_mp)
      apply (simp add: Domain.DomainI fst_eq_Domain)
      apply auto
      subgoal for n' wm'' batch''
        apply (rule exI[of _ n'])
        apply auto
        apply (rule exI[of _ wm''])
        apply (rule exI[of _ batch''])
        apply (auto simp add: ldrop_llist_of llist_of_eq_LCons_conv)
        apply (metis Cons_nth_drop_Suc drop_all dual_order.strict_trans2 list.discI not_le_imp_less)
        apply force
        done
      done
    done
  done

(*FIXME: this is completeness *)
lemma produce_skip_n_productions_op_batch_op_LE_EX:
  "produce (skip_n_productions_op (batch_op buf) n) lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   t \<in> ts lxs wm \<or> t \<in> fst ` set buf \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> n' \<le> n. \<exists>wm' batch' lxs'. produce (skip_n_productions_op (batch_op buf) n') lxs = LCons (Data wm' batch') lxs' \<and> t \<in> fst ` set batch'"
  apply (subst (asm) produce.code)
  apply (simp split: event.splits prod.splits option.splits sum.splits)
  subgoal for x2 
    apply (frule produce_inner_skip_n_productions_op_batch_op_xs)
    apply simp
    apply (rule refl)
    apply hypsubst_thin
    apply (frule produce_inner_skip_n_productions_op_batch_op_smaller)
    apply simp_all
    apply auto
    done
  subgoal for x2 
    by (simp add: produce_inner_skip_n_productions_op_batch_op_smaller_Inr)
  done

subsection \<open>ltaken_Data Soundness\<close> 
lemma produce_skip_n_productions_op_batch_op_LE_EX_ltaken_Data:
  "\<exists> n'\<le>n . produce (skip_n_productions_op op n') lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data (Suc n) (produce op lxs))"
  apply (subst (asm) produce_skip_n_productions_op_correctness)
  apply (elim exE conjE)
  using ldropn_LCons_ltaken_Data apply fast
  done

lemma produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX:
  "(wm, batch) \<in> set (ltaken_Data (Suc n) (produce op lxs)) \<Longrightarrow>
   \<exists> n'\<le>n . \<exists> lxs' . produce (skip_n_productions_op op n') lxs = LCons (Data wm batch) lxs'"
  apply (subst produce_skip_n_productions_op_correctness)
  using in_ltaken_Data_ldropn_LCons apply fast
  done

lemma ltaken_Data_produce_batch_op_in_batch_LE:
  "monotone lxs WM \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow> t \<le> wm"
  apply (induct n arbitrary: buf lxs t wm batch WM)
  apply auto
  subgoal premises prems for n buf lxs wm' batch' WM a b
    using prems(2-) apply -
    apply (subst (asm) produce.code)
    apply (auto split: option.splits sum.splits)
    subgoal for  op wm d lxs'
      apply (frule produce_inner_batch_op_specify_Some)
      apply assumption+
      apply (elim conjE exE)
      apply (auto simp add: produce_inner_batch_op_batch_le)
      subgoal for buf' wm d'
        apply (cases n)
        apply simp_all
        subgoal for n'
          using prems(1)[of lxs' WM wm' batch' buf' a] apply simp
          apply (frule produce_inner_batch_op_inversion)
          apply auto
          apply hypsubst_thin
          apply (drule meta_mp)
          using ldrop_enat strict_monotone_ldrop apply blast
          apply (drule meta_mp)
          using ltaken_Data_in_Suc order_less_imp_le apply blast
          apply force
          done
        done
      subgoal for buf' wm 
        apply (cases n)
        apply simp_all
        subgoal for n'
          using prems(1)[of lxs' WM wm' batch' buf' a] apply simp
          apply (frule produce_inner_batch_op_inversion)
          apply auto
          apply hypsubst_thin
          apply (drule meta_mp)
          using ldrop_enat strict_monotone_ldrop apply blast
          apply (drule meta_mp)
          apply (metis fst_conv image_iff)
          apply fast
          done
        done
      done
    using produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX[OF  prems(3)] apply -
    apply auto
    subgoal for exitt n' lxs'
      using produce_skip_n_productions_op_batch_op_batch_op_soundness_LCons_stronger[where n=n', of buf lxs "Data wm' batch'" lxs' WM wm' batch'] apply auto
      done
    done
  done

lemma timestamp_in_taken_Data_inversion:
  "monotone lxs WM \<Longrightarrow>
   t \<in> fst ` (\<Union>a\<in>set (ltaken_Data n (produce (batch_op buf) lxs)). set (snd a)) \<Longrightarrow>
   \<exists> wm \<ge> t . \<exists> batch . (wm, batch) \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<and> t \<in> fst ` set batch"
  using timestamp_in_taken_Data_inversion_aux
    ltaken_Data_produce_batch_op_in_batch_LE
  apply fast
  done 

lemma ltaken_Data_sync_description:
  "monotone lxs WM \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<Longrightarrow>
   fst ` set batch = bach_ts ((map (\<lambda> (t,d). Data t d) buf) @@- lxs) wm \<and>
   (\<forall> t \<in> ts lxs wm . \<exists> wm' batch' . (wm', batch') \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<and> t \<in> fst ` set batch') \<and> 
   (\<forall> t \<in> {t \<in> fst ` set buf . t \<le> wm} . \<exists> wm' batch' . (wm', batch') \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<and> t \<in> fst ` set batch')"
  apply (rule conjI)
  subgoal
    apply (cases n)
    apply simp
    subgoal for n'
      apply hypsubst_thin
      apply (drule produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX)
      apply (elim exE conjE)
      subgoal for n'' lxs'
        using produce_skip_n_productions_op_batch_op_soundness[where x="Data wm batch" and lxs=lxs and buf=buf and n=n'' and WM=WM] apply simp
        done
      done
    done
  apply (rule conjI)
  subgoal
    apply (intro ballI)
    subgoal for t
      apply (cases n)
      apply simp
      subgoal for n'
        apply hypsubst_thin
        apply (frule produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX)
        apply (elim exE conjE)
        subgoal for n'' lxs'
          apply (frule produce_skip_n_productions_op_batch_op_LE_EX[where t=t])
          apply simp
          using ts_le apply blast
          apply assumption+
          apply (meson order_trans produce_skip_n_productions_op_batch_op_LE_EX_ltaken_Data)
          done
        done
      done
    done
  subgoal
    apply (intro ballI)
    subgoal for t
      apply (cases n)
      apply simp
      subgoal for n'
        apply hypsubst_thin
        apply (frule produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX)
        apply (elim exE conjE)
        subgoal for n'' lxs'
          apply (frule produce_skip_n_productions_op_batch_op_LE_EX[where t=t and WM=WM])
          apply simp
          apply fast
          apply assumption+
          apply (meson order_trans produce_skip_n_productions_op_batch_op_LE_EX_ltaken_Data)
          done
        done
      done
    done
  done                 

lemma produce_batch_op_ts_le_1:
  "t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   ts lxs t \<union> {t' \<in> fst ` set buf. t' \<le> t} \<subseteq> {t' \<in> fst ` (\<Union>a\<in>set (ltaken_Data n (produce (batch_op buf) lxs)). set (snd a)). t' \<le> t}"
  apply (frule ltaken_Data_sync_description)
  apply assumption+
  apply (elim exE conjE)
  apply auto
  subgoal for x
    by (metis (no_types, lifting) UN_iff image_UN order_trans snd_conv t_in_ts)
  subgoal for t' d
    apply (smt (verit) UN_iff fst_conv image_UN image_eqI order_trans snd_conv)
    done
  done

lemma produce_batch_op_ts_le_2:
  "t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   {t' \<in> fst ` (\<Union>a\<in>set (ltaken_Data n (produce (batch_op buf) lxs)). set (snd a)). t' \<le> t} \<subseteq> ts lxs t \<union> {t' \<in> fst ` set buf. t' \<le> t}"
  apply (frule ltaken_Data_sync_description)
  apply assumption+
  apply (elim exE conjE)
  apply (intro subsetI)
  apply simp
  subgoal for t'
    apply (cases n)
    apply simp
    subgoal for n'
      apply hypsubst_thin
      apply (frule timestamp_in_taken_Data_inversion[where t=t' and n="Suc n'" and buf=buf])
      apply simp
      apply auto[1]
      apply (metis Domain.DomainI fst_eq_Domain produce_no_timestamps_out_of_the_blue_aux produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX)
      done
    done
  done

lemma produce_batch_op_ts_le:
  "t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   ts lxs t \<union> {t' \<in> fst ` set buf. t' \<le> t} = {t' \<in> fst ` (\<Union>a\<in>set (ltaken_Data n (produce (batch_op buf) lxs)). set (snd a)). t' \<le> t}"
  apply (smt (verit, ccfv_SIG) Collect_cong le_iff_sup produce_batch_op_ts_le_1 produce_batch_op_ts_le_2 sup.order_iff)
  done

lemma produce_inner_skip_n_productions_op_batch_op_coll_list_batch:
  "produce_inner (skip_n_productions_op (batch_op buf) n', lxs) = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   n' \<le> n \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   coll_list (concat (map snd (ltaken_Data (Suc n) (produce (batch_op buf) lxs)))) t = coll_list batch t \<and>
   Watermark wm \<in> lset lxs \<and>
   t \<le> wm \<and>
   (\<exists> d. Data t d \<in> lset lxs \<or> (t, d) \<in> set buf)"
  apply (induct "(skip_n_productions_op (batch_op buf) n', lxs)" r arbitrary: lxs lxs' op buf x xs n n' WM rule: produce_inner_alt)
  subgoal for h lxs lgc' zs buf' n' lxs' op x xs n WM'
    apply (simp del: produce_LCons produce_lshift split: event.splits if_splits option.splits)
    subgoal for t' d
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n"])
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply simp
      apply (simp add: produce_Data)
      apply blast
      done
    subgoal for t' d
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n"])
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply auto
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n - 2"])
      apply (drule meta_spec[of _ "insert wm' WM'"])
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply simp
      apply (simp add: in_buf_produce_Watermark)
      apply (cases n)
       apply auto
       apply (subgoal_tac "\<not> t \<le> wm'")
        defer
      subgoal
        by (meson Data_set_strict_monotone_not_GE insertI1)
      subgoal
        unfolding coll_list_def
        apply (auto simp add: filter_empty_conv)
        done
      subgoal
        unfolding coll_list_def
        apply (auto simp add: filter_empty_conv)
        done
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n - 1"])
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply simp
      apply (simp add: not_in_buf_produce_Watermark)
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
       apply simp
      apply (simp add: in_buf_produce_Watermark)
      apply (cases n)
       apply auto
       apply (subgoal_tac "\<not> t \<le> wm'")
        defer
      subgoal
        by (meson Data_set_strict_monotone_not_GE insertI1)
      subgoal
        unfolding coll_list_def
        apply (auto simp add: filter_empty_conv)
        done
      subgoal
        unfolding coll_list_def
        apply (auto simp add: filter_empty_conv)
        done
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n - 1"])
      apply (drule meta_spec)
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_remove_wm apply blast
      apply (drule meta_mp)
      apply simp
      apply (simp add: in_buf_produce_Watermark ltaken_Data_LCons_Watermark)
      done
    done
  subgoal for h x xs lxs lxs' lgc' buf n' lxs'a op xa xsa n
    apply (subgoal_tac "n' = 0")
    defer
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: event.splits if_splits option.splits)
      apply hypsubst_thin
      apply (metis drop0 drop_Suc_Cons event.distinct(1) less_2_cases list.distinct(1) list.sel(1) not_less_iff_gr_or_eq numeral_2_eq_2)
      apply (metis Suc_lessI bot_nat_0.not_eq_extremum diff_Suc_1 drop0 drop_Cons' list.distinct(1))
      done
    apply simp
    apply (subst produce.code)
    apply (auto split: prod.splits event.splits if_splits option.splits sum.splits; hypsubst_thin)
    apply (smt (verit) coll_list_nil concat.simps(1) event.distinct(1) list.simps(8) llist.distinct(1) llist.inject ltaken_Data.elims)
    subgoal for b aa ba op x xs lxs'
      apply (subst (asm) (1 2) produce_inner.simps)
      apply (auto split: event.splits if_splits option.splits sum.splits llist.splits)
      apply hypsubst_thin
      apply (rule coll_list_concat_ltaken_Data_Nil)
      apply auto
      subgoal for lxs' t' d' a bb wm' batch' baa
        using produce_no_timestamps_out_of_the_blue[where n=0 and buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf @ [(t', d')]" and lxs=lxs' and t=t and wm=wm' and batch=batch'] apply simp
        apply (drule meta_mp)
        subgoal
          apply auto
          apply (meson LConsData insertI1 strict_monotone_LCons_Watermark_insert)
          done
        apply (drule meta_mp)
        apply auto[1]
        apply (meson Data_set_strict_monotone_not_GE insertI1 strict_monotone_drop_head)
        apply force
        done
      subgoal for lxs' t' d' a bb wm' batch' baa
        using produce_no_timestamps_out_of_the_blue[where n=0 and buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf @ [(t', d')]" and lxs=lxs' and t=t and wm=wm' and batch=batch'] apply simp
        apply (drule meta_mp)
        subgoal
          apply auto
          apply (meson LConsData insertI1 strict_monotone_LCons_Watermark_insert)
          done
        apply (drule meta_mp)
        apply auto[1]
        apply (meson Data_set_strict_monotone_not_GE insertI1 strict_monotone_drop_head)
        apply force
        done
      subgoal for lxs' t' d' a bb wm' batch' baa
        using produce_no_timestamps_out_of_the_blue[where n=0 and buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf @ [(t', d')]" and lxs=lxs' and t=t and wm=wm' and batch=batch'] apply simp
        apply (drule meta_mp)
        subgoal
          apply auto
          apply (meson LConsData insertI1 strict_monotone_LCons_Watermark_insert)
          done
        apply (drule meta_mp)
        apply auto[1]
        apply (meson Data_set_strict_monotone_not_GE insertI1 strict_monotone_drop_head)
        apply force
        done
      apply hypsubst_thin
      apply (rule coll_list_concat_ltaken_Data_Nil)
      apply auto
      subgoal for wm'' t' d' a bb wm' batch' baa
        using produce_no_timestamps_out_of_the_blue[where n=0 and buf="filter (\<lambda>x. (case x of (t, _) \<Rightarrow> \<not> t \<le> wm) \<and> (case x of (t, _) \<Rightarrow> \<not> t \<le> wm'')) buf" and lxs=lxs' and t=t and wm=wm' and batch=batch'] apply simp
        apply (drule meta_mp)
        subgoal
          apply auto
          done
        apply (drule meta_mp)
        apply auto[1]
        apply (meson Data_set_strict_monotone_not_GE insertI1 insertI2)
        apply force
        done
      apply hypsubst_thin
      apply (rule coll_list_concat_ltaken_Data_Nil)
      apply auto
      subgoal for wm'' t' d' wm''' batch' wm' 
        using produce_no_timestamps_out_of_the_blue[where n=0 and buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf" and lxs=lxs' and t=t and wm=wm''' and batch=batch'] apply simp
        apply (drule meta_mp)
        apply auto[1]
        apply (drule meta_mp)
        apply (meson Data_set_strict_monotone_not_GE insertI1 insertI2)
        apply force
        done
      done
    subgoal for a t'' d op
      apply (subst (asm) (1 2) produce_inner.simps)
      apply (auto split: event.splits if_splits option.splits sum.splits llist.splits)
      subgoal for t' d'
        apply (rule coll_list_concat_ltaken_Data_Nil)
        apply auto
        apply (metis case_prodD filter_set member_filter sync_batches_from_buf)
        done
      subgoal for lxs'  t' d b c
        apply (rule coll_list_concat_ltaken_Data_Nil)
        apply auto
        subgoal for wm'' batch'' d''
          apply hypsubst_thin
          using produce_no_timestamps_out_of_the_blue[where n=0 and buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf @ [(t', d)]" and lxs=lxs' and t=t and wm=wm'' and batch=batch''] apply simp
          apply (drule meta_spec)+
          apply (drule meta_mp)
          apply (metis produce_inner_skip_n_productions_Inr_op_ldropn produce_skip_n_productions_op_correctness skip_n_productions_op_0)
          apply (drule meta_mp)
          apply (rule refl)
          apply (drule meta_mp)
          apply (rule refl)
          apply (drule meta_mp)
          using strict_monotone_LCons_Watermark_Data_not_ge apply fastforce
          apply (drule meta_mp)
          apply (meson Data_set_strict_monotone_not_GE insertI1 lset_intros(2))
          apply force
          done
        done
      done
    done
  apply auto
  done

(* FIXME: move me*)
lemma coll_list_concat_eq:
  "count_list xs batch = 1 \<Longrightarrow>
   \<forall> x \<in> set xs. x \<noteq> batch \<longrightarrow> coll_list x t = [] \<Longrightarrow>
   coll_list (concat xs) t = coll_list batch t"
  unfolding coll_list_def
  apply (induct xs)
  apply (auto 0 0 split: if_splits)
  apply (smt (z3) Nil_eq_concat_conv count_list_0_iff filter_concat map_eq_set_D)
  done

(* FIXME: move me*)
lemma in_ltaken_Data:
  "Data t d \<in> lset (ltake n lxs) \<Longrightarrow>
   (t, d) \<in> set (ltaken_Data n lxs)"
  apply (induct n arbitrary: lxs)
  using zero_enat_def apply auto[1]
  subgoal for n lxs
    apply (cases lxs)
    apply simp_all
    subgoal for x lxs'
      apply auto
      apply (cases x)
      apply auto
      done
    done
  done

(* FIXME: move me*)
lemma drop_in_Suc_take:
  "drop n xs = y#ys \<Longrightarrow>
   y \<in> set (take (Suc n) xs)"
  by (metis drop_all in_set_conv_decomp leI list.discI nth_via_drop take_Suc_conv_app_nth)

(* FIXME: move me*)
lemma ltaken_Data_llist_of:
  "ltaken_Data n (llist_of xs) = List.map_filter (\<lambda> ev. case ev of Data t d \<Rightarrow> Some (t, d) | _ \<Rightarrow> None) (take n xs)"
  apply (induct xs arbitrary: n)
  apply (auto simp add: List.map_filter_simps)
  subgoal for a xs n
    apply (cases n)
    apply (auto simp add: List.map_filter_simps split: event.splits)
    done
  done

(* FIXME: move me*)
lemma in_on_case_event:
  "\<forall> x \<in> A. is_Data x \<Longrightarrow>
   inj_on (case_event (\<lambda>t d. Some (t, d)) Map.empty) A"
  apply (smt (verit, best) event.case_eq_if event.expand inj_onI option.inject prod.inject)
  done

(* FIXME: move me*)
lemma in_on_the:
  "\<forall> x \<in> A. \<not> Option.is_none x \<Longrightarrow>
   inj_on the A"
  by (metis inj_onI is_none_simps(1) option.expand)

(* FIXME: move me*)
lemma inj_on_snd_set:
  "distinct (map snd xs) \<Longrightarrow>
   inj_on snd (set xs)"
  by (simp add: distinct_map)

(* FIXME: move me*)
lemma in_on_the_case_event:
  "\<forall> x \<in> A. is_Data x \<Longrightarrow>
   inj_on (\<lambda>x. the (case x of Data t d \<Rightarrow> Some (t, d) | Watermark x \<Rightarrow> Map.empty x)) A"
  by (smt (verit) event.case_eq_if event.expand inj_onI option.sel prod.inject)


lemma inj_on_snd_case_event:
  "\<forall> x \<in> A. is_Data x \<Longrightarrow>
   \<forall> x \<in> A. \<forall> y \<in> A. data y = data y \<longrightarrow>  x = y \<Longrightarrow>
   inj_on (snd \<circ> (the \<circ> case_event (\<lambda>t d. Some (t, d)) Map.empty)) A"
  by (simp add: inj_onI)


(* FIXME: move me*)
lemma inj_on_snd_map_filter_take:
  "inj_on f (set (List.map_filter g xs)) \<Longrightarrow>
   inj_on f (set (List.map_filter g (take n xs)))"
  unfolding List.map_filter_def
  apply (induct xs arbitrary: xs)
  apply auto
  apply (smt (verit) Collect_mono_iff image_mono in_set_takeD inj_on_subset)
  done

(* FIXME: move me to utils *)
lemma nth_take_Suc:
  "n' \<le> n \<Longrightarrow>
   n' < length xs \<Longrightarrow>
   xs ! n' = x \<Longrightarrow>
   x \<in> set (take (Suc n) xs)"
  by (metis in_set_conv_nth le_imp_less_Suc length_take min_less_iff_conj nth_take)

(* FIXME: move me to Watermarked_stream *)
lemma map_snd_case_event_map_data:
  "\<forall> x \<in> set xs. is_Data x \<Longrightarrow>
   map (\<lambda>x. snd (the (case x of Data t d \<Rightarrow> Some (t, d) | Watermark x \<Rightarrow> Map.empty x))) xs = map data xs"
  apply (induct xs)
  apply (auto split: event.splits)
  done

(* FIXME: move me to batches lemmas *)
lemma map_snd_ltaken_Data_llist_of_batches:
  "map snd (ltaken_Data n (llist_of (fst (batches wss xs)))) = map data (take n (fst (batches wss xs)))"
  apply (induct wss arbitrary: n xs)
   apply (auto split: prod.splits)
  subgoal for a wss n
    apply (cases n)
     apply simp_all
    apply (metis fst_conv)
    done
  done

(* FIXME: move me to ltaken_Data *)
lemma ltaken_Data_soundness:
  "(wm, batch) \<in> set (ltaken_Data n (llist_of xs)) \<Longrightarrow>
   Data wm batch \<in> set xs"
  apply (induct xs arbitrary: n)
   apply (auto split: prod.splits)
  subgoal for a wss n
    apply (cases n)
     apply (auto simp add: Let_def split: if_splits prod.splits)
    apply (smt (verit) empty_iff fst_conv list.set(1) llist.inject ltaken_Data.elims set_ConsD snd_conv)
    done
  done
(* FIXME: move me to ltaken_Data *)
lemma ltaken_Data_completeness:
  "Data wm batch \<in> set (take n xs) \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (llist_of xs))"
  apply (induct xs arbitrary: n)
   apply (auto split: prod.splits)
  subgoal for a wss n
    apply (cases n)
     apply (auto simp add: Let_def split: if_splits prod.splits)
    apply (smt (verit) Suc_inject list.set_intros(2) llist.distinct(1) llist.inject ltaken_Data.elims nat.discI)
    done
  done

lemma produce_inner_skip_n_productions_op_batch_op_Inr_coll_list:
  "produce_inner (skip_n_productions_op (batch_op buf) n', lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   n' \<le> n \<Longrightarrow>
   exit op = LCons (Data wm batch) lxs' \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   coll_list (concat (map snd (ltaken_Data (Suc n) (produce (batch_op buf) lxs)))) t =
   coll_list batch t \<and> t \<le> wm \<and> \<not> (\<exists> wm' \<ge> wm. Watermark wm' \<in> lset lxs) \<and> 
   (\<exists> d. Data t d \<in> lset lxs \<or> (t, d) \<in> set buf)"
  apply (induct "(skip_n_productions_op (batch_op buf) n', lxs)" r arbitrary:  n n' lxs op buf rule: produce_inner_alt)
  subgoal for h lxs lgc' zs n' buf n op
    apply hypsubst_thin
    apply (cases h)
     apply (simp_all split: if_splits)
    subgoal
      by fastforce
    subgoal
      by (metis Un_iff append_Nil2 bot_nat_0.extremum fst_conv set_ConsD set_append skip_n_productions_op_0 strict_monotone_drop_head)
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ "n' - Suc (Suc 0)"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply blast
      apply (subgoal_tac "\<not> t \<le> wm'")
       defer
      subgoal
        by (metis Data_set_strict_monotone_not_GE case_prodD filter_set insertI1 member_filter)
      apply (cases n)
       apply auto[1]
      subgoal for n'
        apply (elim conjE)
        apply simp
        apply safe
        subgoal
          unfolding coll_list_def
          apply (auto 0 0 simp add: filter_empty_conv split_beta split: prod.splits)
          done
        subgoal
          using order_trans by blast
        subgoal
          apply (subst produce.code)
          apply (auto split: option.splits)
          done
        subgoal
          by fastforce
        subgoal
          unfolding coll_list_def
          apply (auto 0 0 simp add: filter_empty_conv split_beta split: prod.splits)
          done
        subgoal
          using order.trans by blast
        subgoal
          apply (subst produce.code)
          apply (auto split: option.splits)
          done
        subgoal
          by fastforce
        done
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ "n' - Suc 0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n - Suc 0"])
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply blast
      apply (subgoal_tac "\<not> t \<le> wm'")
       defer
      subgoal
        by (metis Data_set_strict_monotone_not_GE case_prodI insertI1)
      apply (cases n)
       apply auto[1]
      subgoal for n'
        apply (elim conjE)
        apply simp
        apply safe
        using order.trans apply blast+
        done
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply blast
      apply (subgoal_tac "\<not> t \<le> wm'")
       defer
      subgoal
        using Data_set_strict_monotone_not_GE by fastforce
      apply (cases n)
       apply auto[1]
      subgoal for n'
        apply (elim conjE)
        apply simp
        apply safe
        subgoal
          unfolding coll_list_def
          apply (auto 0 0 simp add: filter_empty_conv split_beta split: prod.splits)
          done
        subgoal
          using order_trans by blast
        subgoal
          apply (subst produce.code)
          apply (auto split: option.splits)
          done
        subgoal
          by fastforce
        subgoal
          unfolding coll_list_def
          apply (auto 0 0 simp add: filter_empty_conv split_beta split: prod.splits)
          done
        subgoal
          using order.trans by blast
        subgoal
          apply (subst produce.code)
          apply (auto split: option.splits)
          done
        subgoal
          by fastforce
        done
      done
    subgoal for wm'
      apply hypsubst_thin
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "n - Suc 0"])
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply blast
      apply (subgoal_tac "\<not> t \<le> wm'")
       defer
      subgoal
        using Data_set_strict_monotone_not_GE by fastforce
      apply (cases n)
       apply auto[1]
      subgoal for n'
        apply (elim conjE)
        apply simp
        apply safe
        using order.trans apply blast+
        done
      done
    done
   apply simp
  subgoal for n' buf n op
    apply simp
    apply hypsubst_thin
    apply auto
      defer
      apply (metis Domain.intros Domain_fst in_lset_ldropD lset_intros(1) lset_llist_of sync_batches_le_wm)
    subgoal
      by (metis in_lset_ldropD llist.set_intros(1) lset_llist_of sync_batches_from_buf)
    apply (subgoal_tac "fst (batches (maximal_antichain_list (map fst buf)) buf) ! n' = Data wm batch \<and> n' < length (fst (batches (maximal_antichain_list (map fst buf)) buf))")
     defer
     apply (metis (no_types, lifting) drop_eq_Nil2 ldrop_llist_of leI llist.distinct(1) llist_of.simps(1) llist_of_eq_LCons_conv nth_via_drop)
    subgoal premises prems
      using prems(1,4,5) apply -
      apply (subst ltaken_Data_llist_of)
      apply (rule coll_list_concat_eq)
       defer
      subgoal
        unfolding coll_list_def
        apply (auto simp add: map_filter_def filter_empty_conv split: event.splits)
        by (metis Domain.DomainI fst_eq_Domain in_set_takeD nth_mem sync_batches_batches_uniques)
      subgoal
        unfolding coll_list_def
        apply (auto simp add:comp_def map_filter_def filter_empty_conv split: event.splits)
        apply (subst filter_True)
        using in_set_takeD apply fastforce
        apply (simp flip: take_map)
        using sync_batches_unique_data[where wm=wm and batch=batch and A="maximal_antichain_list (map fst buf)" and buf=buf] apply -
        apply (drule meta_mp)
        using maximal_antichain_distinct apply blast
        apply (subst map_snd_case_event_map_data)
        using in_sync_batches_all_Data apply blast
        apply (smt (z3) One_nat_def count_list_1_take event.sel(3) length_map list.set_map maximal_antichain_correct maximal_antichain_subset nth_map nth_mem)
        done
      done
    done
  done

lemma produce_skip_n_productions_op_batch_op_coll_list_batch:
  "produce (skip_n_productions_op (batch_op buf) n') lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   t \<in> ts lxs wm \<or> t \<in> fst ` set buf \<Longrightarrow>
   n' \<le> n \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   coll_list (concat (map snd (ltaken_Data (Suc n) (produce (batch_op buf) lxs)))) t = coll_list batch t"
  apply (subst (asm) produce.code)
  apply (simp split: prod.splits option.splits sum.splits)
  subgoal for op xs lxs'' d
    apply hypsubst_thin
    apply (drule produce_inner_skip_n_productions_op_batch_op_coll_list_batch[where t=t and wm=wm])
    apply (rule refl)+
    apply assumption+
    apply auto
    done
  subgoal for x op
    apply hypsubst_thin
    using produce_inner_skip_n_productions_op_batch_op_Inr_coll_list apply blast
    done
  done

lemma not_timestmap_out_of_the_blue_ltaken_Data:
  "t' \<notin> ts lxs wm \<Longrightarrow> t' \<notin> fst ` set buf \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data (Suc n) (produce (batch_op buf) lxs)) \<Longrightarrow>
   t' \<le> t \<Longrightarrow>
   set (coll_list (concat (map snd (ltaken_Data (Suc n) (produce (batch_op buf) lxs)))) t') = {}"
  unfolding coll_list_def
  apply (simp del: produce_LCons produce_lshift)
  apply (drule produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX)
  apply (elim conjE exE)
  subgoal for b wm' 
    by (smt (verit, ccfv_SIG) Domain.DomainI fst_eq_Domain order_trans prod.collapse produce_no_timestamps_out_of_the_blue_aux produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX)
  done

(* FIXME: move me *)
lemma produce_skip_n_productions_op_batch_op_coll_soundness:
  "produce (skip_n_productions_op (batch_op buf) n) lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   t' \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   coll WM lxs t' + mset (coll_list buf t') = mset (coll_list batch t')"
  unfolding coll_list_def
  using produce_skip_n_productions_op_batch_op_soundness[of "Data wm batch" buf n lxs wm batch WM] apply auto
  by (smt (verit, best) case_prod_unfold filter_cong image_iff mset_filter)


lemma ltaken_Data_produce_soundness:
  "monotone lxs WM \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data (Suc n) (produce (batch_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   t' \<le> t \<Longrightarrow> 
   coll WM lxs t' + mset (coll_list buf t') = mset (coll_list (concat (map snd (ltaken_Data (Suc n) (produce (batch_op buf) lxs)))) t') \<and>
   (\<forall> t \<in> fst ` set batch . t \<le> wm)"
  apply (frule produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX)
  apply (cases "t' \<in> ts lxs wm \<or> t' \<in> fst ` set buf")
  subgoal
    apply (elim exE conjE)
    subgoal for n' lxs'
      apply (drule produce_skip_n_productions_op_batch_op_LE_EX[where t=t'])
      apply assumption+
      apply simp
      apply assumption+
      apply (elim exE conjE)
      subgoal for n'' wm' batch' lxs'
        apply (frule produce_skip_n_productions_op_batch_op_batch_op_soundness_LCons)
        apply (rule refl)
        apply assumption+
        apply (elim conjE)
        apply (subst produce_skip_n_productions_op_batch_op_coll_list_batch)
        apply assumption+
        apply (meson t_in_ts)
        apply simp
        apply assumption+
        apply (meson ltaken_Data_produce_batch_op_in_batch_LE produce_skip_n_productions_op_batch_op_coll_soundness)
        done
      done
    done
  apply (elim exE conjE)
  subgoal for n' lxs'
    apply (subgoal_tac "coll WM lxs t'= {#}")
    defer
    subgoal
      apply (metis (no_types, lifting) coll_empty mem_Collect_eq order_trans ts_def)
      done
    subgoal
      apply (subst coll_list_concat_ltaken_Data_Nil)
      apply (smt (verit, ccfv_threshold) mem_Collect_eq order_trans produce_no_timestamps_out_of_the_blue skip_n_productions_op_0 ts_def)
      unfolding coll_list_def
      by (simp add: image_iff ltaken_Data_produce_batch_op_in_batch_LE)
    done
  done


lemma produce_inner_skip_n_productions_op_Some_Data_in:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: n buf lxs lxs' xs batch wm lgc' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n buf lxs'a xs lgc'a batch wm
    apply (auto split: if_splits event.splits)
    apply fastforce+
    apply (metis fst_conv rotate1.simps(2) set_ConsD set_rotate1 skip_n_productions_op_0)
    apply (metis rotate1.simps(2) set_ConsD set_rotate1 skip_n_productions_op_0 snd_conv)
    apply (metis filter_is_subset skip_n_productions_op_0 subset_code(1))
    apply (metis skip_n_productions_op_0)
    done
  subgoal for h xa xs lxs lxs' lgc' n buf lxs'a xsa batch wm lgc'a
    apply hypsubst_thin
    apply (auto split: if_splits event.splits)
    apply (subgoal_tac "n = 1 \<or> n = 0")
    defer
    apply (metis (mono_tags, lifting) One_nat_def Suc_lessI add.commute bot_nat_0.not_eq_extremum drop_eq_Nil2 leI list.discI list.size(3) list.size(4) plus_1_eq_Suc)
    apply (auto split: if_splits event.splits)
    apply (metis drop_Cons' drop_Nil event.distinct(1) list.distinct(1) nth_Cons_0)
    done
  apply auto
  done 

lemma produce_inner_skip_n_productions_op_Some_Data_Inr_in:
  "produce_inner (skip_n_productions_op (batch_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   Data wm batch \<in> lset (exit op) \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf"
  apply (induct "(skip_n_productions_op (batch_op buf) n, lxs)" r arbitrary: n buf lxs batch wm rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto split: if_splits event.splits)
    apply fastforce+
    apply (metis fst_conv rotate1.simps(2) set_ConsD set_rotate1 skip_n_productions_op_0)
    apply (metis prod.inject rotate1.simps(2) set_ConsD set_rotate1 skip_n_productions_op_0)
    apply (metis filter_set member_filter skip_n_productions_op_0)
    apply (metis skip_n_productions_op_0)
    done
  apply auto
  apply (metis in_lset_ldropD lset_llist_of sync_batches_from_buf)
  done

lemma produce_skip_n_productions_op_Some_Data_in_LCons:
  "produce (skip_n_productions_op (batch_op buf) n) lxs = LCons x xs \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits sum.splits)
  using produce_inner_skip_n_productions_op_Some_Data_in apply fast
  apply (metis lset_intros(1) produce_inner_skip_n_productions_op_Some_Data_Inr_in)
  done 

lemma produce_inner_skip_n_productions_op_batch_op_Watermark_soundness_no_monotone_2:
  "Watermark wm \<in> lset lys \<Longrightarrow>
   produce (skip_n_productions_op (batch_op buf) n) lxs = lys \<Longrightarrow>
   wm \<in> Watermark -` lset lxs"
  apply (induct lys arbitrary: n buf rule: lset_induct)
  subgoal for lxs n buf
    apply auto
    apply (subst (asm) produce.code)
    apply (auto split: option.splits sum.splits)
    using produce_inner_skip_n_productions_op_batch_op_Inl_soundness_no_monotone_2 apply blast
    apply (metis lnth_Data_produce_inner_Some_skip_n_productions_op_batch_op_Inr_LCons_batch_not_ge lset_intros(1))
    done
  subgoal for x xs n buf
    apply auto
    apply (meson produce_skip_n_productions_op_LCons)
    done
  done

lemma in_ltaken_Data_in_lxs:
  "(wm, batch) \<in> set (ltaken_Data n (produce (batch_op buf) lxs)) \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf"
  by (meson Suc_le_mono le_Suc_eq ltaken_Data_in_Suc produce_skip_n_productions_op_Some_Data_in_LCons produce_skip_n_productions_op_batch_op_ltaken_Data_LE_EX)

subsection \<open>Strict monotone proofs\<close>


lemma produce_inner_batch_op_Inl_monotone_1:
  "produce_inner (batch_op buf, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', Data wm batch, xs, lxs') \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   \<forall> (t, d) \<in> set buf. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   Watermark wm \<in> lset input_stream \<and>
   batch \<noteq> [] \<and>
   xs = [Watermark wm] \<and>
   monotone lxs' (insert wm WM) \<and> 
   \<not> (\<exists> t' d'. Data t' d' \<in> lset lxs' \<and> t' \<le> wm) \<and> 
   (\<forall>wm'\<in>WM. \<not> wm \<le> wm') \<and> 
   (\<exists> buf'. lgc' = batch_op buf' \<and> (\<forall> wm' \<in> (insert wm WM). (\<forall> t \<in> fst ` set buf'. \<not> t \<le> wm')))"
  apply (induction "(batch_op buf, input_stream)" r arbitrary: WM input_stream batch wm buf rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (smt (verit, ccfv_threshold) LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    done
  apply (auto simp add: split: llist.splits event.splits if_splits; hypsubst_thin)
  apply (metis case_prodI empty_filter_conv)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: if_splits)
  apply (metis (no_types, lifting) LConsR in_lset_shift_eq produce_inner_LCons_Some_cases produce_inner_to_finite_produce strict_monotone_LCons_Watermark_Data_not_ge)
  apply fastforce+
  done


lemma produce_inner_batch_op_Inl_monotone_2:
  "produce_inner (batch_op buf, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', Watermark wm, xs, lxs') \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   \<forall> (t, d) \<in> set buf. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   Watermark wm \<in> lset input_stream \<and>
   xs = [] \<and>
   monotone lxs' (insert wm WM) \<and> 
   \<not> (\<exists> t' d'. Data t' d' \<in> lset lxs' \<and> t' \<le> wm) \<and> 
   (\<exists> buf'. lgc' = batch_op buf' \<and> \<not> (\<exists> t d. (t, d) \<in> set buf' \<and> t \<le> wm) \<and> (\<forall> wm' \<in> (insert wm WM). (\<forall> t \<in> fst ` set buf'. \<not> t \<le> wm')))"
  apply (induction "(batch_op buf, input_stream)" r arbitrary: WM input_stream wm buf rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)
    apply (smt (verit, best) Data_set_strict_monotone_not_GE fst_conv lset_intros(1) rotate1.simps(2) set_ConsD set_rotate1 strict_monotone_drop_head)
    done
  subgoal for h x xsa lxs lxs'a lgc'a buf WM wm
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: Data_set_strict_monotone_not_GE  split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
    apply fastforce
    done
  apply auto
  done


lemma produce_inner_batch_op_Inr_monotone:
  "produce_inner (batch_op buf, input_stream) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   \<forall> (t, d) \<in> set buf. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   monotone (exit op) WM \<and> 
   (\<forall> x \<in> lset (exit op). is_Data x \<and> (\<forall> wm \<in> WM. \<not> wm \<ge> tmp x))"
  apply (induction "(batch_op buf, input_stream)" r arbitrary: WM input_stream buf op rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
    apply (metis LConsData fst_conv rotate1.simps(2) set_ConsD set_rotate1)+
    done
  apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
  subgoal for buf WM op
    apply (drule Inr_inject)
    apply hypsubst_thin
    apply auto
    apply (rule sync_batches_monotone)
    apply (metis (mono_tags, lifting) case_prod_unfold in_maximal_antichain map_eq_set_D)
    subgoal for x wm
      apply (cases x)
      apply auto
      by (smt (verit) case_prod_unfold map_eq_set_D maximal_antichain_correct maximal_antichain_distinct maximal_antichain_subset subset_code(1) sync_batches_batch_correct)
    done
  done

lemma produce_batch_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   \<forall> (t, d) \<in> set buf. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   produce (batch_op buf) stream_in = stream_out \<Longrightarrow> 
   monotone stream_out WM"
  apply (coinduction arbitrary: stream_in WM stream_out buf rule: strict_monotone_coinduct_strict_monotone_prepend_cong1)
  subgoal for stream_in WM stream_out buf
    apply (subst (asm) produce.code)
    apply (simp split: option.splits prod.splits sum.splits)
    subgoal for x2 d lgc' x' x xs' xs lxs'
      apply hypsubst_thin
      apply (cases x)
      subgoal for wm d
        apply hypsubst_thin
        apply (frule produce_inner_batch_op_Inl_monotone_1)
        apply (rule refl)
        apply assumption
        apply fast
        apply (rule disjI2 exI conjI refl)+
        apply simp
        apply (rule disjI1)
        apply (rule monotone_prepend_cong_prepend)
        apply (rule monotone_prepend_cong_base)
        apply (elim exE conjE)
        apply hypsubst_thin
        apply (rule exI conjI[rotated] refl)+
        subgoal
          apply auto
          apply fastforce
          done
        subgoal 
          apply auto
          done
        subgoal
          apply auto
          by (meson monotone.LNil)
        done
      subgoal wm
        apply hypsubst_thin
        apply (frule produce_inner_batch_op_Inl_monotone_2)
        apply (rule refl)
        apply assumption
        apply blast
        apply (rule disjI2)
        apply (rule disjI1)
        apply (rule exI conjI refl)+
        apply (rule disjI1)
        apply (rule monotone_prepend_cong_prepend)
        apply (rule monotone_prepend_cong_base)
        apply (elim exE conjE)
        apply hypsubst_thin
        apply (rule exI conjI[rotated] refl)+
        apply auto
        apply fastforce
        apply (meson monotone.LNil)
        done
      done
    subgoal for r op'
      apply hypsubst
      apply (frule produce_inner_batch_op_Inr_monotone)
      apply (rule refl)
      apply assumption+
      apply force
      apply (drule sym[of _ "exit op'"])
      apply (cases stream_out)
      apply simp
      subgoal for x xs
        apply (cases x)
        subgoal
          apply simp
          apply (rule disjI2 conjI exI | assumption)+
          by blast
        apply simp
        done
      done
    done
  done

subsection \<open>Productive proofs\<close> 


lemma produce_inner_batch_op_Inl_productive_1:
  "produce_inner (batch_op buf, input_stream) = Some r \<Longrightarrow>
   productive input_stream \<Longrightarrow>
   r = Inl (lgc', Data wm batch, xs, lxs') \<Longrightarrow>
   xs = [Watermark wm] \<and> productive lxs'"
  apply (induction "(batch_op buf, input_stream)" r arbitrary: input_stream buf rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
    using productive_drop_head apply blast+
    done
  apply (subst (asm) produce_inner.simps)
  apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
  using productive_drop_head apply blast+
  done


lemma produce_inner_batch_op_Inl_productive_2:
  "produce_inner (batch_op buf, input_stream) = Some r \<Longrightarrow>
   productive input_stream \<Longrightarrow>
   r = Inl (lgc', Watermark wm, xs, lxs') \<Longrightarrow>
   xs = [] \<and> productive lxs'"
  apply (induction "(batch_op buf, input_stream)" r arbitrary: input_stream buf rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
    using productive_drop_head apply blast+
    done
  apply (subst (asm) produce_inner.simps)
  apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
  using productive_drop_head apply blast+
  done

lemma produce_inner_batch_op_Inr_lfinite:
  "produce_inner (batch_op buf, stream_in) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   lfinite (exit op)"
  apply (induction "(batch_op buf, stream_in)" r arbitrary: stream_in buf rule: produce_inner_alt[consumes 1])
  apply (auto simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
  apply (subst (asm) produce_inner.simps)
  apply (auto  simp add: split_beta split: llist.splits event.splits if_splits prod.splits; hypsubst_thin)
  apply (drule Inr_inject)
  apply hypsubst_thin
  apply simp
  done

lemma produce_batch_op_productive:
  "productive stream_in \<Longrightarrow>
   produce (batch_op buf) stream_in = stream_out \<Longrightarrow> 
   productive stream_out"
  apply (coinduction arbitrary: stream_in stream_out buf rule: productive_coinduct_prepend_cong1)
  subgoal for stream_in stream_out buf
    apply (cases "lfinite stream_out")
    apply simp
    apply hypsubst_thin
    apply (subst (asm) produce.code)
    apply (simp split: option.splits prod.splits sum.splits)
    subgoal for x2 x1 op x2a x x2b xs lxs
      apply hypsubst_thin
      apply (cases x)
      subgoal for wm d
        apply hypsubst_thin
        apply simp
        apply (frule produce_inner_batch_op_Inl_productive_1)
        apply assumption
        apply (rule refl)
        apply (elim conjE)
        apply hypsubst_thin
        apply (rule conjI)
        apply force
        apply (metis (mono_tags, lifting) event.distinct(1) length_Cons less_Suc0 list.size(3) nth_Cons_0 produce_inner_batch_op_inversion_2 productive_prepend_cong1_base productive_prepend_cong1_prepend_1)
        done
      subgoal for wm
        apply hypsubst_thin
        apply simp
        apply (frule produce_inner_batch_op_Inl_productive_2)
        apply assumption
        apply (rule refl)
        apply (elim conjE)
        apply hypsubst_thin
        apply (rule disjI1)
        apply simp
        apply (metis (mono_tags, lifting) produce_inner_batch_op_inversion_2 productive_prepend_cong1_base)
        done
      done
    subgoal for op lxs
      apply (frule produce_inner_Some_Inr_lfinite)
      apply (rule refl)
      apply (rule disjI1)
      apply (subst produce.code)
      apply (auto split: option.splits)
      using produce_inner_batch_op_Inr_lfinite apply auto
      done
    done
  done

subsection \<open>Completeness proofs\<close> 
lemma produce_batch_op_from_buf:
  "x \<in> lset lxs \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   (t, d) \<in> set buf \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   \<exists> wm' d. Data wm' d \<in> lset (produce (batch_op buf) lxs) \<and> t \<in> fst ` set d"
  apply (induct lxs arbitrary: buf rule: lset_induct)
  subgoal for xs buf
    apply (subst produce.code)
    apply (subst produce_inner.simps)
    apply (auto split: llist.splits event.splits option.splits)
    apply (metis (no_types, lifting) case_prodI2 fst_conv image_iff mem_Collect_eq set_filter)
    done
  subgoal for x' xs buf
    apply (cases x')
    defer
    subgoal for wm'
      apply hypsubst_thin
      apply (cases " \<exists>(t, d)\<in>set buf. t \<le> wm'")
      subgoal
        apply (cases "t \<le> wm'")
        defer
        subgoal premises p2
          using p2(1,2,4-) apply -
          apply (subst in_buf_produce_Watermark)
          apply simp
          using p2(3)[where buf="filter (\<lambda>(t, _). \<not> t \<le> wm') buf"] apply -
          apply (drule meta_mp)
          apply simp
          apply (drule meta_mp)
          apply simp
          apply (meson llist.set_intros(2) strict_monotone_remove_wm)
          done
        subgoal premises p2
          using p2(1,2,4-) apply -
          apply (subst in_buf_produce_Watermark)
          apply assumption
          using image_iff apply fastforce
          done
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply assumption
        apply (drule meta_mp)
        apply assumption
        apply (subst not_in_buf_produce_Watermark)
        apply simp_all        
        done
      done
    subgoal for t d
      apply (drule meta_spec[of _ "buf @ [(t, d)]"])
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply assumption
      apply (simp add: produce_Data)
      done
    done
  done


lemma produce_inner_None_finite_aux:
  "produce_inner (batch_op buf, lxs) = None \<Longrightarrow>
   productive lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   False"
  apply (subgoal_tac "lfinite lxs \<or> (\<exists> n t d . lnth lxs n = Data t d)")
  defer
  subgoal 
    unfolding productive_def
    apply (smt (verit, ccfv_threshold) in_buf_produce_Watermark lfinite.simps llist.distinct(1) lnth_0 monotone.simps not_in_buf_produce_Watermark produce_inner_None_produce_LNil)
    done
  apply simp
  apply safe
  subgoal for n t d
    apply (frule productive_finds_data)
    apply assumption+
    apply safe
    subgoal for m wm
      apply (frule produce_inner_conditions_to_produce[where m=n and n=m and d=d and buf=buf])
      apply assumption+
      apply (simp add: not_lfinite_llength)
      apply assumption
      apply (rule disjI2)
      apply fast
      apply simp
      done
    done
  done

lemma produce_inner_None_finite:
  "produce_inner (batch_op buf, lxs) = None \<Longrightarrow>
   productive lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   lfinite lxs"
  using produce_inner_None_finite_aux by blast  


lemma lfinite_batch_op_produces:
  "lfinite lxs \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf \<Longrightarrow>
   \<not> (\<exists> wm. wm \<ge> t \<and> Watermark wm \<in> lset lxs) \<Longrightarrow>
   \<exists>wm out. Data wm out \<in> lset (produce (batch_op buf) lxs) \<and> t \<in> fst ` set out"
  apply (induct lxs arbitrary: buf rule: lfinite_induct)
  subgoal for xs buf
    apply (subst produce.code)
    apply (subst produce_inner.simps)
    apply (auto simp del: produce_LCons produce_lshift simp add: lset_lnull split: llist.splits event.splits option.splits sum.splits)
    using in_sync_batches[where A="maximal_antichain_list (map fst buf)" and buf=buf and t=t and d=d] maximal_antichain_covers_all[where t=t and buf=buf]
    apply (metis Domain.DomainI fst_eq_Domain maximal_antichain_correct)
    done
  apply auto
  subgoal for xs buf
    apply (cases xs)
    apply (simp_all del: produce_LCons produce_lshift)
    apply hypsubst_thin
    apply (subst produce.code)
    apply (subst produce_inner.simps)
    apply (auto 0 0 simp del: produce_LCons produce_lshift simp add: lset_lnull split: llist.splits event.splits option.splits sum.splits)
    apply (meson produce_inner_None_not_lfinite_aux)
    subgoal
      by (metis in_lset_shift_eq insert_iff list.set_intros(1) llist.simps(19) produce_inner_Some_produce rotate1.simps(2) set_rotate1)
    subgoal for lxs' op
      apply (drule meta_spec[of _ "buf @ [(t, d)]"])
      apply auto
      apply (subst (asm) produce.code)
      apply simp
      apply (metis fst_conv imageI)
      done
    subgoal
      using produce_inner_None_not_lfinite_aux by blast
    subgoal
      by (metis in_lset_shift_eq insert_iff llist.simps(19) produce_inner_Some_produce)
    subgoal for lxs' t' d' op
      apply (drule meta_spec[of _ "buf @ [(t', d')]"])
      apply auto
      apply (subst (asm) produce.code)
      apply simp
      apply (metis fst_conv imageI)
      done
    subgoal
      apply fast
      done
    done
  subgoal for xs buf
    apply (cases xs)
    apply auto[1]
    subgoal for x lxs
      apply (cases x)
      subgoal for t d
        apply (drule meta_spec[of _ "buf @ [(t, d)]"])
        apply auto
        done
      subgoal for wm
        apply (cases "t \<le> wm")
        apply auto
        apply (metis (no_types, lifting) case_prodI mem_Collect_eq set_filter)
        done
      done
    done
  done


(* FIXME: move me*)
lemma produce_inner_batch_op_Inr_always_produce:
  "produce_inner (batch_op buf, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf \<Longrightarrow>
   \<exists>wm out. Data wm out \<in> lset (exit op) \<and> t \<in> fst ` set out"
  apply (induct "(batch_op buf, lxs)" r arbitrary: buf lxs op rule: produce_inner_alt[consumes 1])
  apply (auto split: if_splits event.splits)
  using in_sync_batches[where A="maximal_antichain_list (map fst buf)" and buf=buf and t=t and d=d] in_maximal_antichain[where t=t]
  by (smt (z3) Domain.DomainI fst_eq_Domain in_maximal_antichain maximal_antichain_covers_all in_sync_batches)

lemma sync_completeness_gen_aux:
  "(\<exists> i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i) \<or> j = 0 \<and> (\<exists> d. (t, d) \<in> set buf) \<Longrightarrow>
  \<forall> (t', d) \<in> set buf . lfinite lxs \<or> (\<exists> wm \<ge> t' . Watermark wm \<in> lset lxs) \<Longrightarrow>
  productive lxs \<Longrightarrow>
  \<exists> wm out. Data wm out \<in> lset (produce (batch_op buf) lxs) \<and> t \<in> fst ` set out"  
  apply (induct j arbitrary: lxs buf)
  subgoal for lxs buf
    apply simp
    apply (cases "\<exists> wm \<ge> t . Watermark wm \<in> lset lxs")
    apply (elim exE)
    subgoal for d wm
      using produce_batch_op_from_buf[of "Watermark wm" lxs wm t d buf] apply (auto)
      done
    subgoal
      apply (elim exE)
      subgoal for d
        apply (drule bspec[of  _ _ "(t, d)"])
        apply auto
        using lfinite_batch_op_produces apply fast
        done
      done
    done
  subgoal for j' lxs buf
    apply simp
    apply (subgoal_tac "\<not> lnull lxs")
    prefer 2
    subgoal
      by (cases lxs; auto)
    apply (cases j')
    apply simp
    apply (elim exE conjE)
    subgoal premises prems for d
      using prems(1)[where lxs="ltl lxs" and buf="buf @ [(t, d)]"]
      apply -
      apply (drule meta_mp)
      apply auto[1]
      apply (drule meta_mp)
      apply auto[1]
      subgoal
        using prems(2-) apply -
        by (metis (no_types, lifting) enat_ord_code(4) event.distinct(1) in_lset_conv_lnth insert_iff lfinite.simps llist.exhaust_sel llist.simps(19) lnth_0 not_lfinite_llength productive_finds_data)
      subgoal
        using prems(2-) apply -
        by (smt (verit) case_prod_conv event.distinct(1) insert_iff lfinite.simps llist.exhaust_sel llist.simps(19) lnth_0)
      apply (drule meta_mp)
      using prems(2-) apply (metis lhd_LCons_ltl productive_drop_head)
      apply (metis eq_LConsD lnth_0 not_lnull_conv prems(4) prems(7) produce_Data)
      done
    subgoal for n'
      apply simp
      apply (cases "lhd' lxs")
      apply (metis lhd'_def option.distinct(1))
      subgoal for h
        apply (cases h)
        subgoal for t' d
          subgoal premises prems
            using prems(1)[where lxs="ltl lxs" and buf="buf @ [(t', d)]"]
            apply -
            apply (drule meta_mp)
            subgoal using prems(2-) 
              by (simp add: Suc_ile_eq Utils.llength_eSuc_ltl lnth_ltl)
            apply (drule meta_mp)
            subgoal
              apply auto[1]
              subgoal using prems(2-) apply -
                apply (drule productive_ldrop[where n=j'])
                apply (smt (verit, best) bot_nat_0.not_eq_extremum enat_ord_code(4) in_lset_conv_lnth lfinite_ltl lhd'_def lhd_LCons_ltl lnth_0 lnth_LCons' not_lfinite_llength option.inject prems(4) productive_finds_data)
                done
              subgoal 
                using prems(2-) apply -
                apply (drule productive_ldrop[where n=j'])
                by (smt (verit, del_insts) case_prodD event.distinct(1) lhd'_simps(2) lset_cases ltl_simps(2) option.inject)
              done
            apply (drule meta_mp)
            using prems(2-) apply (metis lhd_LCons_ltl productive_drop_head)
            subgoal
              using prems(2-)
              apply (simp add: produce_lhd_data)
              done
            done
          done
        subgoal for wm'
          apply hypsubst_thin
          subgoal premises prems
            apply (subst produce.code)
            using prems(6) apply (simp only: Let_def split: option.splits event.splits prod.splits list.splits sum.splits)
            subgoal
              apply (rule conjI)
              apply (rule impI)
              using prems(4) prems(5)  
              apply (metis eq_LConsD in_buf_produce_Watermark lhd'_def lhd_LCons_ltl not_in_buf_produce_Watermark option.sel produce_inner_None_produce_LNil)
              apply auto[1]
              using prems(2) apply -
              apply (elim conjE exE)
              using prems(3-) apply -
              subgoal for op x xs' lxs' d'
                apply (subst (asm) produce_inner.simps)
                apply (simp del: batch_op.simps batch_op_sel1 split: llist.splits prod.splits list.splits option.splits)
                subgoal for x21 x22 x1 x2
                  apply hypsubst_thin
                  apply (frule batch_op_buf_order_empty_lgc_preserves)
                  apply (elim exE conjE disjE)
                  apply simp_all
                  done
                subgoal for lxs d x22'
                  apply hypsubst_thin
                  apply (frule batch_op_buf_some_out_lgc_preserves)
                  apply (elim exE conjE disjE)
                  apply hypsubst_thin
                  subgoal for t' d
                    using prems(1)[where lxs=lxs' and buf="filter (\<lambda>(t, _). \<not> t \<le> t') buf"] apply -
                    apply (drule meta_mp)
                    using Suc_ile_eq apply blast
                    apply (drule meta_mp)
                    apply force
                    apply (drule meta_mp)
                    using productive_drop_head apply blast
                    apply (elim exE conjE disjE)
                    subgoal for wmm out
                      apply (subst (asm) produce.code)
                      apply (simp split: option.splits)
                      apply (subst produce.code)
                      apply (simp del: batch_op.simps batch_op_sel1 split: prod.splits option.splits)
                      apply hypsubst_thin
                      apply blast
                      done
                    done
                  subgoal for wm'
                    using prems(1)[where lxs=lxs' and buf="buf"] apply -
                    apply (drule meta_mp)
                    using Suc_ile_eq apply blast
                    apply (drule meta_mp)
                    apply force
                    apply (drule meta_mp)
                    using productive_drop_head apply blast
                    apply (elim exE conjE disjE)
                    subgoal for wmm out
                      apply (subst (asm) produce.code)
                      apply (simp split: option.splits)
                      apply (subst produce.code)
                      apply (simp del: batch_op.simps batch_op_sel1 split: prod.splits option.splits)
                      apply hypsubst_thin
                      apply blast
                      done
                    done
                  done
                done
              subgoal for op
                using produce_inner_batch_op_Inr_always_produce 
                by (metis (no_types, lifting) in_lset_conv_lnth)
              done
            done
          done
        done
      done
    done
  done

lemma sync_completeness_gen_aux_alt:
  "Data t d \<in> lset lxs \<or> (t \<in> fst ` set buf) \<Longrightarrow>
   lfinite lxs \<or> (\<forall> (t', d) \<in> set buf . (\<exists> wm \<ge> t' . Watermark wm \<in> lset lxs)) \<Longrightarrow>
  productive lxs \<Longrightarrow>
  \<exists> wm out. Data wm out \<in> lset (produce (batch_op buf) lxs) \<and> t \<in> fst ` set out"  
  apply (subst (asm) in_lset_conv_lnth)
  apply (elim conjE disjE exE)
  subgoal for n
    apply (cases n)
    subgoal
      apply (rule sync_completeness_gen_aux[where j=1])
      apply auto
      done
    subgoal for n'
      apply (rule sync_completeness_gen_aux[where j="Suc (Suc n')"])
      apply auto
      done
    done
  subgoal for n
    apply (cases n)
    subgoal
      apply (rule sync_completeness_gen_aux[where j=1])
      apply auto
      done
    subgoal for n'
      apply (rule sync_completeness_gen_aux[where j="Suc (Suc n')"])
      apply auto
      done
    done
  subgoal 
    apply (rule sync_completeness_gen_aux[where j=0])
    apply auto
    done
  subgoal 
    apply (rule sync_completeness_gen_aux[where j=0])
    apply auto
    done
  done


lemma sync_completeness_gen_aux_alt2:
  "(\<exists> i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i) \<or> j = 0 \<and> (\<exists> d. (t, d) \<in> set buf) \<Longrightarrow>
  lfinite lxs \<or> (\<forall> (t', d) \<in> set buf . (\<exists> wm \<ge> t' . Watermark wm \<in> lset lxs)) \<Longrightarrow>
  productive lxs \<Longrightarrow>
  \<exists> wm out. Data wm out \<in> lset (produce (batch_op buf) lxs) \<and> t \<in> fst ` set out" 
  by (smt (verit, best) case_prod_unfold fst_conv imageI in_lset_conv_lnth sync_completeness_gen_aux_alt)


lemma batch_op_completeness_aux: 
  "enat i < llength lxs \<Longrightarrow>
   lnth lxs i = Data t d\<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> wm out. Data wm out \<in> lset (produce (batch_op []) lxs) \<and> t \<in> fst ` set out"
  using sync_completeness_gen_aux[where buf="[]" and lxs=lxs and j="Suc i"] by auto

lemma batch_op_completeness: 
  "enat i < llength lxs \<Longrightarrow>
   lnth lxs i = Data t d \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> wm out. Data wm out \<in> lset (produce (batch_op []) lxs) \<and> mset (map snd (filter (\<lambda> (t', d) . t' = t) out)) = coll WM lxs t"
  apply (subgoal_tac "Data t d \<in> lset lxs")
  defer
  using in_lset_conv_lnth apply fastforce
  apply (frule batch_op_completeness_aux[where lxs=lxs])
  apply assumption+
  apply (elim disjE exE conjE)
  subgoal for wm out
    apply (rule exI[of _ wm])
    apply (rule exI[of _ out])
    apply simp
    apply (frule produce_batch_op_soundness)
    apply assumption+
    apply (elim conjE)
    apply auto
    done
  done

lemma produce_inner_batch_op_None_no_Watermarks:
  "Watermark wm \<in> lset lxs \<Longrightarrow> 
   produce_inner (batch_op buf, lxs) = None \<Longrightarrow>
   False"
  apply (induct lxs arbitrary: buf rule: lset_induct)
  subgoal
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits)
    done
  apply (subst (asm) (2) produce_inner.simps)
  apply (auto split: if_splits event.splits)
  done

lemma produce_batch_op_Watermark_complete:
  "Watermark wm \<in> lset lxs \<Longrightarrow>
   Watermark wm \<in> lset (produce (batch_op buf) lxs)"
  apply (induct lxs arbitrary: buf rule: lset_induct)
  subgoal
    apply simp
    done
  subgoal for x xs buf
    apply (cases x)
    subgoal
      apply hypsubst_thin
      apply simp
      done
    subgoal
      apply simp
      done
    done
  done

lemma produce_batch_op_Watermark_lset:
  "Watermark -` lset (produce (batch_op buf) lxs) = Watermark -` lset lxs"
  apply safe
  defer
  using produce_batch_op_Watermark_complete apply blast
  subgoal for wm w
    using produce_inner_skip_n_productions_op_batch_op_Watermark_soundness_no_monotone_2[where n=0, simplified] apply force
    done
  done

end