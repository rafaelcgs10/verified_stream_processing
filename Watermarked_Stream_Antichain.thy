theory Watermarked_Stream_Antichain
  imports
    "Antichain"
    "Watermarked_Stream"
begin

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

end