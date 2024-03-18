theory Multi_Hist_Op
  imports
    "../operators/Incr_Batch_Op"
    "../operators/Map_Op"
    "HOL-Library.Code_Lazy"
    "../Eq_Op"
begin

definition paths :: "('a::order) set \<Rightarrow> 'a \<Rightarrow> 'a set set" where
  "paths A t = {a \<in> Pow {t' \<in> A . t' < t} . Zorn.pred_on.maxchain {t' \<in> A . t' < t} (<) a}"

definition
  "filter_chains xs = filter (\<lambda> l . (\<forall> (e1::_::order) \<in> (set l). (\<forall> e2 \<in> (set l). e1 < e2 \<or> e2 < e1 \<or> e1 = e2))) xs"

definition 
  "filter_max_chains xs = filter (\<lambda> l . \<forall> l' \<in> set xs . \<not> (set l) \<subset> (set l')) xs"

lemma filter_max_chains_sub_filter_chains:                  
  "set (filter_max_chains xs) \<subseteq> set xs"
  unfolding filter_max_chains_def
  apply (meson filter_is_subset)
  done

lemma filter_chains_subset:
  "set (filter_chains xs) \<subseteq> set xs"
  unfolding filter_chains_def
  apply auto
  done

lemma filter_max_chains_is_chain:
  "x \<in> set ` set (filter_max_chains (filter_chains (List.subseqs xs))) \<Longrightarrow> Zorn.pred_on.chain ((set xs)) (<) x"
  unfolding filter_max_chains_def
  apply (induct xs arbitrary: x)
  apply (simp add: Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def)
  apply (auto simp add: remove_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def Let_def)
  apply (meson subseq_order.dual_order.trans subseq_singleton_left)
  by (meson subseq_order.dual_order.trans subseq_singleton_left)

lemma chain_in_subseqs:
  "Zorn.pred_on.chain ((set xs)) (<) A \<Longrightarrow> A \<in> set ` set (List.subseqs xs)"
  apply (induct xs arbitrary: A)
  apply (simp add: filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def)
  apply (simp add: subset_insert_iff filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def Let_def split: if_splits)
  apply (elim conjE disjE)
  apply (metis Diff_single_insert Pow_iff list.set_map list.simps(15) set_append subseqs.simps(2) subseqs_powset)
  apply (metis Un_iff image_Un)
  done

lemma maxchain_in_subseqs:
  "Zorn.pred_on.maxchain (set xs) (<) A \<Longrightarrow> A \<in> set ` set (List.subseqs xs)"
  using chain_in_subseqs pred_on.maxchain_imp_chain by blast

lemma chain_in_filter_chains:
  "Zorn.pred_on.chain (set xs) (<) A \<Longrightarrow> A \<in> set ` set (filter_chains (List.subseqs xs))" 
  apply (subgoal_tac "A \<subseteq> set xs")
  defer
  apply (simp add: pred_on.chain_def)
  apply (frule chain_in_subseqs)
  unfolding filter_chains_def
  apply auto
  apply hypsubst_thin
  subgoal for A
    apply (induct xs arbitrary: A)
    apply (simp add: filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def)
    using list_emb_Nil2 apply fastforce
    apply auto
    apply (simp add: subset_insert_iff filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def Let_def split: if_splits)
    subgoal for a xs A
      apply (drule meta_spec[of _ "filter ((\<noteq>) a) A"])
      apply (drule meta_mp)
      apply auto
      apply (drule meta_mp)
      apply auto
      apply (drule meta_mp)
      apply (smt (verit, ccfv_SIG) filter.simps(2) list.sel(3) list_emb.simps nth_Cons_0 subseq_filter_left subseq_order.dual_order.trans)
      apply auto
      done
    apply fast
    done
  done

lemma maxchain_in_filter_chains:
  "Zorn.pred_on.maxchain ((set xs)) (<) A \<Longrightarrow> A \<in> set ` set (filter_chains (List.subseqs xs))" 
  using chain_in_filter_chains pred_on.maxchain_imp_chain by blast

lemma filter_subseqs_powset:
  "set ` set (filter (\<lambda> l. P (set l)) (subseqs xs)) = {x \<in> Pow (set xs) . P x}"
  by (smt (verit) Collect_cong image_iff set_filter setcompr_eq_image subseqs_powset)

lemma maxchain_in_filter_max_chains:
  "Zorn.pred_on.maxchain (set xs) (<) A \<Longrightarrow> (A::_::order set) \<in> set ` set (filter_max_chains (filter_chains (List.subseqs xs)))"
  unfolding filter_max_chains_def filter_chains_def
  apply (simp only: filter_filter)
  apply (subst filter_subseqs_powset)
  apply (frule maxchain_in_subseqs)
  apply (frule maxchain_in_filter_chains)
  unfolding Zorn.pred_on.maxchain_def pred_on.chain_def
  apply (induct xs arbitrary: A)
  apply (simp add: filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def)
  apply (simp add: Let_def)
  apply safe
  apply (metis dual_order.refl)
  apply (metis Pow_iff Set.insert_mono image_eqI list.simps(15) psubsetI subseqs_powset)
  apply (metis insert_iff psubsetI subseq_order.dual_order.trans subseq_singleton_left subsetI)
  apply force
  apply (metis Pow_iff Set.insert_mono image_eqI list.simps(15) psubsetI subseqs_powset)
  apply (metis insert_iff psubsetI subseq_order.dual_order.trans subseq_singleton_left subsetI)
  done

lemma filter_max_chains_is_chain_alt:
  "x \<in> set (filter_max_chains (filter_chains (List.subseqs xs))) \<Longrightarrow> Zorn.pred_on.chain ((set xs)) (<) (set x)"
  by (simp add: filter_max_chains_is_chain)

definition paths_from_list :: "('a::order) list \<Rightarrow> 'a \<Rightarrow> 'a list list" where
  "paths_from_list xs t = (
    let less = filter ((>) t) xs in
    let subs = List.subseqs less in
    let maxs = filter_chains subs in
    filter_max_chains maxs
   )"

lemma paths_from_list_soundness:
  "set ` (set (paths_from_list xs t)) \<subseteq> paths (set xs) t"
  apply safe
  subgoal for _ x
    unfolding paths_from_list_def Let_def paths_def
    apply (smt (verit, ccfv_SIG) Collect_cong chain_in_filter_chains chain_in_subseqs filter_max_chains_def filter_max_chains_is_chain_alt image_iff mem_Collect_eq pred_on.maxchain_def set_filter subseqs_powset)
    done
  done

lemma paths_from_list_completeness:
  "paths (set xs) t \<subseteq> set ` (set (paths_from_list xs t))"
  apply safe
  subgoal
    unfolding paths_from_list_def Let_def paths_def
    apply (metis (no_types, lifting) Collect_cong maxchain_in_filter_max_chains mem_Collect_eq set_filter)
    done
  done

lemma paths_from_list_correctness:
  "set ` (set (paths_from_list xs t)) = paths (set xs) t"
  by (simp add: Orderings.order_eq_iff paths_from_list_completeness paths_from_list_soundness)

definition multi_incr_coll_list :: "'t \<Rightarrow> ('t::order \<times> 'd) list \<Rightarrow> _" where
  "multi_incr_coll_list t xs = 
   mset (concat (map (\<lambda> x . concat (map (\<lambda> t' . coll_list xs t') x)) (paths_from_list (remdups (map fst xs)) t))) +
   mset (coll_list xs t)"

lemma distinct_paths_from_list:
  "distinct xs \<Longrightarrow>
   distinct (paths_from_list xs t)"
  unfolding paths_from_list_def Let_def filter_max_chains_def filter_chains_def
  apply (meson distinct_List_subseqs distinct_filter)
  done

lemma le_paths_eq:
  "{a \<in> A . a \<le> (t::_::order)} = {b \<in> B . b \<le> t} \<Longrightarrow>
   paths A t = paths B t"
  unfolding paths_def 
  apply simp
  apply (smt (verit, best) Collect_cong Collect_mono_iff order_less_imp_le)
  done

lemma in_paths_in_set:
  "x \<in> paths A t \<Longrightarrow>
   \<forall> t' \<in> x . t' \<in> A"
  unfolding paths_def
  apply auto
  done

lemma paths_from_list_distinct_lists:
  "distinct xs \<Longrightarrow>
   x \<in> set (paths_from_list xs t) \<Longrightarrow>
   y \<in> set (paths_from_list xs t) \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   set x \<noteq> set y"
  apply (induct xs)
  apply (auto simp add: paths_from_list_def filter_max_chains_def filter_chains_def)[1]
  apply (smt (z3) equals0D filter.simps(1) list.inject list.set_cases set_empty2)
  subgoal for x xs
    unfolding  paths_from_list_def filter_max_chains_def filter_chains_def Let_def
    apply (simp split: if_splits)
    apply safe
    apply (smt (verit, ccfv_SIG) distinct.simps(2) distinct_filter filter_cong filter_in_nths filter_set member_filter subseq_conv_nths)
    done
  done

lemma set_paths_from_list_card_preserves:
  "card (set (paths_from_list (remdups xs) t)) = card (set ` set (paths_from_list (remdups xs) t))"
  apply (subst card_image)
  apply auto[2]
  apply (meson distinct_remdups inj_onI paths_from_list_distinct_lists)
  done

definition "multi_incr_hist_op buf1 buf2 =
  compose_op (incr_batch_op buf1 buf2) (map_op multi_incr_coll_list)"

definition "multi_incr_coll_mset WM lxs t = sum (sum (coll WM lxs)) (paths (ts lxs t) t) + coll WM lxs t"

lemma mset_multi_incr_coll_list_eq_multi_incr_coll_mset:
  "ts lxs t = {t' \<in> fst ` set xs . t' \<le> t} \<Longrightarrow>
   \<forall> t' \<in> {t' \<in> fst ` set xs . t' \<le> t} . coll WM lxs t' = mset (coll_list xs t') \<Longrightarrow>
   multi_incr_coll_list t xs = multi_incr_coll_mset WM lxs t"
  unfolding multi_incr_coll_list_def multi_incr_coll_mset_def
  apply (subst mset_concat)
  apply (subst map_map)
  apply (subst sum_list_distinct_conv_sum_set)
  apply (simp add: distinct_paths_from_list)
  apply simp
  apply (subst mset_concat)
  apply (subst map_map)
  apply (subst Sum_set_sum_list_map_Sum_sum_set)
  subgoal
    apply auto
    apply (metis (no_types, lifting) distinct_filter distinct_remdups filter_chains_subset filter_max_chains_sub_filter_chains paths_from_list_def subseqs_distinctD subset_eq)
    done
  apply (subst sum_sum_change_fun[where g="mset \<circ> coll_list xs"])
  subgoal 
    apply safe
    apply (drule in_paths_in_set)
    apply (smt (verit, ccfv_threshold) comp_apply image_iff mem_Collect_eq sum_change_fun)
    done
  apply (subst Sum_sum_sum_sum)
  apply (simp add: set_paths_from_list_card_preserves)
  apply (simp add: paths_from_list_correctness)
  apply (rule cong[where f="\<lambda> x . sum (sum (\<lambda>x. mset (coll_list xs x))) (paths (fst ` set xs) t) + x" and
        g="\<lambda> x . sum (sum (\<lambda>x. mset (coll_list xs x))) (paths {t' \<in> fst ` set xs. t' \<le> t} t) + x"])
  apply (metis (mono_tags, lifting) Collect_cong le_paths_eq mem_Collect_eq)
  apply (cases "t \<in> fst ` set xs")
  subgoal
    apply (drule spec[of _ t])
    apply (drule mp)
    apply auto
    done
  unfolding coll_def coll_list_def ts_def
  apply auto
  apply (subgoal_tac "t \<notin> {t'. (\<exists>d'. Data t' d' \<in> lset lxs) \<and> t' \<le> t}")
  defer
  apply blast
  apply (subgoal_tac "lfilter (\<lambda>x. case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs = LNil")
  defer
  apply (smt (verit) diverge_lfilter_LNil dual_order.refl event.split_sel le_boolD mem_Collect_eq nless_le)
  apply (smt (verit, del_insts) case_prod_unfold filter_cong filter_mset_False image_iff mset_filter)
  subgoal
    by (smt (verit) case_prod_unfold filter_False image_iff mset_filter mset_zero_iff)
  subgoal
    by (smt (verit, best) case_prod_unfold diverge_lfilter_LNil dual_order.refl event.split_sel filter_False image_iff image_mset_empty le_boolE list_of_LNil map_filter_simps(2) mem_Collect_eq mset.simps(1) mset_filter nless_le)
  subgoal
    by (smt (verit, ccfv_threshold) case_prod_unfold filter_False image_iff image_mset_is_empty_iff list_of_LNil map_filter_simps(2) mset.simps(1) mset_filter)
  done

lemma multi_incr_hist_op_soundness:
  "Data t hist \<in> lset (produce (multi_incr_hist_op [] []) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   hist = multi_incr_coll_mset WM lxs t"
  unfolding multi_incr_hist_op_def 
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_map_op_exit_LNil apply blast
  unfolding produce_map_op_correctness llist.set_map 
  apply (auto simp add: image_iff split: event.splits)
  subgoal for x 
    apply (cases x)
    apply simp_all
    apply hypsubst_thin
    subgoal for d
      apply (subst (asm) in_lset_conv_lnth)
      apply (elim exE conjE)
      subgoal for n    
        apply (frule produce_incr_batch_op_soundness)
        apply assumption+
        apply simp
        apply (elim exE conjE)
        subgoal for m
          apply hypsubst_thin
          apply (rule mset_multi_incr_coll_list_eq_multi_incr_coll_mset)
          apply simp
          apply safe
          apply simp
          done
        done
      done
    done
  done

lemma multi_incr_hist_op_completeness_aux:
  "(\<exists>i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i) \<or> j = 0 \<and> (\<exists>d. (t, d) \<in> set buf1) \<Longrightarrow>
   \<forall>(t', d)\<in>set buf1. lfinite lxs \<or> (\<exists>wm\<ge>t'. Watermark wm \<in> lset lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<forall> (t, d) \<in> set buf1. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (multi_incr_hist_op buf1 buf2) lxs) "
  apply (frule produce_incr_batch_op_completeness[ of _ _ _ _ buf2])
  apply auto[1]
  apply assumption+
  apply (elim exE conjE)
  subgoal for batch
    apply (rule exI[of _ "multi_incr_coll_list t batch"])
    unfolding multi_incr_hist_op_def
    apply (subst produce_compose_op_correctness_alt)
    using finite_produce_map_op_exit_LNil apply blast
    unfolding  produce_map_op_correctness llist.set_map multi_incr_coll_mset_def 
    apply (auto simp add: image_iff split: event.splits)
    done
  done

lemma multi_incr_hist_op_completeness:
  "\<exists>i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<forall> (t, d) \<in> set buf1. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (multi_incr_hist_op [] []) lxs) \<and> multi_incr_coll_mset WM lxs t = hist"
  using multi_incr_hist_op_completeness_aux[where t=t and lxs=lxs and j=j and WM=WM, of  "[]" "[]"] apply simp
  apply (elim disjE conjE exE)
  apply (frule multi_incr_hist_op_soundness)
  apply assumption+
  apply simp
  done

lemma multi_incr_hist_op_completeness_2:
  "\<exists> d. Data t d \<in> lset lxs \<Longrightarrow>
   \<exists> wm\<ge>t . Watermark wm \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<forall> (t, d) \<in> set buf1. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (multi_incr_hist_op [] []) lxs) \<and> multi_incr_coll_mset WM lxs t = hist"
  apply (subst (asm) lset_conv_lnth)
  apply auto
  subgoal for d wm n
    using multi_incr_hist_op_completeness[where lxs=lxs and WM=WM and j="Suc n" and t=t, of buf1] apply -
    apply (drule meta_mp)
    apply metis
    apply (drule meta_mp)
    apply assumption
    apply (drule meta_mp)
    apply assumption
    apply simp
    done
  done

lemma multi_incr_hist_op_completeness_3:
  "\<exists> d. Data t d \<in> lset lxs \<Longrightarrow>
   \<exists> wm\<ge>t . Watermark wm \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   Data t (multi_incr_coll_mset WM lxs t) \<in> lset (produce (multi_incr_hist_op [] []) lxs)"
  apply (metis (no_types, opaque_lifting) equals0D list.set(1) multi_incr_hist_op_completeness_2)
  done

lemma produce_multi_incr_hist_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (multi_incr_hist_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  unfolding multi_incr_hist_op_def
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_map_op_exit_LNil apply blast
  apply (rule produce_map_op_strict_monotone[of "produce (incr_batch_op buf1 buf2) stream_in" _ "multi_incr_coll_list"])
  unfolding incr_batch_op_def
  apply (rule produce_compose_op_batch_op_incr_op_strict_monotone)
  apply assumption+
  apply (rule refl)
  apply auto
  done

lemma produce_multi_incr_hist_op_productive:
  "productive stream_in \<Longrightarrow>
   monotone stream_in WM \<Longrightarrow>
   produce (multi_incr_hist_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  unfolding multi_incr_hist_op_def
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_map_op_exit_LNil apply blast
  using produce_map_op_strict_productive produce_incr_batch_op_productive by blast

(* value "ltaken_Data 10 (produce (multi_incr_hist_op [] []) (LCons (Data 3 2) (LCons (Data 1 2) (LCons (Watermark 3) LNil))::((nat, nat) event) llist))"
 *)

primcorec hist_logic where
  "hist_logic H buf = Logic (\<lambda> ev.
     case ev of
       Data (t::_::linorder) d \<Rightarrow> (hist_logic H (buf @ [(t, d)]), [])
     | Watermark wm \<Rightarrow> if \<exists> (t, d) \<in> set buf . t \<le> wm
                  then let out = filter (\<lambda> (t, _) . t \<le> wm) buf ;
                           buf' = filter (\<lambda> (t, _) . t > wm) buf ;
                           ts = rev (remdups (rev (map fst out))) ;
                           Hs = map (\<lambda> t . Data t (H + (mset (map snd (filter (\<lambda> (t', _) . t' \<le> t) out))))) ts in
                           (hist_logic (H + (mset (map snd out))) buf', Hs @ [Watermark wm])
                  else (hist_logic H buf, [Watermark wm])
   ) (llist_of (map (\<lambda> t. Data t (H + mset (map snd (filter (\<lambda> (t', _). t' \<le> t) buf))))  (rev (remdups (map fst (rev buf))))))"


lemma filter_chains_linorder[simp]:
  "filter_chains (xs::('a::linorder) list list) = xs"
  unfolding filter_chains_def
  using filter_id_conv not_less_iff_gr_or_eq by auto

(* FIXME: move me*)
lemma paths_from_list_singleton:
  "distinct xs \<Longrightarrow>
   paths_from_list xs (t::_::linorder) = [(filter (\<lambda> t' . t' < t) xs)]"
  apply (auto simp add: paths_from_list_def filter_max_chains_def Let_def)
  using filter_Pow 
  apply (smt (verit, best) Collect_cong distinct_filter filter_cong set_filter)
  done

lemma multi_incr_coll_list_linorder[simp]:
  "multi_incr_coll_list (t::_::linorder) xs = mset (map snd (filter (\<lambda> (t', _) . t' \<le> t) xs))"
  unfolding multi_incr_coll_list_def
  apply (subst paths_from_list_singleton)
  apply simp
  apply simp
  unfolding coll_list_def
  apply (auto simp add: order.order_iff_strict)
  apply (subgoal_tac "{#x \<in># mset xs. case x of (t', uu_) \<Rightarrow> t' < t \<or> t' = t#} = {#x \<in># mset xs. case x of (t', uu_) \<Rightarrow> t' < t#} + {#x \<in># mset xs. case x of (t', uu_) \<Rightarrow> t' = t#}")
  defer
  subgoal
    apply (induct xs)
    apply auto
    done
  subgoal premises 
    apply (rule arg_cong2[where f="(+)"])
    defer
    apply (metis (mono_tags, lifting))
    apply (subst mset_concat_sum_filter_fst_snd)
    apply (subst filter_map)
    apply (subst set_map)
    apply (subst mset_map)
    apply (subst mset_filter)
    apply (subgoal_tac "image_mset snd {#(t', _) \<in># mset xs. t' < t#} = image_mset snd {#t' \<in># mset xs. fst t' < t#}")
    defer
    apply (metis (mono_tags, lifting) case_prod_unfold )
    apply (simp only: )
    subgoal premises
      apply simp
      apply (subst Sum_mset_mset_fst[symmetric])
      apply simp
      done
    done
  done

lemma hist_logic_eq_multi_incr_hist_op:
  "\<forall> t \<in> fst ` set buf2 . \<exists> wm \<in> WM . t \<le> wm \<Longrightarrow>
   \<forall> t \<in> fst ` set buf1 . \<forall> wm \<in> WM . t > wm \<Longrightarrow>
   wm_eq WM (hist_logic (mset (map snd buf2)) buf1) (multi_incr_hist_op buf1 buf2)"
  unfolding multi_incr_hist_op_def incr_batch_op_def
  apply (coinduction arbitrary: WM buf1 buf2 rule: wm_eq_coinduct)
  apply (auto simp: comp_def rel_fun_def finite_produce_append not_le rev_map split: list.splits event.splits)
  subgoal for wm  buf2 t d
    apply (rule exI)+
    apply (rule conjI[rotated])
    apply (rule conjI)
    apply (rule refl)
    apply auto
    done
  subgoal for WM buf1 buf2
    apply (auto simp add: sync_batches_linorder produce_map_op_correctness comp_def)
    subgoal for t d
      apply (subgoal_tac "\<not> (\<exists> t' d. (t', d) \<in> set buf2 \<and> t' > t)")
      defer
      subgoal
        apply auto
        by (metis dual_order.trans fst_eqD imageI less_le_not_le)
      apply auto
      subgoal premises prems
        using prems(5) apply -
        apply (induct buf2)
        apply auto
        done
      done
    done
  subgoal for wm buf1 buf2 t 
    apply (rule exI)+
    apply (rule conjI[rotated])
    apply (rule conjI)
    apply (rule refl)
    apply (auto simp: le_max_iff_disj)
    done
  subgoal for WM buf1 buf2 tt t d
    apply (rule map_cong)
    apply (simp add: rev_filter rev_map)
    apply (auto simp add: split_beta comp_def split: prod.splits)
    subgoal for t' d'
      apply (subgoal_tac "\<not> (\<exists> t d. (t, d) \<in> set buf2 \<and> t > t')")
      defer
      subgoal
        apply auto
        by (metis dual_order.trans fst_eqD imageI less_le_not_le)
      subgoal premises prems
        using prems(3,4,5,6,7) apply -
        apply auto
        apply (induct buf2)
        apply auto
        apply (subgoal_tac "{#x \<in># mset buf1. fst x < t' \<and> fst x = tt#} = {#}")
        defer
        subgoal
          using leD by fastforce
        apply clarsimp
        apply (simp flip: image_mset_union)
        apply (rule arg_cong2[where f=image_mset])
        apply blast
        subgoal premises prems2
          using prems2(4) apply -
          apply (induct buf1)
          apply (auto simp add: order.order_iff_strict)
          done
        done
      done
    done
  subgoal for WM buf1 buf2
    apply (auto simp add: sync_batches_linorder produce_map_op_correctness comp_def)
    subgoal for t d
      apply (subgoal_tac "\<not> (\<exists> t' d. (t', d) \<in> set buf2 \<and> t' > t)")
      defer
      subgoal
        apply auto
        by (metis dual_order.trans fst_eqD imageI less_le_not_le)
      apply auto
      subgoal premises prems
        using prems(6,7) apply -
        apply (induct buf2)
        apply auto
        done
      done
    done
  subgoal for wm buf1 buf2 t 
    apply (rule exI)+
    apply (rule conjI[rotated])
    apply (rule conjI)
    apply (rule refl)
    apply (auto simp: le_max_iff_disj)
    done
  subgoal for WM buf1 buf2
    apply (auto simp add: sync_batches_linorder produce_map_op_correctness comp_def)
    subgoal for t d
      apply (subgoal_tac "\<not> (\<exists> t' d. (t', d) \<in> set buf2 \<and> t' > t)")
      defer
      subgoal
        apply auto
        by (metis dual_order.trans fst_eqD imageI less_le_not_le)
      apply auto
      subgoal premises prems
        using prems(6) apply -
        apply (induct buf2)
        apply auto
        done
      done
    done
  done


end