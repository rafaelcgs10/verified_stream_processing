theory Hist_Op
  imports
    "../operators/Incr_Batch_Op"
    "../operators/Map_Op"
    "../Eq_Op"
    "HOL-Library.Code_Lazy"
    "HOL-Library.Product_Lexorder"
begin

definition incr_coll_list :: "'t \<Rightarrow> ('t::order \<times> 'd) list \<Rightarrow> _" where
  "incr_coll_list t xs = sum (\<lambda> t. mset (coll_list xs t)) ({t' \<in> fst ` set xs. t' \<le> t}) "

definition "incr_coll_mset WM lxs t = sum (coll WM lxs) (ts lxs t)"

lemma mset_multi_incr_coll_list_eq_incr_coll_mset:
  "ts lxs t = {t' \<in> fst ` set xs . t' \<le> t} \<Longrightarrow>
   \<forall> t' \<in> {t' \<in> fst ` set xs . t' \<le> t} . coll WM lxs t' = mset (coll_list xs t') \<Longrightarrow>
   incr_coll_list t xs = incr_coll_mset WM lxs t"
  unfolding incr_coll_list_def incr_coll_mset_def
  apply simp
  done

definition "incr_hist_op buf1 buf2 =        
  compose_op (incr_batch_op buf1 buf2) (map_op incr_coll_list)"

lemma incr_hist_op_soundness:
  "Data t hist \<in> lset (produce (incr_hist_op [] []) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   hist = incr_coll_mset WM lxs t"
  unfolding incr_hist_op_def 
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
          apply (rule mset_multi_incr_coll_list_eq_incr_coll_mset)
          apply simp
          apply safe
          apply simp
          done
        done
      done
    done
  done

lemma incr_hist_op_completeness_aux_2:
  "Data t d \<in> lset lxs \<or> t \<in> fst ` set buf1 \<Longrightarrow>
    lfinite lxs \<or> (\<forall>(t', d)\<in>set buf1. (\<exists>wm\<ge>t'. Watermark wm \<in> lset lxs)) \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<forall> (t, d) \<in> set buf1. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (incr_hist_op buf1 buf2) lxs)"
  apply (frule produce_incr_batch_op_completeness_alt[ of _ _ _ _ buf2])
  apply auto[1]
  apply assumption+
  apply (elim exE conjE)
  subgoal for batch
    apply (rule exI[of _ "incr_coll_list t batch"])
    unfolding incr_hist_op_def
    apply (subst produce_compose_op_correctness_alt)
    using finite_produce_map_op_exit_LNil apply blast 
    unfolding  produce_map_op_correctness llist.set_map  
    apply (auto simp add: image_iff split: event.splits)
    done
  done

lemma incr_hist_op_completeness_aux:
  "(\<exists>i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i) \<or> j = 0 \<and> (\<exists>d. (t, d) \<in> set buf1) \<Longrightarrow>
   \<forall>(t', d)\<in>set buf1. lfinite lxs \<or> (\<exists>wm\<ge>t'. Watermark wm \<in> lset lxs) \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<forall> (t, d) \<in> set buf1. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (incr_hist_op buf1 buf2) lxs)"
  apply (frule produce_incr_batch_op_completeness[ of _ _ _ _ buf2])
  apply auto[1]
  apply assumption+
  apply (elim exE conjE)
  subgoal for batch
    apply (rule exI[of _ "incr_coll_list t batch"])
    unfolding incr_hist_op_def
    apply (subst produce_compose_op_correctness_alt)
    using finite_produce_map_op_exit_LNil apply blast
    unfolding  produce_map_op_correctness llist.set_map  
    apply (auto simp add: image_iff split: event.splits)
    done
  done

lemma incr_hist_op_completeness:
  "\<exists>i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i \<Longrightarrow>
   productive lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<forall> (t, d) \<in> set buf1. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (incr_hist_op [] []) lxs) \<and> incr_coll_mset WM lxs t = hist"
  using incr_hist_op_completeness_aux[where t=t and lxs=lxs and j=j and WM=WM, of  "[]" "[]"] apply simp
  apply (elim disjE conjE exE)
  apply (frule incr_hist_op_soundness)
  apply assumption+
  apply simp
  done

lemma incr_hist_op_completeness_2:
  "\<exists> d. Data t d \<in> lset lxs \<Longrightarrow>
   \<exists> wm\<ge>t . Watermark wm \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<forall> (t, d) \<in> set buf1. \<forall> wm \<in> WM. \<not> t \<le> wm \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (incr_hist_op [] []) lxs) \<and> incr_coll_mset WM lxs t = hist"
  apply (subst (asm) lset_conv_lnth)
  apply auto
  subgoal for d wm n
    using incr_hist_op_completeness[where lxs=lxs and WM=WM and j="Suc n" and t=t, of buf1] apply -
    apply (drule meta_mp)
    apply metis
    apply (drule meta_mp)
    apply assumption
    apply (drule meta_mp)
    apply assumption
    apply simp
    done
  done

lemma incr_hist_op_completeness_3:
  "\<exists> d. Data t d \<in> lset lxs \<Longrightarrow>
   \<exists> wm\<ge>t . Watermark wm \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   Data t (incr_coll_mset WM lxs t) \<in> lset (produce (incr_hist_op [] []) lxs)"
  apply (metis (no_types, opaque_lifting) equals0D list.set(1) incr_hist_op_completeness_2)
  done

lemma produce_incr_hist_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (incr_hist_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  unfolding incr_hist_op_def
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_map_op_exit_LNil apply blast
  apply (rule produce_map_op_strict_monotone[of "produce (incr_batch_op buf1 buf2) stream_in" _ "incr_coll_list"])
  unfolding incr_batch_op_def
  apply (rule produce_compose_op_batch_op_incr_op_strict_monotone)
  apply assumption+
  apply (rule refl)
  apply auto
  done

lemma produce_incr_hist_op_productive:
  "productive stream_in \<Longrightarrow>
   monotone stream_in WM \<Longrightarrow>
   produce (incr_hist_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  unfolding incr_hist_op_def
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_map_op_exit_LNil apply blast
  using produce_map_op_strict_productive produce_incr_batch_op_productive by blast

primcorec hist_logic where
  "hist_logic H buf = Logic (\<lambda> ev.
     case ev of
       Data (t::_::linorder) d \<Rightarrow> (hist_logic H (buf @ [(t, d)]), [])
     | Watermark wm \<Rightarrow> if \<exists> (t, d) \<in> set buf . t \<le> wm
                  then let out = [(t, _) \<leftarrow> buf . t \<le> wm] ;
                           buf' = [(t, _) \<leftarrow> buf . t > wm] ;
                           ts = rev (remdups (rev (map fst out))) ;
                           Hs = map (\<lambda> t . Data t (H + (mset (map snd [(t', _) \<leftarrow> out . t' \<le> t])))) ts in
                           (hist_logic (H + (mset (map snd out))) buf', Hs @ [Watermark wm])
                  else (hist_logic H buf, [Watermark wm])
   ) (llist_of (map (\<lambda> t. Data t (H + mset (map snd [(t', _) \<leftarrow> buf . t' \<le> t]))) (rev (remdups (map fst (rev buf))))))"

lemma multi_incr_coll_list_linorder[simp]:
  "incr_coll_list (t::_::linorder) xs = mset (map snd (filter (\<lambda> (t', _) . t' \<le> t) xs))"
  unfolding incr_coll_list_def coll_list_def
  apply (auto simp add: )
  apply (cases "t \<in> fst ` set xs")
  subgoal
    apply (subst sum_le_sum_lt_plus_1)
    apply simp_all
    apply auto
    apply (rule arg_cong2[where f="(+)"])
    defer
    apply (metis (mono_tags, lifting))
    apply (subgoal_tac "image_mset snd {#(t', _) \<in># mset xs. t' < t#} = image_mset snd {#t' \<in># mset xs. fst t' < t#}")
    defer
    apply (metis (mono_tags, lifting) case_prod_unfold )
    apply (simp only: )
    subgoal premises
      apply (subst Sum_mset_mset_fst[symmetric])
      apply auto
      apply (subst Sum_set_image_mset[symmetric])
      apply (simp only: Compr_image_eq)
      apply (rule sum_change_fun)
      apply auto
      apply (metis mset_Collect_filter_mset mset_Collect_fst)
      done
    done
  subgoal
    apply (subst sum_le_sum_lt_plus_2)
    apply simp_all
    apply (subgoal_tac "image_mset snd {#(t', _) \<in># mset xs. t' < t#} = image_mset snd {#t' \<in># mset xs. fst t' < t#}")
    defer
    apply (metis (mono_tags, lifting) case_prod_unfold )
    apply (simp only: )
    subgoal premises prems
      using prems(1) apply -
      apply (subst Sum_mset_mset_fst[symmetric])
      apply auto
      apply (subst Sum_set_image_mset[symmetric])
      apply (simp only: Compr_image_eq)
      apply (subgoal_tac "{#(t', _) \<in># mset xs. t' = t#} = {#}")
      apply simp
      apply (subst Sum_set_image_mset[symmetric])
      apply (rule sum_change_fun)
      apply auto
      apply (metis case_prod_unfold comp_apply)
      apply (smt (verit, best) case_prod_unfold empty_filter_conv image_iff mset.simps(1) mset_filter)
      done
    done
  done

lemma hist_logic_eq_incr_hist_op:
  "\<forall> t \<in> fst ` set buf2 . \<exists> wm \<in> WM . t \<le> wm \<Longrightarrow>
   \<forall> t \<in> fst ` set buf1 . \<forall> wm \<in> WM . t > wm \<Longrightarrow>
   eq_op WM (hist_logic (mset (map snd buf2)) buf1) (incr_hist_op buf1 buf2)"
  unfolding incr_hist_op_def incr_batch_op_def
  apply (coinduction arbitrary: WM buf1 buf2 rule: eq_op.coinduct)
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