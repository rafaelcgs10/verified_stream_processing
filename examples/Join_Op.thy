theory Join_Op
  imports
    "../operators/Incr_Batch_Op"
    "../operators/Map_Op"
    "../operators/Union_Op"
    "../operators/Flatten_Op"
    "HOL-Library.Code_Lazy"
begin

unused_thms  Llists_Processors Antichain - Batch_Op Flatten_Op Incr_Batch_Op Union_Op Map_Op Antichain


definition join_list where
  "join_list join st xs = 
  (let t = (case st of Inr t \<Rightarrow> t | Inl t \<Rightarrow> t) in
   let lefts = List.map_filter (\<lambda> (v, d). case v of Inr _ \<Rightarrow> None | Inl t' \<Rightarrow> if t = t' then Some d else None) xs in
   let rights = List.map_filter (\<lambda> (v, d). case v of Inl _ \<Rightarrow> None | Inr t' \<Rightarrow> if t = t' then Some d else None) xs in
   concat (map (\<lambda> d1 . List.map_filter (\<lambda> d2 . join d1 d2) rights) lefts))"

lemma map_filter_Nil_conv:
  "List.map_filter P xs \<noteq> [] = (\<exists> x \<in> set xs . P x \<noteq> None)"
  apply (induct xs)
  apply (simp add: List.map_filter_simps)
  apply (auto simp add: List.map_filter_simps split: option.splits)
  done

lemma concat_neq_Nil_conv:
  "concat xs \<noteq> [] = (\<exists> ys \<in> set xs . ys \<noteq> [])"
  using concat_eq_Nil_conv by blast

lemma concat_map_map_filter_neq_Nil_conv:
  "concat (map (\<lambda> d1 . List.map_filter (\<lambda> d2 . join d1 d2) rights) lefts) \<noteq> [] =
   (\<exists> right \<in> set rights . \<exists> left \<in> set lefts . join left right \<noteq> None)"
  apply (induct rights arbitrary: lefts)
  apply (simp add: List.map_filter_simps)
  apply (auto simp add: List.map_filter_simps split: option.splits)
  apply (metis option.distinct(1))
  apply blast
  done  

lemma in_set_map_filter_D:
  "x \<in> set (List.map_filter P xs)  \<Longrightarrow> \<exists> y \<in> set xs . P y = Some x"
  by (smt (verit, ccfv_SIG) filter_set map_eq_set_D map_filter_def member_filter o_apply option.collapse)

lemma join_list_neq_Nil_D:
  "join_list join st xs \<noteq> [] \<Longrightarrow>
   (case st of Inr t \<Rightarrow> t | Inl t \<Rightarrow> t) = t \<Longrightarrow>
   \<exists> d1 d2. ((Inr t), d2) \<in> set xs \<and> ((Inl t), d1) \<in> set xs \<and> join d1 d2 \<noteq> None"
  unfolding join_list_def Let_def 
  apply (simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv)
  apply (elim bexE conjE)
  apply (auto split: if_splits sum.splits option.splits)
  subgoal for d1 d2 y'
    apply (rule exI[of _ d1])
    apply (rule exI[of _ d2])
    apply auto
    subgoal
      apply (drule in_set_map_filter_D)
      apply (auto split: prod.splits sum.splits if_splits)
      apply (smt (verit, best) in_set_map_filter_D is_none_code(2) is_none_simps(1) option.sel prod.case_eq_if prod.collapse sum.case_eq_if sum.split_sels(2))
      done
    subgoal
      apply (drule in_set_map_filter_D)
      apply (auto split: prod.splits sum.splits if_splits)
      apply (metis old.sum.exhaust)
      done
    done
  subgoal for d1 d2 y'
    apply (rule exI[of _ d1])
    apply (rule exI[of _ d2])
    apply auto
    subgoal
      apply (drule in_set_map_filter_D)
      apply (auto split: prod.splits sum.splits if_splits)
      apply (smt (verit, best) in_set_map_filter_D is_none_code(2) is_none_simps(1) option.sel prod.case_eq_if prod.collapse sum.case_eq_if sum.split_sels(2))
      done
    subgoal
      apply (drule in_set_map_filter_D)
      apply (auto split: prod.splits sum.splits if_splits)
      apply (metis old.sum.exhaust)
      done
    done
  done

lemma in_join_list_D:
  "d \<in> set (join_list join st xs) \<Longrightarrow>
   (case st of Inr t \<Rightarrow> t | Inl t \<Rightarrow> t) = t \<Longrightarrow>
   \<exists> d1 d2. ((Inr t), d2) \<in> set xs \<and> ((Inl t), d1) \<in> set xs \<and> join d1 d2 = Some d"
  unfolding join_list_def Let_def 
  apply (simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv)
  apply (elim bexE conjE)
  apply (auto split: if_splits sum.splits option.splits)
  subgoal for z
    apply (smt (verit) in_set_map_filter_D is_none_code(2) is_none_simps(1) old.sum.exhaust option.sel prod.case_eq_if prod.collapse sum.case_eq_if sum.split_sels(2))
    done
  subgoal for x
    apply (smt (verit) in_set_map_filter_D is_none_code(2) is_none_simps(1) old.sum.exhaust option.sel prod.case_eq_if prod.collapse sum.case_eq_if sum.split_sels(2))
    done
  done

lemma in_join_list_Inr:
  "(Inr t, d2) \<in> set batch \<Longrightarrow>
   (Inl t, d1) \<in> set batch \<Longrightarrow>
   join d1 d2 = Some x \<Longrightarrow>
   x \<in> set (join_list join (Inr t) batch)"
  apply (induct batch arbitrary: x d1 d2 t)
  apply simp
  subgoal for a batch x d1 d2 t
    apply (auto simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
    subgoal
      unfolding join_list_def Let_def 
      apply (auto simp add: List.map_filter_simps(1)  concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
      apply (rule bexI[of _ d1])
      apply auto
      unfolding List.map_filter_def
      apply (auto simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: event.splits if_splits sum.splits option.splits)
      using image_iff apply fastforce
      done
    subgoal
      unfolding join_list_def Let_def List.map_filter_def
      apply (auto simp add: List.map_filter_simps(1)  concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
      apply (smt (verit, ccfv_threshold) case_prod_conv image_eqI mem_Collect_eq old.sum.simps(6) option.sel)
      done
    subgoal
      unfolding join_list_def Let_def List.map_filter_def
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (cases a)
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (cases a)
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (rule exI[of _ "Inl t"])
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (rule exI[of _ d1])
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (smt (verit, del_insts) Pair_inject image_iff mem_Collect_eq old.sum.simps(6) option.sel prod.case_eq_if prod.collapse)
      done
    done
  done

lemma in_join_list_Inl:
  "(Inr t, d2) \<in> set batch \<Longrightarrow>
   (Inl t, d1) \<in> set batch \<Longrightarrow>
   join d1 d2 = Some x \<Longrightarrow>
   x \<in> set (join_list join (Inl t) batch)"
  apply (induct batch arbitrary: x d1 d2 t)
  apply simp
  subgoal for a batch x d1 d2 t
    apply (auto simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
    subgoal
      unfolding join_list_def Let_def 
      apply (auto simp add: List.map_filter_simps(1)  concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
      apply (rule bexI[of _ d1])
      apply auto
      unfolding List.map_filter_def
      apply (auto simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: event.splits if_splits sum.splits option.splits)
      using image_iff apply fastforce
      done
    subgoal
      unfolding join_list_def Let_def List.map_filter_def
      apply (auto simp add: List.map_filter_simps(1)  concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
      apply (smt (verit, ccfv_threshold) case_prod_conv image_eqI mem_Collect_eq old.sum.simps(6) option.sel)
      done
    subgoal
      unfolding join_list_def Let_def List.map_filter_def
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (cases a)
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (cases a)
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (rule exI[of _ "Inl t"])
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (rule exI[of _ d1])
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (smt (verit, del_insts) Pair_inject image_iff mem_Collect_eq old.sum.simps(6) option.sel prod.case_eq_if prod.collapse)
      done
    done
  done

lemma mset_concat_remove1:
  "x \<in># mset xs \<Longrightarrow>
  mset (f x) + mset (concat (map f (remove1 x xs))) = mset (concat (map f xs))"
  apply (induct xs)
  apply simp
  apply auto
  done

(* FIXME: move me*)
lemma mset_mset_concat_map:
  "mset xs = mset ys \<Longrightarrow>
  \<forall> x \<in> set xs . mset (f x) = mset (g x) \<Longrightarrow>
   mset (concat (map f xs)) = mset (concat (map g ys))"
  apply (induct xs arbitrary: ys f g)
  apply simp
  subgoal premises prems for a xs ys f g
    using prems(2-) apply auto
    apply (subst prems(1)[of "remove1 a ys"])
    apply (metis add_mset_remove_trivial mset_remove1)
    apply fast
    apply (metis mset_concat_remove1 union_single_eq_member)
    done
  done   

lemma mset_concat_map_map_filter:
  "mset rights1 = mset rights2 \<Longrightarrow>
   mset lefts1 = mset lefts2 \<Longrightarrow>
   mset (concat (map (\<lambda> d1 . List.map_filter (\<lambda> d2 . join d1 d2) rights1) lefts1)) = mset (concat (map (\<lambda> d1 . List.map_filter (\<lambda> d2 . join d1 d2) rights2) lefts2))"
  by (simp add: map_filter_def mset_mset_concat_map)      

lemma image_mset_the_image_mset_Inl:
  "image_mset the
     {#case v of Inl t' \<Rightarrow> if (case Inl t'' of Inl t \<Rightarrow> t | Inr t \<Rightarrow> t) = t' then Some d else None | Inr x \<Rightarrow> Map.empty x. (v,
     d) \<in># {#x \<in># mset xs.
             \<exists>y. (case fst x of Inl t' \<Rightarrow> if (case Inl t'' of Inl t \<Rightarrow> t | Inr t \<Rightarrow> t) = t' then Some (snd x) else None | Inr x \<Rightarrow> Map.empty x) = Some y#}#} =
    image_mset snd {#x \<in># mset xs. Inl t'' = fst x#}"
  apply (induct xs arbitrary: t'')
  apply simp
  apply (auto split: if_splits sum.splits)
  done

lemma image_mset_the_image_mset_Inr:
  "image_mset the
     {#case v of Inl x \<Rightarrow> Map.empty x | Inr t' \<Rightarrow> if (case Inl t'' of Inl t \<Rightarrow> t | Inr t \<Rightarrow> t) = t' then Some d else None. (v,
     d) \<in># {#x \<in># mset xs. \<exists>y. (case fst x of Inl x \<Rightarrow> Map.empty x | Inr t' \<Rightarrow> if (case Inl t'' of Inl t \<Rightarrow> t | Inr t \<Rightarrow> t) = t' then Some (snd x) else None) = Some y#}#} =
    image_mset snd {#x \<in># mset xs. Inr t'' = fst x#}"
  apply (induct xs arbitrary: t'')
  apply simp
  apply (auto split: if_splits sum.splits)
  done

definition "join_op buf1 buf2 buf3 buf4 join =
  compose_op (compose_op (incr_batch_op buf1 buf2) (compose_op (map_op (join_list join)) flatten_op)) (union_op buf3 buf4)"

lemma join_op_soundness:          
  "Data t tuple \<in> lset (produce (join_op [] [] [] {} join) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> d1 d2 . d1 \<in> set (data_list_at lxs (Inl t)) \<and> d2 \<in> set (data_list_at lxs (Inr t)) \<and>
   join d1 d2 = Some tuple"
  unfolding join_op_def 
  apply (subst (asm) produce_compose_op_correctness_alt)
  subgoal
    using finite_produce_union_op_exit_LNil apply blast
    done
  apply (subst (asm) compose_op_assoc[symmetric])
  subgoal 
    using finite_produce_flatten_op_exit_LNil apply blast
    done
  apply (subst (asm) produce_compose_op_correctness_alt)
  subgoal 
    using finite_produce_flatten_op_exit_LNil apply blast
    done
  apply (subst (asm) produce_compose_op_correctness_alt)
  subgoal 
    using finite_produce_map_op_exit_LNil apply blast
    done
  unfolding produce_flatten_op_correctness produce_map_op_correctness 
  apply (drule union_op_Data_soundness)
  apply (auto simp add: image_iff split: event.splits)
  subgoal 
    apply (subst (asm) lset_lconcat)
    apply auto
    subgoal for x
      apply (cases x)
      subgoal for st d
        apply hypsubst_thin
        apply simp
        apply (subst (asm) in_lset_conv_lnth)
        apply (elim exE conjE)
        subgoal for n       
          apply (frule produce_incr_batch_op_soundness)
          apply assumption+
          apply simp
          apply (elim exE conjE)
          subgoal for m
            apply hypsubst_thin
            apply (cases st)
            subgoal for t'
              apply hypsubst_thin
              apply (subgoal_tac "concat (map snd (ltaken_Data m (produce (batch_op []) lxs))) \<noteq> []")
              defer
              apply (smt (verit, ccfv_SIG) empty_iff image_is_empty join_list_neq_Nil_D set_empty2)
              apply (subgoal_tac "tuple \<in> set (join_list join (Inl t') (concat (map snd (ltaken_Data m (produce (batch_op []) lxs)))))")
              defer
              apply force
              apply (subgoal_tac "t = t'")
              defer
              apply fastforce
              apply (drule in_join_list_D)
              apply (rule refl)
              apply (elim exE conjE)
              subgoal for d1 d2
                apply (rule exI[of _ d1])
                apply (rule conjI)
                subgoal premises prems2
                  using prems2(1,2,8,9,10,11) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                    apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inl t'" and t'="Inl t'" and wm=t3 and batch=dd3 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                      apply (metis fst_conv image_eqI ltaken_Data_produce_batch_op_in_batch_LE)
                      apply (drule meta_mp)
                      apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (subgoal_tac " Data (Inl t') d1 \<in> lset lxs")
                      defer
                      subgoal
                        using in_ltaken_Data_in_lxs 
                        apply (metis (no_types, opaque_lifting) empty_iff set_empty2)
                        done
                      apply (rule image_eqI[where b=d1 and f="\<lambda>x. the (get_Data x)" and x="Data (Inl t') d1"])
                      apply (auto split: if_splits)
                      subgoal
                        apply (subst set_list_of)
                        apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                        apply auto
                        done
                      subgoal
                        apply (subgoal_tac "\<exists>wm. Watermark (Inl wm) \<in> lset lxs \<and> t' \<le> wm")
                        using Inl_leq apply blast
                        using productive_Data_in_ge_Watermark_in 
                        apply metis
                        done
                      done
                    done
                  done
                apply (rule exI[of _ d2])
                subgoal premises prems2
                  using prems2(1,2,8,9,10,11) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                    apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inr t'" and t'="Inr t'" and wm =t2 and batch=dd2 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                      apply (metis fst_conv image_eqI ltaken_Data_produce_batch_op_in_batch_LE)
                      apply (drule meta_mp)
                      apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (subgoal_tac " Data (Inr t') d2 \<in> lset lxs")
                      defer
                      subgoal
                        using in_ltaken_Data_in_lxs 
                        apply (metis (no_types, opaque_lifting) empty_iff set_empty2)
                        done
                      apply (rule image_eqI[where b=d2 and f="\<lambda>x. the (get_Data x)" and x="Data (Inr t') d2"])
                      apply (auto split: if_splits)
                      subgoal
                        apply (subst set_list_of)
                        apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                        apply auto
                        done
                      subgoal
                        apply (subgoal_tac "\<exists>wm. Watermark (Inr wm) \<in> lset lxs \<and> t' \<le> wm")
                        using Inr_leq apply blast
                        using productive_Data_in_ge_Watermark_in 
                        apply metis
                        done
                      done
                    done
                  using prems2 apply blast
                  done
                done
              done
            subgoal for t'
              apply hypsubst_thin
              apply (subgoal_tac "concat (map snd (ltaken_Data m (produce (batch_op []) lxs))) \<noteq> []")
              defer
              apply (smt (verit, ccfv_SIG) empty_iff image_is_empty join_list_neq_Nil_D set_empty2)
              apply (subgoal_tac "tuple \<in> set (join_list join (Inl t') (concat (map snd (ltaken_Data m (produce (batch_op []) lxs)))))")
              defer
              apply force
              apply (subgoal_tac "t = t'")
              defer
              apply fastforce
              apply (drule in_join_list_D)
              apply (rule refl)
              apply (elim exE conjE)
              subgoal for d1 d2
                apply (rule exI[of _ d1])
                apply (rule conjI)
                subgoal premises prems2
                  using prems2(1,2,8,9,10,11) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                    apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inl t'" and t'="Inl t'" and wm=t3 and batch=dd3 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                      apply (metis fst_conv image_eqI ltaken_Data_produce_batch_op_in_batch_LE)
                      apply (drule meta_mp)
                      apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (subgoal_tac " Data (Inl t') d1 \<in> lset lxs")
                      defer
                      subgoal
                        using in_ltaken_Data_in_lxs 
                        apply (metis (no_types, opaque_lifting) empty_iff set_empty2)
                        done
                      apply (rule image_eqI[where b=d1 and f="\<lambda>x. the (get_Data x)" and x="Data (Inl t') d1"])
                      apply (auto split: if_splits)
                      subgoal
                        apply (subst set_list_of)
                        apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                        apply auto
                        done
                      subgoal
                        apply (subgoal_tac "\<exists>wm. Watermark (Inl wm) \<in> lset lxs \<and> t' \<le> wm")
                        using Inl_leq apply blast
                        using productive_Data_in_ge_Watermark_in 
                        apply metis
                        done
                      done
                    done
                  done
                apply (rule exI[of _ d2])
                subgoal premises prems2
                  using prems2(1,2,8,9,10,11) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                    apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inr t'" and t'="Inr t'" and wm =t2 and batch=dd2 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                      apply (metis fst_conv image_eqI ltaken_Data_produce_batch_op_in_batch_LE)
                      apply (drule meta_mp)
                      apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (subgoal_tac " Data (Inr t') d2 \<in> lset lxs")
                      defer
                      subgoal
                        using in_ltaken_Data_in_lxs 
                        apply (metis (no_types, opaque_lifting) empty_iff set_empty2)
                        done
                      apply (rule image_eqI[where b=d2 and f="\<lambda>x. the (get_Data x)" and x="Data (Inr t') d2"])
                      apply (auto split: if_splits)
                      subgoal
                        apply (subst set_list_of)
                        apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                        apply auto
                        done
                      subgoal
                        apply (subgoal_tac "\<exists>wm. Watermark (Inr wm) \<in> lset lxs \<and> t' \<le> wm")
                        using Inr_leq apply blast
                        using productive_Data_in_ge_Watermark_in 
                        apply metis
                        done
                      done
                    done
                  using prems2 apply blast
                  done
                done
              done
            done
          done
        done
      subgoal for wm
        apply simp
        done
      done
    done
  subgoal 
    apply (subst (asm) lset_lconcat)
    apply auto
    subgoal for x
      apply (cases x)
      subgoal for st d
        apply hypsubst_thin
        apply simp
        apply (subst (asm) in_lset_conv_lnth)
        apply (elim exE conjE)
        subgoal for n       
          apply (frule produce_incr_batch_op_soundness)
          apply assumption+
          apply simp
          apply (elim exE conjE)
          subgoal for m
            apply hypsubst_thin
            apply (cases st)
            subgoal for t'
              apply hypsubst_thin
              apply (subgoal_tac "concat (map snd (ltaken_Data m (produce (batch_op []) lxs))) \<noteq> []")
              defer
              apply (smt (verit, ccfv_SIG) empty_iff image_is_empty join_list_neq_Nil_D set_empty2)
              apply (subgoal_tac "tuple \<in> set (join_list join (Inl t') (concat (map snd (ltaken_Data m (produce (batch_op []) lxs)))))")
              defer
              apply force
              apply (subgoal_tac "t = t'")
              defer
              apply fastforce
              apply (drule in_join_list_D)
              apply (rule refl)
              apply (elim exE conjE)
              subgoal for d1 d2
                apply (rule exI[of _ d1])
                apply (rule conjI)
                subgoal premises prems2
                  using prems2(1,2,8,9,10,11) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                    apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inl t'" and t'="Inl t'" and wm=t3 and batch=dd3 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                      apply (metis fst_conv image_eqI ltaken_Data_produce_batch_op_in_batch_LE)
                      apply (drule meta_mp)
                      apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (subgoal_tac " Data (Inl t') d1 \<in> lset lxs")
                      defer
                      subgoal
                        using in_ltaken_Data_in_lxs 
                        apply (metis (no_types, opaque_lifting) empty_iff set_empty2)
                        done
                      apply (rule image_eqI[where b=d1 and f="\<lambda>x. the (get_Data x)" and x="Data (Inl t') d1"])
                      apply (auto split: if_splits)
                      subgoal
                        apply (subst set_list_of)
                        apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                        apply auto
                        done
                      subgoal
                        apply (subgoal_tac "\<exists>wm. Watermark (Inl wm) \<in> lset lxs \<and> t' \<le> wm")
                        using Inl_leq apply blast
                        using productive_Data_in_ge_Watermark_in 
                        apply metis
                        done
                      done
                    done
                  done
                apply (rule exI[of _ d2])
                subgoal premises prems2
                  using prems2(1,2,8,9,10,11) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                    apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inr t'" and t'="Inr t'" and wm =t2 and batch=dd2 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                      apply (metis fst_conv image_eqI ltaken_Data_produce_batch_op_in_batch_LE)
                      apply (drule meta_mp)
                      apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (subgoal_tac " Data (Inr t') d2 \<in> lset lxs")
                      defer
                      subgoal
                        using in_ltaken_Data_in_lxs 
                        apply (metis (no_types, opaque_lifting) empty_iff set_empty2)
                        done
                      apply (rule image_eqI[where b=d2 and f="\<lambda>x. the (get_Data x)" and x="Data (Inr t') d2"])
                      apply (auto split: if_splits)
                      subgoal
                        apply (subst set_list_of)
                        apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                        apply auto
                        done
                      subgoal
                        apply (subgoal_tac "\<exists>wm. Watermark (Inr wm) \<in> lset lxs \<and> t' \<le> wm")
                        using Inr_leq apply blast
                        using productive_Data_in_ge_Watermark_in 
                        apply metis
                        done
                      done
                    done
                  using prems2 apply blast
                  done
                done
              done
            subgoal for t'
              apply hypsubst_thin
              apply (subgoal_tac "concat (map snd (ltaken_Data m (produce (batch_op []) lxs))) \<noteq> []")
              defer
              apply (smt (verit, ccfv_SIG) empty_iff image_is_empty join_list_neq_Nil_D set_empty2)
              apply (subgoal_tac "tuple \<in> set (join_list join (Inr t') (concat (map snd (ltaken_Data m (produce (batch_op []) lxs)))))")
              defer
              apply force
              apply (subgoal_tac "t = t'")
              defer
              apply fastforce
              apply (drule in_join_list_D)
              apply (rule refl)
              apply (elim exE conjE)
              subgoal for d1 d2
                apply (rule exI[of _ d1])
                apply (rule conjI)
                subgoal premises prems2
                  using prems2(1,2,8,9,10,11) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                    apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inl t'" and t'="Inl t'" and wm=t3 and batch=dd3 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                      apply (metis fst_conv image_eqI ltaken_Data_produce_batch_op_in_batch_LE)
                      apply (drule meta_mp)
                      apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (subgoal_tac " Data (Inl t') d1 \<in> lset lxs")
                      defer
                      subgoal
                        using in_ltaken_Data_in_lxs 
                        apply (metis (no_types, opaque_lifting) empty_iff set_empty2)
                        done
                      apply (rule image_eqI[where b=d1 and f="\<lambda>x. the (get_Data x)" and x="Data (Inl t') d1"])
                      apply (auto split: if_splits)
                      subgoal
                        apply (subst set_list_of)
                        apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                        apply auto
                        done
                      subgoal
                        apply (subgoal_tac "\<exists>wm. Watermark (Inl wm) \<in> lset lxs \<and> t' \<le> wm")
                        using Inl_leq apply blast
                        using productive_Data_in_ge_Watermark_in 
                        apply metis
                        done
                      done
                    done
                  done
                apply (rule exI[of _ d2])
                subgoal premises prems2
                  using prems2(1,2,8,9,10,11) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                    apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inr t'" and t'="Inr t'" and wm =t2 and batch=dd2 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                      apply (metis fst_conv image_eqI ltaken_Data_produce_batch_op_in_batch_LE)
                      apply (drule meta_mp)
                      apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (subgoal_tac " Data (Inr t') d2 \<in> lset lxs")
                      defer
                      subgoal
                        using in_ltaken_Data_in_lxs 
                        apply (metis (no_types, opaque_lifting) empty_iff set_empty2)
                        done
                      apply (rule image_eqI[where b=d2 and f="\<lambda>x. the (get_Data x)" and x="Data (Inr t') d2"])
                      apply (auto split: if_splits)
                      subgoal
                        apply (subst set_list_of)
                        apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                        apply auto
                        done
                      subgoal
                        apply (subgoal_tac "\<exists>wm. Watermark (Inr wm) \<in> lset lxs \<and> t' \<le> wm")
                        using Inr_leq apply blast
                        using productive_Data_in_ge_Watermark_in 
                        apply metis
                        done
                      done
                    done
                  using prems2 apply blast
                  done
                done
              done
            done
          done
        done
      subgoal for wm
        apply simp
        done
      done
    done
  done

lemma join_op_completeness:
  "Data (Inl t) d1 \<in> lset lxs \<Longrightarrow>
   Data (Inr t) d2 \<in> lset lxs  \<Longrightarrow>
   join d1 d2 = Some tuple \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> productive lxs \<Longrightarrow> 
   Data t tuple \<in> lset (produce (join_op [] [] buf1 buf2 join) lxs)"
  unfolding  join_op_def 
  using produce_incr_batch_op_completeness_alt[where lxs=lxs and t="Inl t", of d1 "[]" "[]"] apply simp
  using produce_incr_batch_op_completeness_alt[where lxs=lxs and t="Inr t", of d2 "[]" "[]"] apply simp
  apply (elim disjE exE)
  subgoal for batch1 batch2
    apply (subgoal_tac "(Inl t, d1) \<in> set batch1")
    defer
    subgoal
      using produce_incr_batch_op_soundness_alt[of "Inl t" batch1 "[]" "[]" lxs WM] apply simp
      apply (elim exE conjE)
      unfolding coll_list_def coll_def
      apply (drule spec[of _ "Inl t"])
      apply (drule mp)
      apply simp
      subgoal 
        apply (auto simp del: mset_map split: event.splits if_splits)
        apply hypsubst_thin
        subgoal
          apply (drule mset_eq_setD)
          apply simp
          unfolding List.map_filter_def
          apply simp
          apply (subst (asm) set_list_of)
          apply (smt (verit, best) dual_order.refl event.distinct(1) event.inject(1) event.split_sel le_boolE lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
          apply auto
          apply (subgoal_tac "Data (Inl t) d1 \<in> {x \<in> lset lxs. (\<forall>x11. (\<forall>x12. x \<noteq> Data x11 x12) \<or> x11 = Inl t) \<and> (\<forall>x2. x \<noteq> Watermark x2) \<and> (\<exists>y. get_Data x = Some y)}")
          defer
          using in_lset_conv_lnth  apply force
          apply (smt (verit, ccfv_threshold) event.simps(5) image_iff mem_Collect_eq option.sel prod.collapse)
          done
        subgoal
          apply (drule mset_eq_setD)
          apply simp
          unfolding List.map_filter_def
          apply simp
          apply (smt (verit) event.sel(1) event.simps(4) event.simps(5) imageE imageI in_lset_conv_lnth mem_Collect_eq option.sel prod.exhaust_sel)
          done
        subgoal
          apply (metis (no_types, lifting) in_lset_conv_lnth productive_Data_in_ge_Watermark_in)
          done
        done
      done
    apply (subgoal_tac "(Inr t, d2) \<in> set batch2")
    defer
    subgoal
      using produce_incr_batch_op_soundness_alt[of "Inr t" batch2 "[]" "[]" lxs WM] apply simp
      apply (elim exE conjE)
      unfolding coll_list_def coll_def
      apply (drule spec[of _ "Inr t"])
      apply (drule mp)
      apply simp
      subgoal for n
        apply (auto simp del: mset_map split: event.splits if_splits)
        apply hypsubst_thin
        subgoal
          apply (drule mset_eq_setD)
          apply simp
          unfolding List.map_filter_def
          apply simp
          apply (subst (asm) set_list_of)
          apply (smt (verit, best) dual_order.refl event.distinct(1) event.inject(1) event.split_sel le_boolE lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
          apply auto
          apply (subgoal_tac "Data (Inr t) d2 \<in> {x \<in> lset lxs. (\<forall>x11. (\<forall>x12. x \<noteq> Data x11 x12) \<or> x11 = Inr t) \<and> (\<forall>x2. x \<noteq> Watermark x2) \<and> (\<exists>y. get_Data x = Some y)}")
          defer
          using in_lset_conv_lnth  apply force
          apply (smt (verit, ccfv_threshold) event.simps(5) image_iff mem_Collect_eq option.sel prod.collapse)
          done
        subgoal
          apply (drule mset_eq_setD)
          apply simp
          apply hypsubst_thin
          apply (subst (asm) list_of_lfilter_lfinite)
          apply assumption
          unfolding List.map_filter_def
          apply simp
          apply (subgoal_tac "Data (Inr t) d2 \<in> {x \<in> lset lxs. (\<forall>x11. (\<forall>x12. x \<noteq> Data x11 x12) \<or> x11 = Inr t) \<and> (\<forall>x2. x \<noteq> Watermark x2) \<and> (\<exists>y. get_Data x = Some y)}")
          defer
          using in_lset_conv_lnth  apply force
          apply (smt (verit, best) event.simps(5) image_iff mem_Collect_eq option.sel prod.exhaust_sel)
          done
        subgoal
          apply (metis (no_types, lifting) in_lset_conv_lnth productive_Data_in_ge_Watermark_in)
          done
        done
      done
    apply (subst produce_compose_op_correctness_alt)
    subgoal
      using finite_produce_union_op_exit_LNil apply blast
      done
    apply (subst compose_op_assoc[symmetric])
    subgoal
      using finite_produce_flatten_op_exit_LNil apply blast
      done
    apply (subst produce_compose_op_correctness_alt)
    subgoal
      using finite_produce_flatten_op_exit_LNil apply blast
      done
    apply (subst produce_compose_op_correctness_alt)
    subgoal
      using finite_produce_map_op_exit_LNil apply blast
      done
    unfolding produce_map_op_correctness produce_flatten_op_correctness
    apply (auto split: event.splits)
    apply (frule incr_batch_op_prefix_cases[of _ batch1 _ _ _ _ batch2])
    apply assumption+           
    apply (elim disjE)
    subgoal
      apply (rule produce_union_op_Inr_completeness)
      apply (subst lset_lconcat)
      apply auto
      apply (rule bexI[of _ "Data (Inr t) batch2"])
      apply auto
      using in_join_list_Inr set_mono_prefix apply fastforce
      done
    subgoal
      apply (rule produce_union_op_Inl_completeness)
      apply (subst lset_lconcat)
      apply auto
      apply (rule bexI[of _ "Data (Inl t) batch1"])
      apply auto
      using in_join_list_Inl set_mono_prefix apply fastforce
      done
    done 
  done

lemma produce_join_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   buf4 = maximal_antichain_set WM \<Longrightarrow>
   set buf3 = unproduced_watermarks WM \<Longrightarrow>
   maximal_complete WM \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (join_op buf1 buf2 buf3 buf4 join) stream_in = stream_out \<Longrightarrow>
   monotone stream_out (Inl -` (WM - set buf3) \<union> Inr -` (WM - set buf3))"
  unfolding join_op_def 
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_union_op_exit_LNil apply blast
  apply (subst (asm) compose_op_assoc[symmetric])
  using finite_produce_flatten_op_exit_LNil apply blast
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_flatten_op_exit_LNil apply blast
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_map_op_exit_LNil apply blast
  using produce_map_op_strict_monotone produce_incr_batch_op_strict_monotone produce_flatten_op_strict_monotone
    produce_union_op_monotone 
  apply metis
  done

lemma produce_join_op_strict_monotone_alt:
  "monotone stream_in {} \<Longrightarrow>
   produce (join_op [] [] [] {} join) stream_in = stream_out \<Longrightarrow>
   monotone stream_out {}"
  using produce_join_op_strict_monotone[of stream_in "{}" "{}" "[]" "[]" "[]" join stream_out]
  by (simp add: maximal_complete_def unproduced_watermarks_def)

lemma Watermark_Union_case_simp:
  "(Watermark -`
      (\<Union>x\<in>lset lxs.
          set (case case x of Data t d \<Rightarrow> Data t (join_list join t d) | Watermark x \<Rightarrow> Watermark x of
               Data t x \<Rightarrow> map (Data t) x | Watermark wm \<Rightarrow> [Watermark wm]))) =
   (Watermark -` lset lxs)"
  apply (auto split: event.splits)
  done

lemma produce_join_op_productive:
  "productive stream_in \<Longrightarrow>
   maximal_complete buf4 \<Longrightarrow>
   (\<forall> wm \<in> Watermark -` lset stream_in. producible wm (buf4 \<union> (Watermark -` lset stream_in))) \<Longrightarrow>
   produce (join_op buf1 buf2 buf3 buf4 join) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  unfolding join_op_def 
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_union_op_exit_LNil apply blast
  apply (subst (asm) compose_op_assoc[symmetric])
  using finite_produce_flatten_op_exit_LNil apply blast
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_flatten_op_exit_LNil apply blast
  apply (subst (asm) produce_compose_op_correctness_alt)
  using finite_produce_map_op_exit_LNil apply blast
  apply hypsubst_thin
  apply (rule produce_union_productive)
  prefer 4
  apply (rule refl)
  apply (rule produce_flatten_op_productive)
  prefer 2
  apply (rule refl)
  apply (rule produce_map_op_strict_productive)
  prefer 2
  apply (rule refl)
  apply (rule produce_incr_batch_op_productive)
  prefer 2
  apply (rule refl)
  apply assumption+
  apply auto
  apply (auto simp add: produce_flatten_op_correctness lset_lconcat produce_map_op_correctness)
  subgoal for wm x
    apply (cases x)
    apply auto
    apply hypsubst_thin
    apply (drule bspec[of _ _ wm])
    using produce_incr_batch_op_Watermark_lset apply blast
    apply (drule producible_unionE)
    apply (elim disjE)
    using producible_unionI apply blast
    apply (rule producible_unionI)
    apply (rule disjI2)
    apply (subst Watermark_Union_case_simp)
    apply (subst produce_incr_batch_op_Watermark_lset)
    apply assumption
    done
  done

lemma produce_join_op_productive_alt:
  "productive stream_in \<Longrightarrow>
   (\<forall> wm \<in> Watermark -` lset stream_in. producible wm (Watermark -` lset stream_in)) \<Longrightarrow>
   produce (join_op [] [] [] {} join) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  using produce_join_op_productive[of stream_in "{}" "[]" "[]" "[]" join stream_out]
  apply (simp add: maximal_complete_def)
  done


end