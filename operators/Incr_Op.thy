theory Incr_Op
  imports
    "../Watermarked_Stream"
    "../Llists_Processors"
    "../Sum_Order"
    "HOL-Library.Code_Lazy"
begin

section \<open>incr_op\<close> 

primcorec incr_op where
  "incr_op buf = Logic (\<lambda> ev.
     case ev of
       Data wm batch \<Rightarrow> let ts = rev (remdups (map fst (rev batch))) ;
                        out = map (\<lambda> t . Data t (buf@ batch)) ts in
                        (incr_op (buf @ batch), out)
     | Watermark wm \<Rightarrow>  (incr_op buf, [Watermark wm])
   ) LNil"

subsection \<open>Auxialiry\<close>
lemma produce_inner_incr_op_inversion:
  "produce_inner (incr_op buf, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs', lxs') \<Longrightarrow>
   \<exists> buf' n . lgc' = incr_op buf' \<and> lxs' = ldropn n lxs \<and> n > 0"
  apply (induct "(incr_op buf, lxs)" r arbitrary: buf lxs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs'a lgc'a buf 
    apply (auto split: event.splits)
    apply (metis ldropn_Suc_LCons zero_less_Suc)
    done
  subgoal for h buf
    apply (subst (asm) produce_inner.simps)
    apply (auto split: event.splits)
    apply (metis ldropn_0 ldropn_Suc_LCons lessI)+
    done
  apply auto
  done


lemma apply_incr_op_inversion:
  "apply (incr_op buf) h = (incr_op buf', x # xs) \<Longrightarrow>
  (\<exists> wm batch . h = Data wm batch \<and> (tmp ` set (x#xs) = fst ` set batch)) \<or> ( \<exists> wm . h = Watermark wm)"
  apply (simp split: event.splits)
  apply (elim conjE)
  subgoal premises p for t d
    using p(3,2,1) apply -
    apply (drule arg_cong[where f="\<lambda> x. tmp ` set x"])
    apply simp
    apply (subst (asm) img_tmp_Lambda_Data)
    apply blast
    apply simp
    done
  apply fast
  done

lemma apply_incr_op_out_preserves:
  "apply (incr_op buf) h = (op, x#xs) \<Longrightarrow>
   \<exists> wm batch. (h = Data wm batch \<and> op = (incr_op (buf @ batch)) \<and> (\<forall> e \<in> set (x#xs) . (\<exists> t d . e = Data t d \<and> t \<in> fst ` set batch))) \<or> (h = Watermark wm \<and> op = (incr_op buf) \<and> (xs = []))"
  apply (auto split: event.splits prod.splits list.splits if_splits)
  apply (metis list.set_intros(1) list.set_map rev.simps(2) set_remdups set_rev)
  apply (metis (no_types, lifting) UnI1 image_set set_append set_remdups set_rev)
  done

subsection \<open>Soundness\<close> 

lemma prefix_ltaken_Data:
  "n1 < n2 \<Longrightarrow>
   prefix (ltaken_Data n1 lxs) (ltaken_Data n2 lxs)"
  apply (induct n1 arbitrary: n2 lxs)
  apply auto
  subgoal for n1 n2 lxs
    apply (cases lxs)
    apply auto
    subgoal for x lxs'
      apply (cases x)
      apply auto
      using Suc_less_eq2 apply auto
      done
    done
  done


(* FIXME: move me *)
lemma ltaken_Data_lshift[simp]:
  "ltaken_Data n (xs @@- lxs) = ltaken_Data n (llist_of xs) @  ltaken_Data (n - length xs) lxs"
  apply (induct xs arbitrary: n lxs)
  apply auto
  subgoal for x xs n lxs
    apply (cases x; cases n)
    apply auto
    done
  done

lemma in_concat_map_ltaken_Data:
  "(\<exists> batch wm. t \<in> fst ` set batch \<and> (wm, batch) \<in> set (ltaken_Data n lxs)) \<longleftrightarrow> t \<in> fst ` (\<Union>a\<in>set (ltaken_Data n lxs). set (snd a))"
  apply (induct n arbitrary: lxs)
  apply auto
  apply (metis UN_iff fst_conv image_eqI snd_conv)
  apply (metis Domain.DomainI fst_eq_Domain)
  done


lemma produce_inner_skip_n_productions_op_incr_op_Inl:
  "produce_inner (skip_n_productions_op (incr_op buf) m, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   x = Data t data_coll \<Longrightarrow>
   \<exists> n. data_coll = buf @ concat (map snd (ltaken_Data n lxs)) \<and>
   t \<in> fst ` set (concat (map snd (ltaken_Data n lxs)))"
  apply (induct "(skip_n_productions_op (incr_op buf) m, lxs)" r arbitrary: buf lxs lgc' lxs' m x rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs buf m lgc'a lxs'' x
    apply (auto split: if_splits event.splits)
    subgoal for t' d
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply auto
      subgoal for n b aa batch
        apply (rule exI[of _ "Suc n"])
        apply auto
        apply (metis (no_types, lifting) Domain.DomainI UN_iff Un_iff fst_eq_Domain snd_conv)
        done
      done
    subgoal for wm
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply auto
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply auto
        apply (metis UN_iff fst_conv imageI snd_conv)
        done
      done
    subgoal for t' d
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply auto
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply auto
        apply (metis UN_iff UnCI fst_conv imageI snd_conv)
        done
      done
    subgoal for wm
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply auto
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply auto
        apply (metis UN_iff fst_conv imageI snd_conv)
        done
      done
    done
  subgoal for h x xsa lxs lxs' lgc' buf m lgc'' lxs'' x'
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits event.splits)
    subgoal for t d
      apply hypsubst_thin
      apply (rule exI[of _ 1])
      apply auto
      apply (metis (mono_tags, lifting) drop_map event.inject(1) list.set_intros(1) map_eq_set_D)
      apply (metis (mono_tags, lifting) event.inject(1) in_set_dropD list.set_intros(1) list.set_map map_eq_set_D set_remdups set_rev)
      done
    subgoal for wm
      apply hypsubst_thin
      apply (rule exI[of _ 1])
      apply simp
      apply (metis drop_Cons' drop_Nil event.distinct(1) list.distinct(1) list.inject)
      done
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_incr_op_Inl_Watermark:
  "produce_inner (skip_n_productions_op (incr_op buf) n, lxs) = Some r \<Longrightarrow>
   r = Inl (op, Watermark wm, xs, lxs') \<Longrightarrow>
   Watermark wm \<in> lset lxs \<and> xs = []"
  apply (induct "(skip_n_productions_op (incr_op buf) n, lxs)" r arbitrary: n buf lxs op lxs' rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: if_splits event.splits)
    apply (metis skip_n_productions_op_0)+
    done
  subgoal
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: drop_map map_eq_Cons_conv split: if_splits event.splits)
    apply (metis Suc_lessI drop0 drop_Suc_Cons event.inject(2) list.inject neq_Nil_conv zero_less_iff_neq_zero)
    apply (metis drop_Nil list.sel(3) tl_drop)
    done
  apply auto
  done


lemma produce_inner_skip_n_productions_op_incr_op_Inr:
  "produce_inner (skip_n_productions_op (incr_op buf) m, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   exit op = LNil"
  apply (induct "(skip_n_productions_op (incr_op buf) m, lxs)" r arbitrary: buf lxs op m rule: produce_inner_alt[consumes 1])
  apply (auto split: if_splits event.splits)
  apply (metis skip_n_productions_op_0)+
  done

lemma produce_inner_op_incr_op_Inr:
  "produce_inner (incr_op buf, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   exit op = LNil \<and> (\<forall> x \<in> lset lxs. is_Data x \<and> data x = [])"
  apply (induct "(incr_op buf, lxs)" r arbitrary: buf op lxs rule: produce_inner_alt[consumes 1])
  apply (auto split: if_splits event.splits)
  done

lemma produce_skip_n_productions_op_incr_op_soundness:
  "produce (skip_n_productions_op (incr_op buf) m) lxs = LCons (Data t data_coll) lxs' \<Longrightarrow>
   \<exists> n. data_coll = buf @ concat (map snd (ltaken_Data n lxs)) \<and>
   t \<in> fst ` set (concat (map snd (ltaken_Data n lxs)))"
  apply (subst (asm) produce.code)
  apply (simp split: option.splits event.splits prod.splits sum.splits)
  subgoal
    apply hypsubst_thin
    apply (drule produce_inner_skip_n_productions_op_incr_op_Inl)
    apply (rule refl)+
    apply auto
    done
  subgoal
    using produce_inner_skip_n_productions_op_incr_op_Inr apply force
    done
  done


lemma produce_incr_op_soundness_alt:
  "Data t data_coll \<in> lset (produce (incr_op buf) lxs) \<Longrightarrow>
   \<exists> n. data_coll = buf @ concat (map snd (ltaken_Data n lxs)) \<and> t \<in> fst ` set (concat (map snd (ltaken_Data n lxs)))"
  by (metis in_lset_conv_lnth ldropn_Suc_conv_ldropn produce_skip_n_productions_op_correctness produce_skip_n_productions_op_incr_op_soundness)

lemma produce_incr_op_soundness:
  "lnth (produce (incr_op buf) lxs) m = Data t data_coll \<Longrightarrow>
   m < llength (produce (incr_op buf) lxs) \<Longrightarrow>
   \<exists> n. data_coll = buf @ concat (map snd (ltaken_Data n lxs)) \<and>
   t \<in> fst ` set (concat (map snd (ltaken_Data n lxs)))"
  by (metis ldropn_Suc_conv_ldropn produce_skip_n_productions_op_incr_op_soundness produce_skip_n_productions_op_correctness)

subsection \<open>Completeness\<close> 
lemma produce_incr_op_completeness_Data:
  "lnth stream_in n = Data t batch \<Longrightarrow>
   n < llength stream_in \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   t' \<in> fst ` set batch \<Longrightarrow>
   ext = concat (map snd (ltaken_Data (Suc n) stream_in)) \<Longrightarrow>
   Data t' (buf @ ext) \<in> lset stream_out"
  apply (induct n arbitrary: stream_in buf stream_out ext)
  subgoal for buf
    apply (subst (asm) produce.code)
    apply (simp split: prod.splits option.splits sum.splits)
    apply (subst (asm) produce_inner.simps)
    apply (simp split: prod.splits llist.splits list.splits sum.splits)
    apply hypsubst_thin
    subgoal for x2 op x2a x x2b xs lxs'
      apply (subst (asm) produce_inner.simps)
      apply (simp split: prod.splits llist.splits list.splits)
      apply (metis (mono_tags, lifting) image_iff list.set_map set_ConsD set_remdups set_rev)
      done
    subgoal
      apply (frule produce_inner_op_incr_op_Inr)
      apply (rule refl)
      apply simp
      apply hypsubst_thin
      apply auto
      apply (metis empty_iff event.sel(3) in_lset_conv_lnth list.set(1))
      done
    done
  subgoal for n stream_in buf stream_out ext
    apply (cases stream_in)
    apply auto[1]
    subgoal for h stream_in'
      apply (cases h)
      subgoal for t d
        apply (drule meta_spec[of _ "stream_in'"])
        apply (drule meta_spec[of _ "buf@d"])
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply (metis Extended_Nat.eSuc_mono eSuc_enat llength_LCons)
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply assumption
        apply (drule meta_mp)
        apply simp
        apply simp
        apply hypsubst_thin
        apply (subst produce.code)
        apply (simp split: prod.splits option.splits)
        apply (rule conjI)
        apply (subst produce_inner.simps)
        apply (auto split: prod.splits llist.splits event.splits list.splits)[1]
        apply (metis empty_iff lset_LNil produce_inner_None_produce_LNil)
        apply (rule allI impI)+
        apply (auto split: prod.splits llist.splits event.splits list.splits sum.splits)[1]
        apply (frule produce_inner_op_incr_op_Inr)
        apply (rule refl)
        apply auto
        apply (simp add: produce.code)
        done
      subgoal for wm
        apply (drule meta_spec[of _ "stream_in'"])
        apply (drule meta_spec[of _ "buf"])
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply (metis Extended_Nat.eSuc_mono eSuc_enat llength_LCons)
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply assumption
        apply (drule meta_mp)
        apply simp
        apply simp
        apply hypsubst_thin
        apply (subst produce.code)
        apply (simp split: prod.splits option.splits)
        apply (rule conjI)
        apply (auto split: prod.splits llist.splits event.splits list.splits sum.splits)[1]
        apply (metis llist.set_cases llist.simps(3) option.exhaust produce_inner_None_produce_LNil)
        apply (rule allI impI)+
        subgoal for s
          apply (cases s)
           apply auto
        apply (simp add: produce.code)
        done
      done
    done
  done
  done

lemma produce_incr_op_completeness_Watermark:
  "x \<in> lset stream_in \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   Watermark wm \<in> lset stream_out"
  apply (induct stream_in arbitrary: buf stream_out wm rule: lset_induct)
  subgoal for xs buf stream_out wm
    apply simp
    apply hypsubst_thin
    apply (subst produce.code)
    apply (auto split: option.splits sum.splits)  
    done
  subgoal for x' lxs buf stream_out wm
    apply (cases x')
    subgoal for t d
      apply simp
      apply hypsubst_thin
      apply (subst produce.code)
      apply (simp split: option.splits)
      apply (rule conjI)
      subgoal
        apply (drule meta_spec[of _ "buf@d"])
        apply (rule impI)
        apply (subst (asm) produce.code)
        apply (auto split: event.splits list.splits option.splits sum.splits llist.splits)
        done
      subgoal
        apply (drule meta_spec[of _ "buf@d"])
        apply (subst (asm) produce.code)
        apply (auto split: event.splits list.splits option.splits sum.splits llist.splits)
        done
      done
    subgoal for wm'
      apply simp
      apply hypsubst_thin
      apply (subst produce.code)
      apply (simp split: option.splits)
      apply (rule conjI)
      subgoal
        apply (drule meta_spec[of _ "buf"])
        apply (subst (asm) produce.code)
        apply (auto split: event.splits list.splits option.splits sum.splits llist.splits)
        done
      subgoal
        apply (drule meta_spec[of _ "buf"])
        apply (subst (asm) produce.code)
        apply (auto split: event.splits list.splits option.splits sum.splits llist.splits)
        done
      done
    done
  done

lemma produce_incr_op_completeness:
  "\<exists> wm batch . Data wm batch \<in> lset lxs \<and> t \<in> fst ` set batch \<Longrightarrow>
   \<exists>batch. Data t batch \<in> lset (produce (incr_op buf) lxs)"
  apply (elim exE conjE)
  subgoal for wm batch
    apply (subst (asm) lset_conv_lnth)
    apply auto
    subgoal for b n
      using produce_incr_op_completeness_Data[where n=n and stream_in=lxs and t=wm and t'=t and batch=batch and buf=buf] apply simp
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply force
      apply (drule meta_mp)
      apply (rule refl)
      apply fast
      done
    done
  done

lemma produce_incr_op_completeness_Data_alt:
  "x \<in> lset stream_in \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   t' \<in> fst ` set batch \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   \<exists> batch. Data t' batch \<in> lset stream_out"
  apply (induct stream_in arbitrary: buf stream_out wm rule: lset_induct)
  subgoal for xs buf stream_out wm
    apply simp
    apply hypsubst_thin
    apply (subst produce.code)
    apply (auto split: option.splits sum.splits)  
    done
  subgoal for x' lxs buf stream_out wm
    apply (cases x')
    subgoal for t d
      apply simp
      apply hypsubst_thin
      apply (subst produce.code)
      apply (simp split: option.splits)
      apply (rule conjI)
      subgoal
        apply (drule meta_spec[of _ "buf@d"])
        apply (rule impI)
        apply (subst (asm) produce.code)
        apply (auto split: event.splits list.splits option.splits sum.splits llist.splits)
        done
      subgoal
        apply (drule meta_spec[of _ "buf@d"])
        apply (subst (asm) produce.code)
        apply (auto split: event.splits list.splits option.splits sum.splits llist.splits)
        done
      done
    subgoal
      apply auto
      done
    done
  done

lemma produce_incr_op_completeness_alt:
  "Data wm batch \<in> lset lxs \<and> t \<in> fst ` set batch \<Longrightarrow>
   \<exists>batch. Data t batch \<in> lset (produce (incr_op buf) lxs)"
  apply (elim conjE)
  apply (drule produce_incr_op_completeness_Data_alt[where buf=buf])
  apply simp_all
  done


subsection \<open>Strict monotone\<close>
lemma all_Data_strict_monotone_aux:
  "y \<in> lset lxs \<Longrightarrow> \<forall> x \<in> lset lxs . is_Data x \<and> (\<forall> wm \<in> WM . \<not> wm \<ge> tmp x) \<Longrightarrow> monotone lxs WM"
  apply (coinduction arbitrary: y lxs rule: monotone.coinduct)
  subgoal for y lxs
    apply (cases lxs)
    apply simp
    subgoal for x lxs'
      apply (cases x)
      apply simp_all
      apply (metis lset_intros(1) neq_LNil_conv monotone.LNil)
      done
    done
  done

lemma all_Data_strict_monotone:
  "\<forall> x \<in> lset lxs . is_Data x \<and> (\<forall> wm \<in> WM . \<not> wm \<ge> tmp x) \<Longrightarrow> monotone lxs WM"
  apply (cases lxs)
  using monotone.LNil apply blast
  apply (metis all_Data_strict_monotone_aux lset_intros(1))
  done


(* FIXME: move me *)
lemma monotone_llist_of:
  "(\<forall> x \<in> set xs. is_Data x \<and> (\<forall> wm \<in> WM. \<not> tmp x \<le> wm)) \<Longrightarrow>
   monotone (llist_of xs) WM"
  apply (induct xs arbitrary: WM)
  apply (auto 2 1 simp add: monotone.LNil)
  subgoal for x xs WM
    apply (cases x)
    apply auto
    apply (rule LConsL)
    apply blast
    apply simp
    done
  done



lemma produce_inner_incr_op_monotone_Inl_1:
  "produce_inner (incr_op buf, stream_in) = Some r \<Longrightarrow>
   r = Inl (op, Data t d, xs, lxs) \<Longrightarrow>
   \<forall>n. enat n < llength stream_in \<longrightarrow>
        (\<forall>wm batch.
            lnth stream_in n = Data wm batch \<longrightarrow>
            (\<forall>t'. t' \<in> fst ` set batch \<longrightarrow> t' \<le> wm \<and> (\<forall>wm'\<in>WM \<union> Watermark -` lset (ltake (enat n) stream_in). \<not> t' \<le> wm'))) \<Longrightarrow>
   monotone stream_in WM \<Longrightarrow>
   (\<forall>wm\<in>WM. \<not> t \<le> wm) \<and> 
   wms xs = {} \<and>
   monotone lxs WM \<and>
   (\<exists> n. lxs = ldropn (Suc n) stream_in) \<and>
   (\<exists> buf. op = incr_op buf) \<and>
   monotone (llist_of xs) WM"
  apply (induct "(incr_op buf, stream_in)" r arbitrary: WM buf op lxs stream_in t d xs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs buf WM op lxsa t d xs
    apply (simp split: event.splits llist.splits sum.splits if_splits)
    subgoal for wm' 
      apply hypsubst_thin
      apply (drule meta_spec[of _ buf])
      apply (drule meta_spec[of _ WM])
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      subgoal
        apply auto
        apply (metis Domain.DomainI eSuc_enat fst_eq_Domain ileI1 lnth_Suc_LCons)
        apply (metis Domain.DomainI Un_iff eSuc_enat fst_eq_Domain ileI1 lnth_Suc_LCons)
        subgoal for n
          apply (drule spec[of _ "Suc n"])
          apply auto
          using Suc_ile_eq apply blast
          done
        done
      apply (drule meta_mp)
      apply fast
      apply auto
      done
    done
  subgoal
    apply (subst (asm) produce_inner.simps)
    apply (auto split: event.splits llist.splits sum.splits if_splits)
    apply (metis (no_types, opaque_lifting) Un_iff list.set_intros(1) list.set_map lnth_0 rev.simps(2) set_remdups set_rev zero_enat_def zero_le)
    subgoal
      by (metis ldropn_0)
    subgoal for t' d' xs
      apply hypsubst_thin
      apply (drule spec[of _ 0])
      using zero_enat_def apply auto
      apply (rule monotone_llist_of)
      apply auto
      apply (metis UnI1 image_set set_append set_remdups set_rev)
      done
    done
  apply auto
  done


lemma produce_inner_incr_op_monotone_Inl_2:
  "produce_inner (incr_op buf, stream_in) = Some r \<Longrightarrow>
   r = Inl (op, Watermark wm, xs, lxs) \<Longrightarrow>
   monotone stream_in WM \<Longrightarrow>
   monotone lxs (insert wm WM) \<and>
   (\<exists> n. lxs = ldropn (Suc n) stream_in \<and> (\<forall> x \<in> lset (ltake n stream_in). is_Data x \<and> data x = []) \<and> n < llength stream_in \<and> lnth stream_in n = Watermark wm) \<and>
   (\<exists> buf. op = incr_op buf) \<and>
   xs = []"
  apply (induct "(incr_op buf, stream_in)" r arbitrary: WM buf op lxs stream_in wm xs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs buf WM op lxsa wm xs
    apply (auto split: event.splits llist.splits sum.splits if_splits; hypsubst_thin)
      apply blast
    apply (smt (verit) eSuc_enat event.disc(1) event.sel(3) ileI1 llist.inject llist.set_cases lnth_Suc_LCons ltake_enat_Suc strict_monotone_drop_head)
    apply fastforce
    done
  subgoal
    apply (subst (asm) produce_inner.simps)
    apply (auto split: event.splits llist.splits sum.splits if_splits; hypsubst_thin)
    apply (metis empty_iff enat_0 i0_lb ldropn_0 lnth_0 lset_LNil ltake_0)
    done
  apply auto
  done

lemma produce_incr_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   (\<forall> n wm batch. n < llength stream_in \<longrightarrow> lnth stream_in n = Data wm batch \<longrightarrow> 
    (\<forall> t'\<in> fst ` set batch . t' \<le> wm \<and> (\<forall> wm' \<in> (WM \<union> (Watermark -` lset (ltake n stream_in))) . \<not> wm' \<ge> t'))) \<Longrightarrow>
   monotone stream_out WM"
  apply (coinduction arbitrary: stream_in WM stream_out buf rule: strict_monotone_coinduct_strict_monotone_prepend_cong1)
  subgoal for stream_in WM stream_out buf
    apply (subst (asm) produce.corec.code)
    apply (simp split: option.splits prod.splits sum.splits)
    apply hypsubst_thin
    subgoal for x2 x1 op x2a x x2b xs lxs
      apply (cases x)
      subgoal for t d
        apply hypsubst_thin
        apply simp
        apply (drule produce_inner_incr_op_monotone_Inl_1)
        apply (rule refl)
        apply assumption+
        apply simp
        apply (rule disjI1)
        apply (rule monotone_prepend_cong_prepend)
        apply (rule monotone_prepend_cong_base)
        apply (rule exI[of _ lxs])
        apply (intro conjI)
        apply auto[1]
        apply auto[1]
        subgoal
          apply (elim conjE)
          apply auto
          apply (metis fst_conv imageI in_lset_conv_lnth in_lset_ldropnD llength_ldropn)
          subgoal
            by (metis (no_types, opaque_lifting) Domain.DomainI Un_iff fst_eq_Domain in_lset_conv_lnth in_lset_ldropnD llength_ldropn)
          subgoal for n buf n' wm batch a b wm'
            apply hypsubst_thin
            apply (cases stream_in)
            apply auto
            apply (subst (asm) lnth_ldropn)
            apply (metis add.commute ldropn_Suc_LCons ldropn_eq_LNil ldropn_ldropn leD leI llength_LCons llength_ldropn)
            apply (drule spec[of _ "n + n' + 1"])
            apply auto
            apply (metis add.commute eSuc_enat eSuc_minus_eSuc eq_LConsD ileI1 ldropn_Suc_conv_ldropn ldropn_eq_LNil ldropn_ldropn leI llength_ldropn)
            apply (smt (verit, del_insts) Un_iff add.commute fst_conv imageI in_lset_ldropnD insertCI ltake_ldropn plus_enat_simps(1) vimage_eq)
            done
          done
        subgoal
          using Suc_ile_eq by fastforce
        done
      subgoal for wm
        apply hypsubst_thin
        apply simp
        apply (drule produce_inner_incr_op_monotone_Inl_2)
        apply (rule refl)
        apply assumption+
        apply (elim conjE exE)
        apply (rule disjI1)
        apply (rule monotone_prepend_cong_prepend)
        apply (rule monotone_prepend_cong_base)
        apply (rule exI[of _ lxs])
        apply (intro conjI)
        subgoal 
          by fastforce
        subgoal 
          by auto
        subgoal for n buf
          apply (intro allI impI)
          apply hypsubst_thin
          apply (subst (asm) lnth_ldropn)
          apply (metis add.commute ldropn_eq_LNil ldropn_ldropn linorder_not_le)
          apply (subst (asm) llength_ldropn)
          subgoal for n' wm' batch t'
            apply (drule spec[of _ "n + n' + 1"])
            apply (drule mp)
            apply (metis add.commute ldropn_eq_LNil ldropn_ldropn leD leI llength_ldropn plus_1_eq_Suc)
            apply simp
            apply (drule spec[of _ wm'])
            apply (drule spec[of _ batch])
            apply (drule mp)
            apply (simp add: add.commute)
            apply (drule spec[of _ t'])
            apply simp
            apply (rule conjI)
            defer
            apply (smt (verit, ccfv_threshold) Un_iff add.commute add_Suc_right in_lset_ldropnD ltake_ldropn plus_enat_simps(1) vimage_eq)
            apply (elim conjE)
            apply (drule bspec[of _ _ wm])
            subgoal
              apply auto
              by (metis (no_types, lifting) enat_ord_simps(2) in_lset_conv_lnth less_add_Suc1 llength_ltake lnth_ltake min_def)
            apply simp
            done
          done
        apply auto
        apply (meson monotone.LNil)
        done
      done
    subgoal for op op' 
      apply (drule produce_inner_op_incr_op_Inr)
      apply (rule refl)
      apply auto
      done
    done
  done

subsection \<open>Productive\<close> 
lemma produce_inner_incr_op_lnull:
  "(\<forall> t batch . Data t batch \<in> lset lxs \<longrightarrow> batch \<noteq> []) \<Longrightarrow>
   lnull lxs \<Longrightarrow> produce_inner (incr_op buf, lxs) \<noteq> None"
  apply (subst produce_inner.simps)
  apply (auto split: prod.splits if_splits list.splits llist.splits event.splits)
  done

lemma produce_inner_incr_op_Inl_1:
  "produce_inner (incr_op buf, stream_in) = Some r \<Longrightarrow>
   r = Inl (op, Data t d, xs, lxs) \<Longrightarrow>
   (\<forall> n wm batch. n < llength stream_in \<longrightarrow> lnth stream_in n = Data wm batch \<longrightarrow>
   (\<exists> m > n. m < llength stream_in \<and> lnth stream_in m = Watermark wm) \<and> (\<forall> t'\<in> fst ` set batch . t' \<le> wm) \<and> batch \<noteq> []) \<Longrightarrow>
   (\<exists> wm. Watermark wm \<in> lset lxs \<and> t \<le> wm \<and> (\<forall> x \<in> set xs. is_Data x \<and> (\<exists> wm. Watermark wm \<in> lset lxs \<and> tmp x \<le> wm)))"
  apply (induct "(incr_op buf, stream_in)" r arbitrary: buf op lxs stream_in t d xs rule: produce_inner_alt[consumes 1])
  subgoal
    apply (simp split: event.splits)
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (metis lnth_0 zero_enat_def zero_le)
      apply auto
      done
    done
  subgoal for h x xs lxs lxs' lgc' buf op lxs'' t d xs'
    apply (subst (asm) produce_inner.simps)
    apply (simp split: event.splits)
    apply (elim conjE exE)
    apply hypsubst_thin
    subgoal for x xs''
      apply (drule spec[of _ 0])
      apply (drule mp)
      apply (simp add: enat_0)
      apply auto
      subgoal for zs m
        apply (rule exI[of _ x])
        apply auto
        subgoal 
          by (metis One_nat_def Suc_ile_eq Suc_pred in_lset_conv_lnth lnth_LCons' not_gr_zero)
        apply (metis (no_types, lifting) list.set_intros(1) map_eq_set_D rev.simps(2) set_remdups set_rev)
        by (metis (no_types, lifting) \<open>\<lbrakk>remdups (map fst (rev xs'')) = rev zs @ [t]; \<forall>t'\<in>set xs''. fst t' \<le> x; xs'' \<noteq> []; 0 < m; xs' = map (\<lambda>t. Data t (buf @ xs'')) zs; enat m \<le> llength lxs''; lnth (LCons (Data x xs'') lxs'') m = Watermark x; d = buf @ xs''\<rbrakk> \<Longrightarrow> Watermark x \<in> lset lxs''\<close> list.set_intros(2) map_eq_set_D rev.simps(2) set_remdups set_rev)
      done
    done
  apply auto
  done

lemma produce_inner_incr_op_Inl_2:
  "produce_inner (incr_op buf, stream_in) = Some r \<Longrightarrow>
   r = Inl (op, Watermark wm, xs, lxs) \<Longrightarrow>
   xs = []"
  apply (induct "(incr_op buf, stream_in)" r arbitrary: buf op lxs stream_in t d xs rule: produce_inner_alt[consumes 1])
  apply (auto split: event.splits)
  done


lemma produce_incr_op_productive:
  "productive stream_in \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   (\<forall> n wm batch. n < llength stream_in \<longrightarrow> lnth stream_in n = Data wm batch \<longrightarrow>
   (\<exists> m > n. m < llength stream_in \<and> lnth stream_in m = Watermark wm) \<and> (\<forall> t'\<in> fst ` set batch . t' \<le> wm) \<and> batch \<noteq> []) \<Longrightarrow>
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
      subgoal for t d
        apply simp
        apply (frule produce_inner_incr_op_inversion)
        apply (rule refl)
        apply(elim exE conjE)
        apply hypsubst_thin
        apply (frule produce_inner_incr_op_Inl_1)
        apply (rule refl)
        apply simp
        apply(elim exE conjE)
        apply (rule conjI)
        subgoal
          apply (meson Un_iff produce_incr_op_completeness_Watermark vimage_eq)
          done
        subgoal for buf' n wm
          apply (rule disjI1)
          apply (rule productive_prepend_cong1_prepend_1)
          apply (rule productive_prepend_cong1_base)
          subgoal 
            apply (rule exI[of _ "ldropn n stream_in"])
            apply (intro conjI)
            apply (metis ldrop_enat productive_ldrop)
            apply (rule exI[of _ "buf'"])
            apply simp
            apply (intro impI allI)
            apply (subst (asm) lnth_ldropn)
            apply (metis add.commute ldropn_eq_LNil ldropn_ldropn leD leI)
            subgoal for n'
              apply (drule spec[of _ "n' + n"])
              apply (drule mp)
              apply (metis ldropn_eq_LNil ldropn_ldropn leD leI)
              apply simp
              apply (elim conjE exE)
              subgoal for m
                apply (rule exI[of _ "m - n"])
                apply auto
                apply (smt (verit) antisym_conv2 ldropn_eq_LNil ldropn_ldropn leD leI le_add_diff_inverse2 less_diff_conv llength_ldropn not_add_less2 order_less_imp_le)
                done
              done
            done
          subgoal
            apply auto
            by (metis event.sel(1) nth_mem produce_incr_op_completeness_Watermark)
          done
        done
      subgoal for wm
        apply simp
        apply (frule produce_inner_incr_op_inversion)
        apply (rule refl)
        apply(elim exE conjE)
        apply hypsubst_thin
        apply (frule produce_inner_incr_op_Inl_2)
        apply (rule refl)
        apply (rule disjI1)
        apply (rule productive_prepend_cong1_prepend_1)
        apply (rule productive_prepend_cong1_base)
        subgoal for buf n'
          apply (rule exI[of _ " (ldropn n' stream_in)"])
          apply (intro conjI)
          apply (metis ldrop_enat productive_ldrop)
          apply (rule exI[of _ buf])
          apply simp
          apply (intro impI allI)
          apply (subst (asm) lnth_ldropn)
          apply (metis add.commute ldropn_eq_LNil ldropn_ldropn leD leI)
          subgoal for n''
            apply (drule spec[of _ "n'' + n'"])
            apply (drule mp)
            apply (metis ldropn_eq_LNil ldropn_ldropn verit_comp_simplify1(3))
            apply simp
            apply (smt (verit) add.commute diff_is_0_eq' ldropn_eq_LNil ldropn_ldropn leD leI le_add_diff_inverse less_diff_conv llength_ldropn lnth_ldropn order_less_imp_le)
            done
          done
        subgoal 
          apply auto
          done
        done
      done
    subgoal for op op'
      by (simp add: produce_inner_op_incr_op_Inr)
    done
  done

lemma finite_produce_incr_op_exit_LNil:
  "finite_produce (incr_op buf) xs = (op', out) \<Longrightarrow> exit op' = LNil"
  apply (induct xs arbitrary: buf op' out)
  apply (auto split: list.splits event.splits prod.splits)
  done


lemma skip_n_productions_op_incr_op_Watermark_soundness:
  "Watermark wm \<in> lset lys \<Longrightarrow>
   produce (skip_n_productions_op (incr_op buf) n) lxs = lys \<Longrightarrow>
   Watermark wm \<in> lset lxs"
  apply (induct lys arbitrary: n buf rule: lset_induct)
  subgoal for lxs buf
    apply (subst (asm) produce.code)
    apply (auto split: option.splits sum.splits)
    subgoal for op xs lxs'
      apply hypsubst_thin
      using produce_inner_skip_n_productions_op_incr_op_Inl_Watermark
      by blast
    subgoal
      by (simp add: produce_inner_skip_n_productions_op_incr_op_Inr)
    done
  subgoal
    by (meson produce_skip_n_productions_op_LCons)
  done

lemma produce_incr_op_Watermark_lset:
  "Watermark -` lset (produce (incr_op buf) lxs) = Watermark -` lset lxs"
  apply auto
  subgoal for wm
    using skip_n_productions_op_incr_op_Watermark_soundness[where n=0, simplified]
    apply auto
    done
  subgoal
    using produce_incr_op_completeness_Watermark by blast
  done

lemma incr_op_prefix_cases:
  "Data t1 batch1 \<in> lset (produce (incr_op buf) lxs) \<Longrightarrow>
   Data t2 batch2 \<in> lset (produce (incr_op buf) lxs) \<Longrightarrow>
   prefix batch1 batch2 \<or> prefix batch2 batch1"
  apply (simp add: in_lset_conv_lnth)
  apply (elim exE conjE)
  subgoal for n1 n2
        using produce_incr_op_soundness[of buf lxs n1 t1 batch1] apply simp
        using produce_incr_op_soundness[of buf lxs n2 t2 batch2] apply simp
        apply (elim exE conjE)
        subgoal for m1 m2
          apply hypsubst_thin
          apply auto
        apply (rule prefix_concat)
          apply (rule map_mono_prefix)
          apply (cases "m1 < m2")
          apply (meson prefix_ltaken_Data)
          apply (cases "m1 = m2")
          apply fastforce
          apply (subgoal_tac "m2 < m1")
          defer
           apply simp
          using map_mono_prefix prefix_concat prefix_ltaken_Data apply blast
          done
        done
      done


end