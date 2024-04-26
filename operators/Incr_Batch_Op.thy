theory Incr_Batch_Op
  imports
    "Incr_Op"
    "Batch_Op"
begin

section \<open>incr_batch_op\<close> 

definition "incr_batch_op buf1 buf2 = compose_op (batch_op buf1) (incr_op buf2)"

lemma produce_inner_batch_op_produces_some:
  "(enat m < llength lxs \<and> m < n \<and> lnth lxs m = Data t d) \<or> (t, d) \<in> set buf \<Longrightarrow>
   enat n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   \<exists>y. produce_inner_induct (batch_op buf, lxs) = Some y"
  apply (induct n arbitrary: m buf lxs)
  subgoal for m buf lxs
    apply (cases lxs)
    apply auto
    done
  subgoal for n m buf lxs
    apply (cases m)
    subgoal
      apply (cases lxs)
      apply auto[1]
      apply (subst produce_inner_induct.simps)
      apply (auto split: event.splits llist.splits)
      subgoal
        apply (drule meta_spec[of _ "n - 1"])
        apply (drule meta_spec[of _ "buf @ [(t, d)]"])
        apply (drule meta_spec[of _ "ltl lxs"])
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply (simp add: Suc_ile_eq)
        apply (drule meta_mp)
        apply simp
        apply auto
        done
      apply (simp add: Suc_ile_eq)
      done
    subgoal for n'
      apply (cases lxs)
      apply auto[1]
      apply (subst produce_inner_induct.simps)
      apply (auto split: event.splits llist.splits)
      using Suc_ile_eq apply auto
      done
    done
  done

lemma productive_produce_inner_produces_some:
  "productive stream_in \<Longrightarrow> \<exists>y. produce_inner_induct (batch_op buf, stream_in) = Some y"
  apply (subst (asm) productive_alt)
  apply (erule productive'.cases)
  subgoal
    using produce_inner_None_not_lfinite_aux by auto
  subgoal for lxs t d
    apply hypsubst_thin
    apply (elim bexE)
    subgoal for wm
      apply (subgoal_tac "\<exists> n. lnth lxs n = Watermark wm \<and> n < llength lxs")
      defer
      apply (meson in_lset_conv_lnth vimageE)
      apply (elim exE conjE)
      subgoal for n
        using produce_inner_batch_op_produces_some[where n="Suc n" and buf=buf and wm=wm and m=0 and lxs="LCons (Data t d) lxs" and t=t and d=d]
        apply auto
        apply (drule meta_mp)
        using i0_lb zero_enat_def apply presburger
        apply (drule meta_mp)
        using Suc_ile_eq apply blast
        apply auto
        done
      done
    done
  subgoal
    apply (subst produce_inner_induct.simps)
    apply auto
    done
  done

lemma llength_produce_batch_op_productive_lfinite:
  "llength (produce (batch_op buf) stream_in) \<le> enat n \<Longrightarrow> productive stream_in \<Longrightarrow> lfinite stream_in"
  apply (induct n arbitrary: buf stream_in)
  subgoal 
    apply (subst (asm)  produce.code)
    apply (auto split: option.splits sum.splits)
    apply (metis option.distinct(1) productive_produce_inner_produces_some)
    using zero_enat_def apply fastforce
    using produce_inner_Some_Inr_lfinite apply blast
    done
  subgoal for n buf stream_in
    apply (subst (asm) (2) produce.code)
    apply (auto split: option.splits sum.splits)
    apply (metis llength_LNil produce_inner_None_produce_LNil zero_le)
    subgoal for op x xs lxs
      apply (cases x)
      apply (frule produce_inner_batch_op_inversion)
      apply (rule refl)
      subgoal for t d
        apply (frule produce_inner_skip_n_productions_op_batch_op_xs[where n=0, simplified])
        apply (rule refl)
        apply simp
        apply (elim exE conjE)
        apply hypsubst_thin
        apply (metis (no_types, lifting) antisym_conv2 eSuc_enat enat_ile ile_eSuc iless_Suc_eq lfinite_ldropn llength_LCons lshift_simps(1) lshift_simps(2) produce_inner_Some_produce produce_inner_batch_op_Inl_productive_1)
        done
      subgoal for wm
        apply hypsubst_thin
        apply (frule produce_inner_batch_op_Inl_productive_2)
        apply assumption
        apply (rule refl)
        apply auto
        apply (metis (no_types, lifting) eSuc_enat eSuc_inject eSuc_le_iff lfinite_ldropn produce_inner_batch_op_inversion)
        done
      done
    subgoal for op
      using produce_inner_Some_Inr_lfinite apply blast
      done
    done
  done

lemma productive_not_lfinite_produce_batch_op_aux:
  "lfinite lxs \<Longrightarrow>
   lxs = produce (skip_n_productions_op (batch_op buf) n) stream_in \<Longrightarrow>
   productive stream_in \<Longrightarrow>
   lfinite stream_in"
  apply (induct lxs arbitrary: buf stream_in n rule: lfinite_induct)
  subgoal for lxs buf stream_in n
    apply auto
    apply hypsubst_thin
    apply (subst (asm) produce_skip_n_productions_op_correctness)
    apply auto
    apply (subst (asm) productive_alt)
    apply (erule productive'.cases)
    apply auto[1]
    subgoal for lxs t d
      apply hypsubst_thin
      using llength_produce_batch_op_productive_lfinite 
      by (metis productive_alt productive_intros(2))
    subgoal for lxs t 
      apply hypsubst_thin
      using llength_produce_batch_op_productive_lfinite 
      using productive'_productive productive_intros(3) by blast
    done
  subgoal for lxs buf stream_in n
    apply hypsubst_thin
    by (metis lhd_LCons_ltl produce_skip_n_productions_op_LCons)
  done

lemma productive_not_lfinite_produce_batch_op:
  "productive stream_in \<Longrightarrow>
   \<not> lfinite stream_in \<Longrightarrow>
   \<not> lfinite (produce (batch_op buf) stream_in)"
  using productive_not_lfinite_produce_batch_op_aux
  by (metis skip_n_productions_op_0)

lemma produce_skip_n_productions_op_batch_op_produce_inner:
  "\<exists> x lxs. produce (skip_n_productions_op (batch_op buf) n) stream_in = LCons x lxs \<Longrightarrow>
   \<exists>y. produce_inner_induct (skip_n_productions_op (batch_op buf) n, stream_in) = Some y"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits sum.splits)
  done

lemma batch_op_always_productive:
  "productive stream_in \<Longrightarrow>
   \<forall>n. produce_inner_induct (skip_n_productions_op (batch_op buf) n, stream_in) \<noteq> None"
  apply safe
  subgoal for n
    apply (subst (asm) productive_alt)
    apply (erule productive'.cases)
    using produce_inner_None_not_lfinite_aux apply auto[1]
    subgoal for lxs t d
      apply (rule produce_skip_n_productions_op_batch_op_produce_inner)
      apply (subst produce_skip_n_productions_op_correctness)
      using productive_not_lfinite_produce_batch_op
      apply (metis lfinite_code(1) lfinite_code(2) lfinite_ldropn neq_LNil_conv productive'.intros(2) productive_alt)
      done
    subgoal for lxs wm
      apply (rule produce_skip_n_productions_op_batch_op_produce_inner)
      apply (subst produce_skip_n_productions_op_correctness)
      using productive_not_lfinite_produce_batch_op
      by (metis ldropn_Suc_conv_ldropn ldropn_eq_LNil lfinite.simps lfinite_code(2) lfinite_ldropn linorder_not_less productive'.intros(3) productive_alt)
    done
  done

subsection \<open>Strict Monotone\<close> 
lemma produce_compose_op_batch_op_incr_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (compose_op (batch_op buf1) (incr_op buf2)) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  apply (subst (asm) produce_compose_op_correctness_alt)
  subgoal 
    using finite_produce_incr_op_exit_LNil apply blast
    done
  apply (rule produce_incr_op_strict_monotone[where stream_in="produce (batch_op buf1) stream_in"])
  apply (rule produce_batch_op_strict_monotone[where buf=buf1])
  apply assumption
  apply force
  apply simp
  apply assumption
  apply hypsubst_thin
  apply (rule allI)+
  apply (rule impI)+
  apply (rule ballI)+
  subgoal for n wm batch t'
    apply (subgoal_tac "Data wm batch \<in> lset (produce (batch_op buf1) stream_in)")
    defer
    apply (metis in_lset_conv_lnth)
    apply (drule produce_batch_op_soundness)
    apply assumption+
    apply (intro conjI)
    subgoal
      apply fastforce
      done
    subgoal
      apply (elim conjE)
      subgoal 
        using lnth_produce_skip_n_productions_op_batch_op_batch_not_ge[where i=0 and buf=buf1 and n="n" and lxs=stream_in and WM=WM and batch=batch and t=wm, OF refl] apply auto
        apply (smt (z3) Data_set_strict_monotone_not_GE case_prod_unfold image_iff prod.collapse)
        apply (smt (verit) enat_ord_simps(2) in_lset_conv_lnth llength_ltake lnth_ltake min_def order_less_imp_le)
        done
      done
    done
  done

lemma produce_incr_batch_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (incr_batch_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  unfolding incr_batch_op_def
  using produce_compose_op_batch_op_incr_op_strict_monotone by blast

(* FIXME: move me *)
lemma batch_op_preservers_finiteness:
  "lfinite stream_in \<Longrightarrow>
   lfinite (produce (batch_op buf) stream_in)"
  apply (induct stream_in arbitrary: buf rule: lfinite_induct)
  subgoal for lxs
    apply (cases lxs)
    apply auto
    done
  subgoal for lxs buf
    apply (cases lxs)
    apply (auto split: option.splits sum.splits event.splits)
    done
  done

(* FIXME: move me *)
lemma incr_op_preservers_finiteness:
  "lfinite stream_in \<Longrightarrow>
   lfinite (produce (incr_op buf) stream_in)"
  apply (induct stream_in arbitrary: buf rule: lfinite_induct)
  subgoal for lxs
    apply (cases lxs)
    apply auto
    done
  subgoal for lxs buf
    apply (cases lxs)
    apply (auto split: option.splits sum.splits event.splits)
    done
  done

(* FIXME: move me *)
lemma produce_inner_batch_op_batch:
  "produce_inner_induct (batch_op buf1, stream_in) = Some (Inl (op, x, xs, lxs')) \<Longrightarrow>
   Data wm batch = x  \<Longrightarrow>
   batch \<noteq> [] \<and> (\<forall>t'\<in>set batch. fst t' \<le> wm) \<and> xs = [Watermark wm] \<and> Watermark wm \<in> lset stream_in"
  by (metis produce_inner_skip_n_productions_op_batch_op_Inl_soundness_no_monotone produce_inner_skip_n_productions_op_batch_op_xs skip_n_productions_op_0)


lemma produce_skip_n_productions_op_batch_op_soundness_no_monotone:
  "x \<in> lset lys \<Longrightarrow> 
   x = Data wm batch \<Longrightarrow>
   lys = produce (skip_n_productions_op (batch_op buf1) n) stream_in \<Longrightarrow>
   batch \<noteq> [] \<and> (\<forall>t'\<in>fst ` set batch. t' \<le> wm)"
  apply (induct lys arbitrary: n rule: lset_induct)
  subgoal
    apply (subst (asm) produce.code)
    apply (simp split: prod.splits option.splits sum.splits)
    apply hypsubst_thin
    subgoal for x2 x1 op x2a x x2b xs
      apply (drule produce_inner_skip_n_productions_op_batch_op_Inl_soundness_no_monotone)
      apply auto                                  
      done
    subgoal for xs' op
      apply hypsubst_thin
      using produce_inner_skip_n_productions_op_batch_op_Inr_soundness_no_monotone 
      by metis
    done
  subgoal for x xs
    apply hypsubst_thin
    by (metis produce_skip_n_productions_op_LCons)
  done

subsection \<open>Productive\<close> 
lemma produce_compose_op_batch_op_incr_op_productive:
  "productive stream_in \<Longrightarrow>
   produce (compose_op (batch_op buf1) (incr_op buf2)) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  apply (subst (asm) produce_compose_op_correctness_alt)
  subgoal 
    using finite_produce_incr_op_exit_LNil by blast
  apply (cases "lfinite stream_in")
  subgoal
    apply (subgoal_tac "lfinite stream_out")
    using productive_intros(1) apply blast
    using incr_op_preservers_finiteness batch_op_preservers_finiteness apply blast
    done
  subgoal
    apply (rule produce_incr_op_productive[where stream_in="produce (batch_op buf1) stream_in"])
    using produce_batch_op_productive apply blast
    apply simp
    apply (intro allI impI conjI)
    subgoal for n wm batch
      using produce_skip_n_productions_op_batch_op_n_Data_Suc_n_Watermark
      apply (metis leI lessI llength_produce_batch_op_productive_lfinite skip_n_productions_op_0)
      done
    subgoal for n wm batch
      apply (subgoal_tac "Data wm batch \<in> lset (produce (batch_op buf1) stream_in)")
      defer
      apply (metis in_lset_conv_lnth)
      subgoal
        by (metis ldropn_Suc_conv_ldropn lset_intros(1) produce_skip_n_productions_op_correctness produce_skip_n_productions_op_batch_op_soundness_no_monotone)
      done  
    subgoal
      by (metis ldropn_Suc_conv_ldropn lset_intros(1) produce_skip_n_productions_op_correctness produce_skip_n_productions_op_batch_op_soundness_no_monotone)
    done
  done

lemma produce_incr_batch_op_productive:
  "productive stream_in \<Longrightarrow>
   produce (incr_batch_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  unfolding incr_batch_op_def
  using produce_compose_op_batch_op_incr_op_productive by blast

subsection \<open>Soundness\<close> 
lemma produce_incr_batch_op_soundness:
  "lnth (produce (incr_batch_op buf1 buf2) lxs) m = Data t colld \<Longrightarrow>
   enat m < llength (produce (incr_batch_op buf1 buf2) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> n . colld = 
   buf2 @ concat (map snd (ltaken_Data n (produce (batch_op buf1) lxs))) \<and>
   ts lxs t \<union> {t' \<in> fst ` set buf1 . t' \<le> t} = {t' \<in> fst ` set (concat (map snd (ltaken_Data n (produce (batch_op buf1) lxs)))). t' \<le> t} \<and>
   (\<forall> t' \<le> t. coll WM lxs t' + mset (coll_list buf1 t') = mset (coll_list (concat (map snd (ltaken_Data n (produce (batch_op buf1) lxs)))) t'))"
  unfolding llist.set_map incr_batch_op_def
  apply (subst (asm) (1 2) produce_compose_op_correctness_alt)
  using finite_produce_incr_op_exit_LNil apply blast+
  apply (frule produce_incr_op_soundness)
  apply assumption+
  apply (elim conjE exE)
  subgoal for n
    apply hypsubst_thin
    apply (rule exI[of _ "n"])
    apply simp
    apply (intro conjI)
    subgoal premises prems
      using prems(3-) apply -
      apply (frule timestamp_in_taken_Data_inversion)
      apply assumption+
      apply (elim conjE exE)
      apply (subst produce_batch_op_ts_le)
      apply assumption+
      apply simp
      done
    subgoal premises prems
      using prems(3-) apply -
      apply (drule timestamp_in_taken_Data_inversion)
      apply assumption+
      apply auto
      subgoal for b wm' batch' wm t' batch bb
        using ltaken_Data_produce_soundness 
        apply (smt (verit) empty_iff empty_set ltaken_Data.elims prems(3) prems(4) timestamp_in_taken_Data_inversion)
        done 
      done
    done
  done

lemma produce_incr_batch_op_soundness_alt:
  "Data t colld \<in> lset (produce (incr_batch_op buf1 buf2) lxs)  \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> n . colld = 
   buf2 @ concat (map snd (ltaken_Data n (produce (batch_op buf1) lxs))) \<and>
   ts lxs t \<union> {t' \<in> fst ` set buf1 . t' \<le> t} = {t' \<in> fst ` set (concat (map snd (ltaken_Data n (produce (batch_op buf1) lxs)))). t' \<le> t} \<and>
   (\<forall> t' \<le> t. coll WM lxs t' + mset (coll_list buf1 t') = mset (coll_list (concat (map snd (ltaken_Data n (produce (batch_op buf1) lxs)))) t'))"
  apply (auto simp add: lset_conv_lnth)
  apply (drule sym)
  apply (drule produce_incr_batch_op_soundness)
  apply assumption+
  apply auto
  done 

subsection \<open>Completeness\<close> 
lemma produce_incr_batch_op_completeness:
  "(\<exists>i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i) \<or> j = 0 \<and> (\<exists>d. (t, d) \<in> set buf1) \<Longrightarrow>
    lfinite lxs \<or> (\<forall>(t', d)\<in>set buf1. \<exists>wm\<ge>t'. Watermark wm \<in> lset lxs) \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> batch . Data t batch \<in> lset (produce (incr_batch_op buf1 buf2) lxs)"
  unfolding incr_batch_op_def
  apply (subst produce_compose_op_correctness_alt)
  subgoal 
    using finite_produce_incr_op_exit_LNil by blast
  apply (drule sync_completeness_gen_aux[where buf=buf1])
  apply fast
  apply blast
  apply (elim exE)
  subgoal for wm out
    apply (rule produce_incr_op_completeness_alt[where buf=buf2])
    apply assumption
    done
  done

lemma produce_incr_batch_op_completeness_alt:
  "Data t d \<in> lset lxs \<or> (t \<in> fst ` set buf1) \<Longrightarrow>
   lfinite lxs \<or> (\<forall>(t', d)\<in>set buf1. \<exists>wm\<ge>t'. Watermark wm \<in> lset lxs) \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> batch . Data t batch \<in> lset (produce (incr_batch_op buf1 buf2) lxs)"
  unfolding incr_batch_op_def
  apply (subst produce_compose_op_correctness_alt)
  subgoal 
    using finite_produce_incr_op_exit_LNil by blast
  apply (drule sync_completeness_gen_aux_alt[where buf=buf1])
  apply fast
  apply blast
  apply (elim exE)
  subgoal for wm out
    apply (rule produce_incr_op_completeness_alt[where buf=buf2])
    apply assumption
    done
  done

lemma produce_incr_batch_op_Watermark_lset:
  "Watermark -` lset (produce (incr_batch_op buf1 buf2) lxs) = Watermark -` lset lxs"
  unfolding incr_batch_op_def
  apply (subst produce_compose_op_correctness_alt)
  using finite_produce_incr_op_exit_LNil apply blast
  apply (simp add: produce_batch_op_Watermark_lset produce_incr_op_Watermark_lset)
  done

lemma incr_batch_op_prefix_cases:
  "Data t1 batch1 \<in> lset (produce (incr_batch_op buf1 buf2) lxs) \<Longrightarrow>
   Data t2 batch2 \<in> lset (produce (incr_batch_op buf1 buf2) lxs) \<Longrightarrow>
   prefix batch1 batch2 \<or> prefix batch2 batch1"
  unfolding  incr_batch_op_def
  apply (subst (asm) (1 2) produce_compose_op_correctness_alt)
  using finite_produce_incr_op_exit_LNil apply blast+
  apply (drule incr_op_prefix_cases)
  apply auto
  done

end