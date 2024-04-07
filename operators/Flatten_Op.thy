theory Flatten_Op
  imports
    "../Watermarked_Stream"
    "../Llists_Processors"
    "../Sum_Order"
    "HOL-Library.Code_Lazy"
begin

section \<open>flatten_op\<close> 

primcorec flatten_op where
  "flatten_op = Logic (\<lambda> ev. case ev of
                                Watermark wm \<Rightarrow> (flatten_op, [Watermark wm])
                            | Data t d \<Rightarrow> (flatten_op, map (Data t) d)) LNil"

lemma flatten_op_Nil[simp]:
  "snd (apply flatten_op (Data t [])) = []"
  apply (auto split: list.splits)
  done

lemma lconcat_lmap_LNil':
  "\<forall>t d. Data t d \<in> lset lxs \<longrightarrow> d = [] \<Longrightarrow> \<nexists>wm. Watermark wm \<in> lset lxs \<Longrightarrow>
   lconcat (lmap (case_event (\<lambda>t. map (Data t)) (\<lambda>wm. [Watermark wm])) lxs) = LNil"
  apply (rule lconcat_all_Nil)
  apply (auto split: event.splits)
  done

lemma produce_flatten_op_correctness_aux:
  "\<forall> t d . Data t d \<in> lset lxs \<and> d \<noteq> [] \<Longrightarrow>
   produce flatten_op lxs = lconcat (lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> [Watermark wm] | Data t d \<Rightarrow> map (Data t) d) lxs)"
  apply (auto split: option.splits)
  done

lemma produce_inner_flatten_op_None_Data_False:
  "Data t d \<in> lset lxs \<Longrightarrow> d \<noteq> [] \<Longrightarrow> produce_inner (flatten_op, lxs) = None \<Longrightarrow> False"
  apply (induct lxs rule: lset_induct)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: event.splits list.splits)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: event.splits list.splits)
  done

lemma produce_inner_flatten_op_None_False:
  "Watermark wm \<in> lset lxs \<Longrightarrow> produce_inner (flatten_op, lxs) = None \<Longrightarrow> False"
  apply (induct lxs rule: lset_induct)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: event.splits list.splits)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: event.splits list.splits)
  done

lemma produce_inner_flatten_op_None_f_empty_aux:
  "Data t d \<in> lset lxs \<Longrightarrow> produce_inner (flatten_op, lxs) = None \<Longrightarrow> d = []"
  apply (induct lxs rule: lset_induct)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: list.splits)
  apply (subst (asm) (2) produce_inner.simps)
  apply (auto split: list.splits event.splits)
  done

lemma produce_inner_flatten_op_None_f_empty:
  "produce_inner (flatten_op, lxs) = None \<Longrightarrow>
   \<forall> t d . Data t d \<in> lset lxs \<longrightarrow> d = []"
  apply safe
  apply (meson produce_inner_flatten_op_None_f_empty_aux)
  done

lemma produce_inner_flatten_op_None_no_Watermark:
  "produce_inner (flatten_op, lxs) = None \<Longrightarrow>
   \<not> (\<exists> wm . Watermark wm \<in> lset lxs)"
  unfolding not_def
  apply safe
  using produce_inner_flatten_op_None_False apply blast
  done

lemma produce_inner_flatten_op_Some_flatten_op_None:
  "produce_inner op_lxs = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   op_lxs = (flatten_op, lfilter (\<lambda>x. case x of Data t d \<Rightarrow> d \<noteq> [] | Watermark x \<Rightarrow> True) lxs) \<Longrightarrow>
   produce_inner (flatten_op, lxs) = None \<Longrightarrow>
   False"
  apply (induct op_lxs r arbitrary: lxs op x xs lxs' rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' op' x xs lxs'a lxs
    apply (auto split: if_splits event.splits; hypsubst_thin)
    apply (metis (mono_tags, lifting) lfilter_id_conv lfilter_idem llist.set_intros(1))
    done
  subgoal for op h x xs lxs' lgc' lxs
    apply (auto split: if_splits event.splits; hypsubst_thin)
    apply (metis (mono_tags, lifting) llist.set_intros(1) lset_lfilter mem_Collect_eq produce_inner_flatten_op_None_f_empty)
    apply (metis (no_types, lifting) llist.set_intros(1) lset_lfilter mem_Collect_eq produce_inner_flatten_op_None_False)
    done
  apply auto
  done

lemma produce_inner_flatten_op_Some_Some_ex:
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
  \<exists> lxs'' . produce_inner (flatten_op, lfilter (\<lambda>x. case x of Data t d \<Rightarrow> d \<noteq> [] | Watermark x \<Rightarrow> True) lxs) = Some (Inl (flatten_op, x, xs, lxs''))"
  apply (induct oo r arbitrary: lxs op x xs lxs' rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: if_splits event.splits; hypsubst_thin)
    apply (smt (verit, del_insts) lfilter_cong)
    done
  subgoal for op h x xs lxs' lgc' lxs
    apply (auto split: if_splits event.splits; hypsubst_thin)
    apply (subst produce_inner.simps)
    apply (auto split: if_splits event.splits prod.splits llist.splits; hypsubst_thin)
    apply (subst produce_inner.simps)
    apply (auto split: if_splits event.splits prod.splits llist.splits; hypsubst_thin)
    done
  apply auto
  done

lemma produce_inner_None_constant_op:
  "ev \<in> lset lxs \<Longrightarrow> \<forall>ev. fst (apply op ev) = op \<Longrightarrow> produce_inner (op, lxs) = None \<Longrightarrow> snd (apply op ev) = []"
  apply (induct lxs rule: lset_induct)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: list.splits prod.splits list.splits)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: list.splits prod.splits list.splits)
  apply (metis fst_conv)
  done

lemma produce_inner_flatten_op_None_le_Suc_n:
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inl (op', x, xs, lxs') \<Longrightarrow>
   oo = (skip_n_productions_op flatten_op n, lxs) \<Longrightarrow>
   produce_inner (skip_n_productions_op flatten_op (Suc n), lxs) = None \<Longrightarrow>
   llength (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> (map (Data t) d) | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> enat (Suc n)"
  apply (induct oo r arbitrary: n lxs x xs lxs' op' rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: option.splits event.splits if_splits; hypsubst_thin)
    subgoal 
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: option.splits event.splits if_splits)
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (simp add: Suc_diff_le)
      apply (subst lconcat.corec.code)
      apply (auto split: list.splits event.splits)
      using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
      apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
      apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      done
    subgoal
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: option.splits event.splits if_splits)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (simp add: Suc_diff_le)
      apply (subst lconcat.corec.code)
      apply (auto split: list.splits event.splits)
      using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
      apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
      apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      done
    subgoal 
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: option.splits event.splits if_splits)
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (simp add: Suc_diff_le)
      apply (subst lconcat.corec.code)
      apply (auto split: list.splits event.splits)
      using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
      apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      done
    subgoal 
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: option.splits event.splits if_splits)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (simp add: Suc_diff_le)
      apply (subst lconcat.corec.code)
      apply (auto split: list.splits event.splits)
      using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
      apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      done
    done
  subgoal for op h x xs lxs' lgc' n lxs
    apply (auto split: option.splits event.splits if_splits)
    subgoal for t d
      apply (subst (asm) produce_inner.simps)
      apply (auto split: list.splits if_splits event.splits)
      apply hypsubst_thin
      apply (subst lconcat_code)
      apply (auto split: llist.splits list.splits event.splits)
      using lconcat_lmap_LNil' 
      apply (metis Orderings.order_eq_iff length_map llength_llist_of produce_inner_flatten_op_None_False produce_inner_flatten_op_None_f_empty shift_LNil) 
      done
    subgoal for wm
      apply (subst (asm) produce_inner.simps)
      apply (auto split: list.splits if_splits event.splits)
      apply hypsubst_thin
      apply (subst lconcat_code)
      apply (auto split: llist.splits list.splits event.splits)
      using lconcat_lmap_LNil' 
      apply (metis dual_order.refl eSuc_enat enat_0 llength_LNil produce_inner_flatten_op_None_False produce_inner_flatten_op_None_f_empty)
      done
    done
  apply auto
  done


lemma produce_inner_skip_n_productions_op_None_le_n:
  "produce_inner (skip_n_productions_op flatten_op n, lxs) = None \<Longrightarrow>
   llength (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> map (Data t) d | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> n"
  apply (induct n arbitrary: lxs)
  subgoal 
    apply simp
    apply (simp add: lconcat_lmap_LNil' produce_inner_flatten_op_None_f_empty produce_inner_flatten_op_None_no_Watermark)
    done
  subgoal for n lxs
    apply (cases "produce_inner (skip_n_productions_op flatten_op n, lxs)")
    subgoal
      using Suc_ile_eq order.order_iff_strict 
      apply (metis (no_types, lifting) verit_comp_simplify1(3))
      done
    subgoal for y
      apply (cases y)
      apply hypsubst_thin
      using produce_inner_flatten_op_None_le_Suc_n 
      apply (metis prod_cases4)
      using produce_inner_flatten_op_None_le_Suc_n 
        produce_inner_None_not_lfinite produce_inner_Some_Inr_lfinite by blast
    done
  done

lemma produce_inner_flatten_op_Some_le:
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inl (op', x, xs, lxs') \<Longrightarrow>
   oo = (skip_n_productions_op flatten_op n, lxs) \<Longrightarrow>
   llength (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> map (Data t) d | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> enat n \<Longrightarrow> False"
  apply (induct oo r arbitrary: n lxs x xs lxs' op' rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: if_splits event.splits)
    apply (subst (asm) (2) lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    apply (metis (no_types, lifting) LNil_eq_shift_iff ldropn_eq_LNil ldropn_shift length_map)
    apply (subst (asm) (2) lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    apply (metis (no_types, lifting) One_nat_def co.enat.sel(2) eSuc_le_iff epred_enat)
    apply (subst (asm) (2) lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    apply (metis (no_types, lifting) dual_order.refl ldropn_eq_LNil length_Cons length_map less_Suc_eq llength_LNil shift_eq_shift_ldropn_length skip_n_productions_op_0 zero_enat_def)
    apply (subst (asm) (2) lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    apply (metis One_nat_def eSuc_ile_mono enat_0 one_eSuc one_enat_def skip_n_productions_op_0)
    done
  subgoal for op h x xs lxs' lgc' n lxs
    apply (auto split: if_splits event.splits)
    apply (subst (asm) lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    apply (metis drop_eq_Nil2 enat_less_enat_plusI leD leI list.distinct(1) llength_shift)
    apply (subst (asm) lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    apply (metis drop_Cons' drop_Nil enat_0 list.distinct(1) not_eSuc_ilei0)
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_Some_lhd:
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inl (op', x, xs, lxs') \<Longrightarrow>
   oo = (skip_n_productions_op flatten_op n, lxs) \<Longrightarrow>
   x = lhd (ldropn n (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> map (Data t) d | Watermark wm \<Rightarrow> [Watermark wm]) lxs)))"
  apply (induct oo r arbitrary: n lxs x xs lxs' op' rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' x xs lxs'a op' n lxs
    apply (auto simp add: lappend_llist_of ldropn_shift split: if_splits event.splits; hypsubst_thin)
    apply (subst (2) lconcat_code)
    apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (subst (2) lconcat_code)
    apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (metis Suc_lessD diff_Suc_Suc gr0_conv_Suc ldropn_Suc_LCons minus_nat.diff_0)
    apply (subst lconcat_code)
    apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (metis ldropn_0 skip_n_productions_op_0)
    apply (subst lconcat_code)
    apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (metis ldropn_0 skip_n_productions_op_0)
    done
  subgoal for op h x xs lxs' lgc' n lxs
    apply (auto split: if_splits event.splits; hypsubst_thin)
    apply (subst lconcat_code)
    apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (subst lconcat_code)
    apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (metis drop_Cons' drop_Nil eq_LConsD ldropn_0 list.distinct(1) nth_Cons_0)
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_flatten_op_Inr:  
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   oo = (skip_n_productions_op flatten_op n, lxs) \<Longrightarrow>
   lfinite lxs \<and> exit op = LNil \<and>
   llength (lconcat (lmap (\<lambda>z. case z of Data t x \<Rightarrow> map (Data t) x | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> enat n"
  apply (induct oo r arbitrary: n lxs op rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (simp split: if_splits event.splits; hypsubst_thin)
    subgoal for t d
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply auto
      apply (subst lconcat.code)
      apply (auto split: list.splits event.splits)
      apply (smt (verit, ccfv_threshold) Nat.diff_add_assoc Suc_eq_plus1 Suc_ile_eq add_diff_cancel_left add_mono_thms_linordered_field(1) diff_Suc_1 diff_nat_numeral enat_llength_ldropn iless_Suc_eq length_map less_numeral_extra(1) linorder_not_le list.size(4) nat_code(2) numeral_1_eq_Suc_0 order_less_le plus_1_eq_Suc shift_eq_shift_ldropn_length)    
      apply (smt (verit, ccfv_threshold) One_nat_def Suc_eq_plus1 Suc_ile_eq add_Suc_shift add_diff_cancel_left' diff_Suc_1 diff_Suc_eq_diff_pred enat_eSuc_iff enat_llength_ldropn iless_Suc_eq length_map lessI less_imp_Suc_add list.size(4) llength_shift nle_le plus_enat_simps(1) shift_eq_shift_ldropn_length)
      done
    subgoal for wm
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply auto
      apply (subst lconcat.code)
      apply (auto split: list.splits event.splits)
      apply (metis Suc_lessD diff_Suc_Suc eSuc_enat eSuc_ile_mono gr0_implies_Suc minus_nat.diff_0)
      done
    subgoal for t d
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
      apply simp
      apply auto
      apply (subst lconcat.code)
      apply (auto simp add: eSuc_enat enat_0 llength_shift split: list.splits event.splits)
      done
    subgoal 
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
      apply simp
      apply auto
      apply (subst lconcat.code)
      apply (auto split: list.splits event.splits)
      apply (metis dual_order.refl eSuc_enat le_zero_eq zero_enat_def)
      done
    done
  subgoal for op h x xs lxs lxs'' lgc' n lxs' op'
    apply (subst (asm) produce_inner.simps)
    apply auto
    done
  apply (simp add: lconcat.code)
  done

lemma produce_flatten_op_skip_n_productions_op_correctness:
  "produce (skip_n_productions_op flatten_op n) lxs = ldropn n (lconcat (lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> [Watermark wm] | Data t d \<Rightarrow> map (Data t) d) lxs))"
  apply (coinduction arbitrary: lxs n rule: llist.coinduct)
  apply (intro impI conjI)
  subgoal for lxs
    apply (subst produce.code)
    apply (auto split: option.splits sum.splits)
    using produce_inner_skip_n_productions_op_None_le_n apply blast
    using  produce_inner_flatten_op_Some_le 
    apply blast
    using produce_inner_skip_n_productions_op_flatten_op_Inr 
    apply fast     
    using produce_inner_skip_n_productions_op_flatten_op_Inr 
    using llist.discI(1) apply blast
    done
  subgoal for lxs n
    apply (subst produce.code)
    apply (auto split: option.splits sum.splits)
    using produce_inner_skip_n_productions_op_None_le_n apply blast
    subgoal for op' x xs lxs'
      using produce_inner_skip_n_productions_op_Some_lhd apply fast
      done
    subgoal 
      using produce_inner_skip_n_productions_op_flatten_op_Inr 
      by blast
    done
  subgoal for lxs n
    apply (rule exI[of _ lxs])
    apply (rule exI[of _ "Suc n"])
    apply auto
    apply (metis lhd_LCons_ltl produce_skip_n_productions_op_LCons)
    apply (simp add: ldrop_eSuc_ltl ltl_ldropn)
    done
  done

lemma produce_flatten_op_correctness:
  "produce flatten_op lxs = lconcat (lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> [Watermark wm] | Data t d \<Rightarrow> map (Data t) d) lxs)"
  using produce_flatten_op_skip_n_productions_op_correctness[where n=0] apply auto
  done

lemma monotone_map:
  "\<forall> wm \<in> WM . \<not> wm \<ge> t \<Longrightarrow> monotone (llist_of (map (Data t) xs)) WM"
  apply (induct xs arbitrary: t WM)
  apply simp
  using monotone.LNil apply blast
  apply (simp add: LConsL)
  done


lemma produce_inner_flatten_op_monotone:
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   monotone (LCons x (llist_of xs)) WM"
  apply (induct oo r arbitrary: lxs x xs lxs' op WM rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: event.splits)
    done
  apply (auto split: event.splits)
  using monotone_map apply (metis LConsData LConsL)
  apply (meson LConsWatermark monotone.LNil strict_monotone_with_smaller_initial_watermark_Watermark)
  done

lemma tmps_monotone_llist_of_not_ge:
  "wm \<in> tmps xs \<Longrightarrow> wm' \<in> WM \<Longrightarrow> monotone (llist_of xs) WM \<Longrightarrow> \<not> wm \<le> wm'"
  apply (induct xs arbitrary: wm wm' WM)
  apply simp
  subgoal for a xs wm wm' WM
    apply (cases a)
    apply simp
    apply auto
    apply (smt (verit, best) LConsData)
    done
  done

lemma produce_inner_flatten_constant:
  "produce_inner oo = Some r \<Longrightarrow> 
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
   op = flatten_op"
  apply (induct oo r arbitrary: lxs x xs lxs' op WM rule: produce_inner_alt[consumes 1])
  apply (auto split: event.splits)
  done

lemma produce_inner_flatten_monotone:
  "produce_inner oo = Some r \<Longrightarrow> 
   r = Inl (op, x, xs, lxs') \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   monotone lxs' (wms (x # xs) \<union> WM)"
  apply (induct oo r arbitrary: lxs x xs lxs' op WM rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: event.splits)
    done
  subgoal for op h x xs lxs' lgc' lxs WM
    apply (subst (asm) produce_inner.simps)
    apply (auto split: event.splits)
    done
  apply auto
  done

lemma produce_inner_flatten_op_Inr:
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
   exit op = LNil"
  apply (induct oo r arbitrary: lxs op  rule: produce_inner_alt[consumes 1])
  apply (auto split: event.splits)
  done



subsection \<open>Strict monotone\<close> 
lemma produce_flatten_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   produce flatten_op stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  apply (coinduction arbitrary: stream_in WM stream_out rule: strict_monotone_coinduct_strict_monotone_prepend_cong1)
  subgoal for stream_in WM stream_out 
    apply (simp split: option.splits prod.splits sum.splits)
    apply hypsubst_thin
    apply (erule monotone.cases)
    apply (simp add: lconcat_code)
    subgoal for lxs wm WM'
      apply hypsubst_thin
      apply (rule disjI2)
      apply (rule disjI1)
      apply (rule exI[of _ "wm"])
      apply (rule exI[of _ "lconcat (lmap (case_event (\<lambda>t d. map (Data t) d) (\<lambda>wm. [Watermark wm])) lxs)"])
      apply (rule conjI)
      unfolding produce_flatten_op_correctness
      apply (simp add: lconcat_code)
      apply (metis (mono_tags, lifting) monotone_prepend_cong_base)
      done
    subgoal for WM t lxs d
      apply hypsubst_thin
      apply (subst (1 2) produce.code)
      apply (simp split: option.splits sum.splits prod.splits)
      apply (intro allI impI conjI)
      subgoal for op op' x xs' lxs'
        apply (subst (asm) produce_inner.simps)
        apply (simp split: list.splits)
        subgoal
          apply (cases x)
          subgoal for t' d'
            apply hypsubst_thin
            apply (intro disjI2)
            apply simp
            apply (intro conjI)
            apply (meson LConsData produce_inner_flatten_op_monotone)
            apply (intro disjI1)
            apply (rule monotone_prepend_cong_prepend)
            apply (rule monotone_prepend_cong_base)
            apply (rule exI[of _ lxs'])
            apply auto
            subgoal
              by (metis produce_inner_flatten_monotone wms.simps(3))
            subgoal
              using produce_inner_flatten_constant by blast
            subgoal
              using produce_inner_flatten_op_monotone by blast
            done
          subgoal for wm
            apply auto
            by (smt (verit, del_insts) LConsWatermark Un_insert_left Un_insert_right monotone_prepend_cong_base monotone_prepend_cong_prepend produce_inner_flatten_constant produce_inner_flatten_monotone produce_inner_flatten_op_monotone wms.simps(2))
          done
        apply (cases x)
        subgoal for t' d'
          apply hypsubst_thin
          apply (intro disjI2)
          apply simp
          apply (intro conjI)
          apply fastforce
          apply (intro disjI1)
          apply (rule monotone_prepend_cong_prepend)
          apply (rule monotone_prepend_cong_base)
          apply (rule exI[of _ lxs'])
          apply auto
          using monotone_map apply blast
          done
        apply auto
        done
      subgoal for t' d'
        apply (subst (asm) produce_inner.simps)
        apply (simp split: list.splits)
        using produce_inner_flatten_op_Inr
        using lnull_def apply blast
        done
      done
    done
  done

lemma produce_inner_flatten_op_productive_Data:
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inl (op, Data t d, xs, lxs') \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   (\<forall> x \<in> set xs. is_Data x) \<and>
   op = flatten_op \<and>
   (\<exists> n. lxs' = ldropn n lxs \<and> (\<exists> wm. t \<le> wm \<and> Watermark wm \<in> lset (produce flatten_op lxs')) \<and> (\<forall> x \<in> set xs. (\<exists> wm \<ge> tmp x. Watermark wm \<in> lset (produce flatten_op lxs'))))"
  apply (induct oo r arbitrary: lxs xs lxs' op rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto split: event.splits; hypsubst_thin)
    using productive_drop_head apply blast
    subgoal
      using productive_drop_head by blast
    subgoal
      by (metis ldropn_Suc_LCons productive_drop_head)
    subgoal
      using productive_drop_head by blast
    subgoal
      using productive_drop_head by blast
    done
  subgoal for op h x xs lxs lxs' lgc' lxsa xsa lxs'' op'
    apply (subst (asm) produce_inner.simps)
    apply (auto split: event.splits)
    subgoal
      by (metis ldropn_0 ldropn_Suc_LCons)
    subgoal
      apply (subst produce_flatten_op_correctness)
      apply (auto simp add: lconcat_correct)
      apply (subst lset_lconcat_lfinite)
      apply auto
      apply (erule productive_cases)
      apply auto
      apply force
      done
    subgoal
      apply (subst produce_flatten_op_correctness)
      apply (auto simp add: lconcat_correct)
      apply (subst lset_lconcat_lfinite)
      apply auto
      apply (erule productive_cases)
      apply auto
      apply force
      done
    done
  apply auto
  done


lemma produce_inner_flatten_op_productive_Watermark:
  "produce_inner oo = Some r \<Longrightarrow>
   r = Inl (op, Watermark wm, xs, lxs') \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   xs = [] \<and>
   op = flatten_op \<and>
   (\<exists> n. lxs' = ldropn (Suc n) lxs \<and> (\<forall> x \<in> lset (ltake n lxs). is_Data x) \<and> (\<forall> x \<in> lset (ltake n lxs). data x = []))"
  apply (induct oo r arbitrary: lxs xs lxs' op rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: event.splits; hypsubst_thin)
    subgoal for x n
      apply (rule exI[of _ "Suc n"])
      apply auto
      done
    done
  subgoal for op h x xs lxs lxs' lgc' lxsa xsa lxs'' op'
    apply (subst (asm) produce_inner.simps)
    apply (auto split: event.splits)
    apply hypsubst_thin
    apply (rule exI[of _ 0])
    apply auto
    apply (simp_all add: enat_0)
    done
  apply auto
  done



subsection \<open>productive\<close> 
lemma produce_flatten_op_productive:
  "productive stream_in \<Longrightarrow>
   produce flatten_op stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  apply (coinduction arbitrary: stream_in stream_out rule: productive_coinduct_prepend_cong1)
  subgoal for stream_in stream_out 
    apply (simp split: option.splits prod.splits sum.splits)
    apply hypsubst_thin
    apply (erule productive_cases)
    apply (simp add: lconcat_code)
    subgoal
      apply (rule disjI1)
      apply (subst produce_flatten_op_correctness)
      apply (simp add: lfinite_lconcat)
      done
    subgoal for lxs t d
      apply (cases "produce_inner (flatten_op, stream_in)")
      subgoal
        apply (rule disjI1)
        by (metis lfinite_LNil produce_inner_None_produce_LNil)
      subgoal for r
        apply (cases r)
        subgoal for r'
          apply (cases r')
          subgoal for op x xs lxs'
            apply hypsubst_thin
            apply (cases x)
            subgoal for t' d'
              apply hypsubst_thin
              apply (frule produce_inner_flatten_op_productive_Data)
              apply (rule refl)+
              apply (simp add: productive_intros(2))
              apply auto[1]
              apply (elim bexE conjE exE)
              subgoal for r wm n
                apply hypsubst_thin
                apply auto
                apply (subst (asm) produce_inner.simps)
                apply (subst produce.code)
                apply (simp split: list.splits option.splits)
                apply (intro conjI impI)
                apply blast
                subgoal
                  apply (rule disjI1)
                  apply (rule productive_prepend_cong1_prepend_1)
                  apply (rule productive_prepend_cong1_base)
                  apply (metis ldrop_enat productive_intros(2) productive_ldrop vimage_eq)
                  subgoal
                    apply auto
                    apply (metis event.sel(1) nth_mem)
                    done
                  done
                subgoal
                  apply (simp split: sum.splits)
                  apply (intro conjI allI impI)
                  apply (meson not_Some_eq produce_inner_flatten_op_None_False)
                  apply (metis lfinite.simps lfinite_shift produce_inner_Some_produce)
                  subgoal
                    by auto
                  subgoal
                    apply (rule disjI1)
                    apply (rule productive_prepend_cong1_prepend_1)
                    apply (rule productive_prepend_cong1_base)
                    apply (meson produce_inner_Some_produce)
                    apply auto
                    done
                  subgoal
                    using produce_inner_Some_Inr_lfinite by blast
                  subgoal
                    by (meson produce_inner_Some_Inr_lfinite)
                  subgoal
                    using produce_inner_Some_Inr_lfinite by blast
                  done
                done
              done
            subgoal for wm
              apply hypsubst_thin
              apply (frule produce_inner_flatten_op_productive_Watermark)
              apply (rule refl)+
              apply simp
              apply (elim conjE exE)
              apply hypsubst_thin
              apply (cases " lfinite (produce flatten_op (LCons (Data t d) lxs))")
              apply simp_all
              apply (rule disjI2)
              apply (subst (asm) produce_inner.simps)
              apply (subst produce.code)
              apply (simp split: list.splits option.splits)
              apply auto
              apply (rule productive_prepend_cong1_base)
              apply (metis ldrop_enat productive_ldrop)
              done
            done
          done
        subgoal
          apply auto
          by (meson lfinite_code(2) produce_inner_Some_Inr_lfinite)
        done
      done
    subgoal for xs' t
      apply hypsubst_thin
      apply simp
      apply (cases "lfinite (produce flatten_op xs')")
      apply simp_all
      apply (rule disjI1)
      apply (rule productive_prepend_cong1_base)
      by blast
    done
  done

lemma finite_produce_flatten_op_exit_LNil:
  "finite_produce flatten_op xs = (op', out) \<Longrightarrow> exit op' = LNil"
  apply (induct xs arbitrary: op' out)
  apply (auto split: list.splits event.splits prod.splits) 
  done

end