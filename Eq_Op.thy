theory Eq_Op
  imports
    Llists_Processors
    Watermarked_Stream
begin


abbreviation OP_EQ where
  "OP_EQ ev p WM op1 op2 \<equiv> (
    case ev of 
      Data t d \<Rightarrow> (\<forall>wm\<in>WM. \<not> t \<le> wm) \<longrightarrow> rel_prod (p WM) (=) (apply op1 ev) (apply op2 ev)
    | Watermark wm \<Rightarrow> rel_prod (p (insert wm WM)) (=) (apply op1 ev) (apply op2 ev)) \<and> exit op1 = exit op2"

definition WM_EQ where
  "WM_EQ = (\<lambda>p WM op1 op2. 
        (\<forall>ev. OP_EQ ev p WM op1 op2))"

definition wm_eq where
  "wm_eq = gfp WM_EQ"

lemma wm_eq_mono:
  "mono WM_EQ"
  apply (auto simp: WM_EQ_def rel_prod_sel le_fun_def mono_def split: event.splits)
  done

lemmas wm_eq_coinduct = coinduct[OF wm_eq_mono, folded wm_eq_def, unfolded WM_EQ_def le_fun_def le_bool_def, rule_format, rotated, of R WM op1 op2 for R WM op1 op2]


lemmas wm_eq_cases = gfp_unfold[OF wm_eq_mono, folded wm_eq_def, unfolded WM_EQ_def, THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD1, elim_format]
lemmas wm_eq_intros = gfp_unfold[OF wm_eq_mono, folded wm_eq_def, unfolded WM_EQ_def, THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD2]

lemma wm_eq_sym:
  "wm_eq WM op1 op2 \<Longrightarrow> wm_eq WM op2 op1"
  apply (coinduction arbitrary: WM op1 op2 rule: wm_eq_coinduct) 
  apply (auto simp add: rel_prod_sel split: event.splits elim!: wm_eq_cases)
    apply metis+
  done

lemma wm_eq_refl[simp]:
  "wm_eq WM op op"
  apply (coinduction arbitrary: WM op rule: wm_eq_coinduct) 
  apply (auto simp add: rel_prod_sel split: event.splits)
  done

lemma not_wm_eq_not_eq:
  "\<not> wm_eq WM op1 op2 \<Longrightarrow>
   op1 \<noteq> op2"
  using wm_eq_refl by blast


lemma produce_inner_wm_eq_Inl:
  "produce_inner (op2, lxs) = Some r \<Longrightarrow> r = Inl (op', x, xs, lxs') \<Longrightarrow> wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> produce_inner (op1, lxs) = None \<Longrightarrow> False"
  apply (induct "(op2, lxs)" r arbitrary: lxs x xs lxs' op1 op2 WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' lxs' zs ys x xs lxs'a op1 WM
   apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  subgoal for op h x xs lxs' op1 WM
    apply (subst (asm) (1 2) produce_inner.simps)
   apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  apply auto
  done

lemma produce_inner_wm_eq_Inr:
  "produce_inner (op2, lxs) = Some r \<Longrightarrow> r = Inr op2' \<Longrightarrow> wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> produce_inner (op1, lxs) = None \<Longrightarrow> False"
  apply (induct "(op2, lxs)" r arbitrary: lxs op2' op1 op2 WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' lxs' zs ys op2' op1 WM
   apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  subgoal for op h x xs lxs' op1 WM
    apply (subst (asm) (1 2) produce_inner.simps)
   apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  apply auto
  done

lemma produce_inner_wm_eq_Inr_Inl:
  "produce_inner (op2, lxs) = Some r \<Longrightarrow> r = Inr op2' \<Longrightarrow> wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> produce_inner (op1, lxs) = Some (Inl x) \<Longrightarrow> False"
 apply (induct "(op2, lxs)" r arbitrary: lxs op2' op1 op2 WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' lxs' zs ys op2' op1 WM
   apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  subgoal for op h x xs lxs' op1 WM
    apply (subst (asm) (1 2) produce_inner.simps)
   apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  apply auto
  done

lemma produce_inner_wm_eq_Inr_Inr:
  "produce_inner (op2, lxs) = Some r \<Longrightarrow> r = Inr op2' \<Longrightarrow> wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> produce_inner (op1, lxs) = Some (Inr op1') \<Longrightarrow> exit op1' = exit op2'"
 apply (induct "(op2, lxs)" r arbitrary: lxs op2' op1 op2 WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' lxs' zs ys op2' op1 WM
   apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  subgoal for op h x xs lxs' op1 WM
    apply (subst (asm) (1 2) produce_inner.simps)
   apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  apply auto
  apply (erule wm_eq_cases)
  apply auto
  done

lemma produce_inner_wm_eq_Some_Some:
  "produce_inner (op1, lxs) = Some r \<Longrightarrow>
   r = Inl (op1', x, xs, lxs') \<Longrightarrow>
   wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   produce_inner (op2, lxs) = Some (Inl (op2', y, ys, lys')) \<Longrightarrow>
   lxs' = lys' \<and> x = y \<and> xs = ys"
  apply (induct "(op1, lxs)" r arbitrary: lxs x xs lxs' op1 op2 op1' op2' y ys lys' WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' x xs lxs'a op1' op2 op2' y ys lys' WM'
    apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  subgoal for op h x xs lxs' lgc' op2 op2' y ys lys' WM
    apply (subst (asm) (1 2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  apply auto
  done

lemma produce_inner_Some_wm_eq_ldropn:
  "produce_inner (op1, lxs) = Some r \<Longrightarrow>
   r = Inl (op1', x, xs, lxs') \<Longrightarrow>
   wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   produce_inner (op2, lxs) = Some (Inl (op2', x, xs, lxs')) \<Longrightarrow>
   \<exists> n . wm_eq (wms (list_of (ltake n lxs)) \<union> WM) op1' op2' \<and> ldropn n lxs = lxs' \<and> n > 0 \<and> monotone lxs' (wms (list_of (ltake n lxs)) \<union> WM)"
  apply (induct "(op1, lxs)" r arbitrary: lxs x xs  op1 op2 op1' op2' lxs' WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' lxs' zs ys x xs op2 op1' op2' lxs'a WM
    apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    subgoal for t d op'
      apply (drule meta_spec)
      apply (drule meta_spec[of _ op'])
      apply (drule meta_spec[of _ op2'])
      apply (drule meta_spec[of _ WM])
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply assumption
      apply auto
      apply hypsubst_thin
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply simp
        done
      done
    subgoal for wm op'
      apply (drule meta_spec)
    apply (drule meta_spec[of _ op'])
      apply (drule meta_spec[of _ op2'])
      apply (drule meta_spec[of _ "insert wm WM"])
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
      using strict_monotone_LCons_Watermark_insert apply blast
      apply (drule meta_mp)
       apply assumption
      apply auto
      apply hypsubst_thin
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply simp
        done
      done
    done
  subgoal for op h x xs lxs' lgc' op2 op2' WM
    apply (subst (asm) (1 2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    using ldropn_0 ldropn_Suc_LCons list_of_llist_of ltake_eSuc_LCons ltake_eq_LNil_iff shift_LNil singleton_lshift sup_bot.right_neutral sup_commute wms.simps(1) wms.simps(3) zero_enat_def
    apply (metis eSuc_enat strict_monotone_drop_head zero_less_Suc)
    using  One_nat_def Suc_ile_eq Un_insert_left enat_ord_code(4) iless_Suc_eq
    ldropn_0 ldropn_Suc_conv_ldropn lfinite_ltake linorder_not_le list_of_LCons list_of_LNil llength_LCons
   llist.inject ltake.ctr(1) ltake_eSuc_LCons nless_le not_eSuc_ilei0 one_eSuc one_enat_def sup_bot.right_neutral sup_commute wms.simps(1) wms.simps(2)
    apply (smt (z3) One_nat_def Un_insert_left enat_ord_code(4) eq_LConsD ldropn_0 ldropn_Suc_conv_ldropn less_Suc_eq lfinite_ltake linorder_not_le list_of_LCons list_of_LNil llength_LCons ltake_eSuc_LCons ltake_eq_LNil_iff not_eSuc_ilei0 one_eSuc one_enat_def strict_monotone_LCons_Watermark_insert sup_bot.right_neutral sup_commute wms.simps(1) wms.simps(2) zero_enat_def)
    done
  apply auto
  done

lemma wm_eq_soundness:
  "wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   produce op1 lxs = produce op2 lxs"
  apply (coinduction arbitrary: op1 op2 lxs WM rule: llist.coinduct_upto)
  apply (intro allI impI conjI)
  subgoal for op1 op2 lxs WM
    apply (subst (1 2) produce.code)
    apply (auto 2 1 dest: produce_inner_wm_eq_Inr_Inl produce_inner_wm_eq_Inr_Inl[OF _ _ wm_eq_sym] produce_inner_wm_eq_Inr produce_inner_wm_eq_Inr[OF _ _ wm_eq_sym] produce_inner_wm_eq_Inl produce_inner_wm_eq_Inl[OF _ _ wm_eq_sym] split: option.splits sum.splits)
      apply (meson not_Some_eq produce_inner_wm_eq_Inl wm_eq_sym)
    using produce_inner_wm_eq_Inr_Inr wm_eq_sym
    apply metis+
    done
  subgoal for op1 op2 lxs WM
    apply (subst (1 2) produce.code)
    apply (auto 2 1 dest:  produce_inner_wm_eq_Inr_Inl produce_inner_wm_eq_Inr_Inl[OF _ _ wm_eq_sym] produce_inner_wm_eq_Some_Some produce_inner_wm_eq_Inl produce_inner_wm_eq_Inl[OF _ _ wm_eq_sym] split: option.splits sum.splits)
    using produce_inner_wm_eq_Inr apply blast
   apply (simp_all add: produce_inner_None_produce_LNil produce_inner_wm_eq_Inr_Inr)
    done
  subgoal for op1 op2 lxs WM
    apply (subst (3 4) produce.code)
    apply (auto 2 1 dest: produce_inner_wm_eq_Inr_Inl produce_inner_wm_eq_Inr_Inl[OF _ _ wm_eq_sym] produce_inner_wm_eq_Inr produce_inner_wm_eq_Inr[OF _ _ wm_eq_sym] produce_inner_wm_eq_Inl produce_inner_wm_eq_Inl[OF _ _ wm_eq_sym] split: option.splits sum.splits)
    using lshift.cong_refl apply blast
      apply (rule llist.cong_lshift)
    subgoal 
      by (meson produce_inner_wm_eq_Some_Some)
    subgoal for op1' x xs lxs' op2' y ys lys
    apply (rule llist.cong_base)
      apply (frule produce_inner_wm_eq_Some_Some)
      apply (rule refl)
          apply assumption+
       apply (elim conjE)
       apply hypsubst_thin      
      apply (frule produce_inner_Some_wm_eq_ldropn)
      apply (rule refl)
       apply assumption+
       apply (elim conjE exE)
      subgoal for n
        apply (rule exI conjI refl)+
        defer
         apply assumption
        apply hypsubst_thin
        apply simp
        done
      done
    apply (simp add: lshift.cong_refl produce_inner_wm_eq_Inr_Inr)
    done
  done

end