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
  done

lemma produce_inner_flatten_op_None_False:
  "Watermark wm \<in> lset lxs \<Longrightarrow> produce_inner (flatten_op, lxs) = None \<Longrightarrow> False"
  apply (induct lxs rule: lset_induct)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: event.splits list.splits)
  done

lemma produce_inner_flatten_op_None_f_empty_aux:
  "Data t d \<in> lset lxs \<Longrightarrow> produce_inner (flatten_op, lxs) = None \<Longrightarrow> d = []"
  apply (induct lxs rule: lset_induct)
  apply (simp_all split: prod.splits list.splits event.splits)
  done

lemma produce_inner_flatten_op_None_f_empty:
  "produce_inner (flatten_op, lxs) = None \<Longrightarrow>
   \<forall> t d . Data t d \<in> lset lxs \<longrightarrow> d = []"
  apply safe
  using produce_inner_flatten_op_None_Data_False by blast


lemma produce_inner_flatten_op_None_no_Watermark:
  "produce_inner (flatten_op, lxs) = None \<Longrightarrow>
   \<not> (\<exists> wm . Watermark wm \<in> lset lxs)"
  unfolding not_def
  apply safe
  using produce_inner_flatten_op_None_False apply blast
  done

lemma produce_inner_flatten_op_None_le_Suc_n:
  assumes  "produce_inner (skip_n_productions_op flatten_op n, lxs) = Some (Inl (op', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
  and "produce_inner (skip_n_productions_op flatten_op (Suc n), lxs) = None"
shows "llength (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> (map (Data t) d) | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> enat (Suc n)"
  using assms apply (induct ?P ?R arbitrary: n lxs x xs lxs' op' rule: produce_inner_alt)
  subgoal 
    apply (simp split: option.splits event.splits if_splits; hypsubst_thin)
    subgoal 
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (simp add: Suc_diff_le)
      apply (smt (verit) Suc_diff_le drop_eq_Nil2 ldropn_eq_LNil ldropn_shift leD length_map less_or_eq_imp_le lshift_simps(1) not_less_eq)
      done
    subgoal
      by (metis (no_types, lifting) One_nat_def add_diff_cancel_right' drop_eq_Nil2 ldropn_eq_LNil ldropn_shift length_map less_SucE less_or_eq_imp_le lshift_simps(1) plus_1_eq_Suc skip_n_productions_op_0)
    subgoal
      by (metis (no_types, lifting) One_nat_def diff_Suc_1 eSuc_enat eSuc_le_iff less_imp_Suc_add)
    subgoal
      by (metis Suc_lessI eSuc_enat eSuc_ile_mono skip_n_productions_op_0)
    done
  subgoal
    apply (simp add: lconcat_lmap_LNil' produce_inner_flatten_op_None_f_empty produce_inner_flatten_op_None_no_Watermark split: option.splits event.splits if_splits list.splits; hypsubst_thin)
     subgoal
      using one_eSuc one_enat_def by auto
    done
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
  assumes  "produce_inner (skip_n_productions_op flatten_op n, lxs) = Some (Inl (op', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
  shows "llength (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> map (Data t) d | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) > enat n"
  using assms proof (induct ?P ?R arbitrary: n lxs op' rule: produce_inner_alt)
  case (no_production h lxs op' n op'')
  then show ?case 
  proof (cases h)
    case (Data t d)
    then show ?thesis 
    proof (cases "length d < n")
      case True
      show ?thesis
        using Data True no_production
        apply simp
        apply (metis (mono_tags, lifting) enat_less_enat_plusI2 le_add_diff_inverse length_map less_or_eq_imp_le llength_shift)
        done
    next
      case False
      show ?thesis
        using Data False no_production
        apply simp
        apply (smt (verit, best) False add_diff_inverse_nat enat_less_enat_plusI2 gr_zeroI length_map llength_shift skip_n_productions_op_0 zero_less_diff)
        done
    qed
  next
    case (Watermark wm)
    then show ?thesis 
    proof (cases "Suc 0 < n")
      case True
      from this Watermark no_production show ?thesis 
        apply simp
        apply (metis One_nat_def Suc_diff_1 Suc_ile_eq Suc_lessD)
        done
    next
      case False
      from this Watermark no_production show ?thesis 
        using Suc_ile_eq by force
    qed
  qed
next
  case (produces h lxs op' n)
  then show ?case 
  proof (cases h)
    case (Data t d)
    from this produces show ?thesis 
    proof (cases "length d < n")
      case True
      then show ?thesis 
        using produces Data by simp
    next
      case False
      then show ?thesis 
        using produces Data apply simp
        apply (metis drop_eq_Nil2 enat_less_enat_plusI leI list.distinct(1) llength_shift)
        done
    qed
  next
    case (Watermark wm)
    then show ?thesis 
    proof (cases "Suc 0 < n")
      case True
      then show ?thesis 
        using produces Watermark by simp
    next
      case False
      then show ?thesis 
        using produces Watermark apply simp
        apply (metis drop_Cons' drop_Nil list.distinct(1) zero_enat_def zero_le)
        done
    qed
  qed
qed

lemma produce_inner_skip_n_productions_op_Some_lhd:
  assumes "produce_inner (skip_n_productions_op flatten_op n, lxs) = Some (Inl (op', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
  shows "x = lhd (ldropn n (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> map (Data t) d | Watermark wm \<Rightarrow> [Watermark wm]) lxs)))"
  using assms apply (induct ?P ?R arbitrary: n lxs op' rule: produce_inner_alt)
  subgoal
    apply (simp add: ldropn_shift split: if_splits event.splits; hypsubst_thin)
    subgoal
      by (metis ldropn_0 skip_n_productions_op_0)
    subgoal
      by (metis ldropn_0 skip_n_productions_op_0)
    done
    apply (simp add: ldropn_shift split: if_splits event.splits; hypsubst_thin)
  done

lemma produce_inner_skip_n_productions_op_flatten_op_Inr:  
  assumes  "produce_inner (skip_n_productions_op flatten_op n, lxs) = Some (Inr op)" (is "produce_inner ?P = Some ?R")
  shows "lfinite lxs \<and> exit op = LNil \<and>
   llength (lconcat (lmap (\<lambda>z. case z of Data t x \<Rightarrow> map (Data t) x | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> enat n"
  using assms proof (induct ?P ?R arbitrary: n lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
  proof (cases h)
    case (Data t d)
    show ?thesis 
    proof (cases "length d < n")
      case True
      from this no_production Data show ?thesis 
        apply simp
        apply (smt (verit, ccfv_SIG) drop_eq_Nil2 gen_llength_def ldropn_shift length_map less_or_eq_imp_le list.size(3) llength_code llength_eq_0 llength_shift lnull_ldropn)
        done
    next
      case False
      from this no_production Data show ?thesis 
        apply simp
        apply (smt (verit, best) length_map llength_eq_0 llength_llist_of llist.collapse(1) nle_le shift_LNil skip_n_productions_op_0 zero_enat_def zero_le)
        done
    qed
  next
    case (Watermark wm)
    then show ?thesis 
    proof (cases "Suc 0 < n")
      case True
      from this no_production Watermark show ?thesis 
        apply simp
        apply (metis One_nat_def eSuc_enat eSuc_ile_mono le_add_diff_inverse less_or_eq_imp_le plus_1_eq_Suc)
        done
    next
      case False
      from this no_production Watermark show ?thesis 
        apply simp
        apply (metis eSuc_enat eSuc_ile_mono skip_n_productions_op_0)
        done
    qed
  qed
next
  case terminates
  then show ?case by auto
qed

lemma produce_flatten_op_skip_n_productions_op_correctness:
  "produce (skip_n_productions_op flatten_op n) lxs = ldropn n (lconcat (lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> [Watermark wm] | Data t d \<Rightarrow> map (Data t) d) lxs))"
  apply (coinduction arbitrary: lxs n rule: llist.coinduct)
  apply (intro impI conjI)
  subgoal for lxs
    apply (subst produce.code)
    apply (simp add: produce_inner_skip_n_productions_op_flatten_op_Inr split: option.splits sum.splits)
    apply (intro impI conjI allI)
        subgoal
      using produce_inner_skip_n_productions_op_None_le_n by blast
    subgoal
      by (metis leD produce_inner_flatten_op_Some_le)
    done
  subgoal for lxs n
    apply (subst produce.code)
    apply (simp split: option.splits sum.splits)
    apply (intro impI conjI allI)
    subgoal
      using produce_inner_skip_n_productions_op_None_le_n by blast
    subgoal
      using produce_inner_skip_n_productions_op_Some_lhd by blast
    subgoal
      using produce_inner_skip_n_productions_op_flatten_op_Inr by blast
    done
  subgoal for lxs n
    apply (rule exI[of _ lxs])
    apply (rule exI[of _ "Suc n"])
    apply simp
    apply (intro conjI)
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
   apply (simp split: event.splits)
  subgoal
    by (metis LConsData llist_of.simps(2) monotone_map)
  subgoal
    using monotone.LNil by blast
  subgoal
    by force
  done

lemma tmps_monotone_llist_of_not_ge:
  "wm \<in> tmps xs \<Longrightarrow> wm' \<in> WM \<Longrightarrow> monotone (llist_of xs) WM \<Longrightarrow> \<not> wm \<le> wm'"
  apply (induct xs arbitrary: wm wm' WM)
  apply simp
  subgoal for a xs wm wm' WM
    apply (cases a)
     apply simp_all
     apply (smt (verit, best) LConsData)
    apply auto
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
            apply (intro conjI)
            subgoal
              by (metis produce_inner_flatten_monotone wms.simps(3))
            subgoal
              using produce_inner_flatten_constant by blast
            subgoal
              using produce_inner_flatten_op_monotone by blast
            done
          subgoal for wm
            apply simp
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
           apply simp_all
          apply force
          using monotone_map apply blast
          done
        apply auto
        done
      subgoal for t' d'
        apply (simp split: list.splits)
        using produce_inner_flatten_op_Inr
        using lnull_def apply blast
        done
      done
    done
  done

lemma produce_inner_flatten_op_productive_Data:
  assumes "produce_inner (flatten_op, lxs) = Some (Inl (op, Data t d, xs, lxs'))" (is "produce_inner ?P = Some ?R")
  and "productive lxs"
  and "\<not> lfinite lxs"
shows "(\<forall> x \<in> set xs. is_Data x) \<and> op = flatten_op \<and>
   (\<exists> n. lxs' = ldropn n lxs \<and> (\<exists> wm. t \<le> wm \<and> Watermark wm \<in> lset (produce flatten_op lxs')) \<and> (\<forall> x \<in> set xs. (\<exists> wm \<ge> tmp x. Watermark wm \<in> lset (produce flatten_op lxs'))))"
  using assms apply (induct ?P ?R arbitrary: lxs xs lxs' rule: produce_inner_alt)
  subgoal
    apply (simp split: event.splits; hypsubst_thin)
    apply (intro conjI)
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
  subgoal for h xs lxs lxs' 
    apply (simp add: produce_flatten_op_correctness lset_lconcat_lfinite lconcat_correct split: event.splits; hypsubst_thin?)
      apply (erule productive_cases; elim conjE)
      apply simp_all
    subgoal
      by fastforce
    subgoal
      apply (intro conjI ballI)
    subgoal
      by fastforce
    subgoal
      by (metis ldropn_0 ldropn_Suc_LCons)
    subgoal
      by blast
    subgoal
      by (metis event.inject(2) event.sel(1) event.simps(4) imageE list.set_intros(2) list.set_map vimageD)
    done
  done
  done

lemma produce_inner_flatten_op_productive_Watermark:
  assumes "produce_inner (flatten_op, lxs) = Some (Inl (op, Watermark wm, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "\<not> lfinite lxs"
  shows "op = flatten_op \<and>
   (\<exists> n. lxs' = ldropn (Suc n) lxs \<and> (\<forall> x \<in> lset (ltake n lxs). is_Data x) \<and> (\<forall> x \<in> lset (ltake n lxs). data x = [])) \<and> xs = []"
  using assms apply (induct ?P ?R arbitrary: lxs xs lxs' rule: produce_inner_alt)
  subgoal for h lxs op' xs lxs'
    apply (simp split: event.splits; hypsubst_thin)
    apply (elim conjE exE)
    subgoal for x n
      apply (rule exI[of _ "Suc n"])
      apply auto
      done
    done
  subgoal
    apply (simp split: event.splits; hypsubst_thin)
    subgoal
      by blast
    subgoal
      by (metis empty_iff enat_0 ldropn_0 lset_LNil ltake_0)
    done
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
              apply (simp add: productive_intros(2))
              apply auto[1]
              apply (elim bexE conjE exE)
              subgoal for r wm n
                apply hypsubst_thin
                apply (cases "lfinite (produce flatten_op lxs)")
                 apply auto[1]
                apply simp_all
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
                    apply simp
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
                apply simp
              apply (elim conjE exE)
              apply hypsubst_thin
              apply (cases " lfinite (produce flatten_op (LCons (Data t d) lxs))")
              apply simp_all
              apply (rule disjI2)
              apply (subst produce.code)
              apply (simp split: list.splits option.splits)
              apply (rule disjI1)
              apply (rule productive_prepend_cong1_base)
               apply (metis ldrop_enat productive_ldrop)
              apply auto
              done
            done
          done
        subgoal
          apply (simp split: list.splits)
          apply (meson produce_inner_Some_Inr_lfinite)
          done
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
   apply (simp_all split: list.splits event.splits prod.splits) 
  using prod.exhaust_sel apply blast+
  done

end