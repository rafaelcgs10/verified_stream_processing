theory Eq_Op
  imports
    Llists_Processors
    Watermarked_Stream
begin


abbreviation eq_op_lifted where
  "eq_op_lifted ev p WM op1 op2 \<equiv> (
    case ev of 
      Data t d \<Rightarrow> (\<forall>wm\<in>WM. \<not> t \<le> wm) \<longrightarrow> rel_prod (p WM) (=) (apply op1 ev) (apply op2 ev)
    | Watermark wm \<Rightarrow> rel_prod (p (insert wm WM)) (=) (apply op1 ev) (apply op2 ev)) \<and> exit op1 = exit op2"

lemma WM_EQ_mono[mono]:
  "(\<And>W x y. P W x y \<longrightarrow> Q W x y) \<Longrightarrow>
    (\<forall>ev. eq_op_lifted ev P W op_1 op_2) \<longrightarrow> (\<forall>ev. eq_op_lifted ev Q W op_1 op_2)"
  by (auto simp: rel_prod_sel split: event.splits)

coinductive eq_op where "(\<forall>ev. eq_op_lifted ev eq_op W op_1 op_2) \<Longrightarrow> eq_op W op_1 op_2"

lemma eq_op_sym:
  "eq_op WM op1 op2 \<Longrightarrow> eq_op WM op2 op1"
proof (coinduction arbitrary: WM op1 op2 rule: eq_op.coinduct)
  case eq_op
  then show ?case
    apply -
    apply (erule eq_op.cases)
    apply (simp add: rel_prod_sel split: event.splits)
    apply metis
    done
qed


lemma eq_op_refl[simp]:
  "eq_op WM op op"
proof (coinduction arbitrary: WM op rule: eq_op.coinduct)
  case eq_op
  then show ?case by (auto simp add: rel_prod_sel split: event.splits)
qed

lemma not_eq_op_not_eq:
  "\<not> eq_op WM op1 op2 \<Longrightarrow> op1 \<noteq> op2"
  using eq_op_refl by blast

lemma produce_inner_eq_op_Inl:
  assumes  "produce_inner (op2, lxs) = Some r"
    and "r = Inl (op', x, xs, lxs')" and "eq_op WM op1 op2"
    and "monotone lxs WM" and "produce_inner (op1, lxs) = None" 
  shows "False"
  using assms proof (induct "(op2, lxs)" r arbitrary: lxs x xs lxs' op1 op2 WM rule: produce_inner_induct)
  case (no_production op h lxs lgc' zs)
  from no_production(6) obtain op1' where H1:"apply op1 h = (op1', [])" and H2: "produce_inner (op1', lxs) = None"
    by (subst (asm) produce_inner.simps; auto split: prod.splits list.splits)
  then show ?case
  proof (cases rule: eq_op.cases[OF no_production(4)])
    case (1 W op_1 op_2)
    then show ?thesis 
      using no_production(1,2,3,5) H1 H2 apply hypsubst_thin
      by (simp split: event.splits; metis LConsData event.exhaust fst_conv rel_prod_sel strict_monotone_LCons_Watermark_insert)
  qed
next
  case (produces op h x xs lxs lxs' lgc')
  from produces(6) obtain op1' where H1:"apply op1 h = (op1', [])" and H2: "produce_inner (op1', lxs) = None"
    by (subst (asm) produce_inner.simps; auto split: prod.splits list.splits)
  then show ?case 
  proof (cases rule: eq_op.cases[OF produces(4)])
    case (1 W op_1 op_2)
    then show ?thesis 
      using produces(1,2,3,5) H1 H2 apply hypsubst_thin
      by (simp split: event.splits; smt (verit, best) LConsData event.exhaust list.discI rel_prod_sel snd_conv)
  qed
next
  case (terminates op)
  then show ?case by auto
qed


lemma produce_inner_eq_op_Inr:
  assumes "produce_inner (op2, lxs) = Some r" and "r = Inr op2'" and "eq_op WM op1 op2" 
    and "monotone lxs WM" and "produce_inner (op1, lxs) = None" shows "False"
  using assms proof (induct "(op2, lxs)" r arbitrary: lxs x xs lxs' op1 op2 WM rule: produce_inner_induct)
  case (no_production op h lxs lgc' zs)
  from no_production(6) obtain op1' where H1:"apply op1 h = (op1', [])" and H2: "produce_inner (op1', lxs) = None"
    by (subst (asm) produce_inner.simps; auto split: prod.splits list.splits)
  then show ?case
  proof (cases rule: eq_op.cases[OF no_production(4)])
    case (1 W op_1 op_2)
    then show ?thesis 
      using no_production(1,2,3,5) H1 H2 apply hypsubst_thin
      by (simp split: event.splits; metis LConsData event.exhaust fst_conv rel_prod_sel strict_monotone_LCons_Watermark_insert)
  qed
next
  case (produces op h x xs lxs lxs' lgc')
  from produces(6) obtain op1' where H1:"apply op1 h = (op1', [])" and H2: "produce_inner (op1', lxs) = None"
    by (subst (asm) produce_inner.simps; auto split: prod.splits list.splits)
  then show ?case 
  proof (cases rule: eq_op.cases[OF produces(4)])
    case (1 W op_1 op_2)
    then show ?thesis 
      using produces(1,2,3,5) H1 H2 apply hypsubst_thin
      by (simp split: event.splits; smt (verit, best) LConsData event.exhaust list.discI rel_prod_sel snd_conv)
  qed
next
  case (terminates op)
  then show ?case by auto
qed

lemma eq_op_same_output_head:
  "eq_op WM op1 op2 \<Longrightarrow>
   monotone (LCons h lxs) WM \<Longrightarrow>
   snd (apply op1 h) = snd (apply op2 h)"
  apply (erule eq_op.cases)
  apply (drule spec[of _ h])
  apply (auto simp add: rel_prod_sel split: event.splits list.splits prod.splits elim: LConsData LConsWatermark)
  done

lemma eq_op_next:
  "eq_op WM op1 op2 \<Longrightarrow>
   monotone (LCons h lxs) WM \<Longrightarrow>
   eq_op (case_event (\<lambda> _ _. WM) (\<lambda> wm. insert wm WM) h) (fst (apply op1 h)) (fst (apply op2 h))"
  apply (erule eq_op.cases)
  apply (drule spec[of _ h])
  apply (auto simp add: rel_prod_sel split: event.splits list.splits prod.splits elim: LConsData LConsWatermark)
  done

lemma eq_op_next_output:
  assumes "eq_op WM op1 op2"
    and "apply op1 h = (op1', out)"
    and "monotone (LCons h lxs) WM"
  shows "apply op2 h = (fst (apply op2 h), out)"
  using assms apply -
  apply (erule eq_op.cases)
  apply hypsubst_thin
  apply (drule spec[of _ h])
  apply (auto simp add: rel_prod_sel split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
  done


lemma produce_inner_eq_op_Inr_Inl:
  assumes "produce_inner (op2, lxs) = Some r" 
    and "r = Inr op2'" and "eq_op WM op1 op2" and "monotone lxs WM" and "produce_inner (op1, lxs) = Some (Inl x)" 
  shows "False"
  using assms proof (induct "(op2, lxs)" r arbitrary: lxs op1 op2 WM rule: produce_inner_induct)
  case (no_production op2 h lxs op' zs)
  from no_production(1,6,4,5) obtain op1' where H1:"apply op1 h = (op1', [])" and H2: "produce_inner (op1', lxs) = Some (Inl x)"
    apply -
    apply (subst (asm) (2) produce_inner.simps; simp split: prod.splits list.splits)
    using eq_op_same_output_head by fastforce
  from no_production(5) have "monotone lxs WM"
    by blast
  from this no_production H1 H2 show ?case 
    apply hypsubst_thin
    apply (drule eq_op_next)
     apply assumption
    apply (auto split: event.splits)
    done
next
  case (produces op h x xs lxs lxs' op')
  then show ?case 
    by blast
next
  case (terminates op)
  then show ?case by auto
qed

lemma produce_inner_eq_op_Inr_Inr:
  assumes "produce_inner (op2, lxs) = Some r" and "r = Inr op2'" and "eq_op WM op1 op2"
    and "monotone lxs WM" and "produce_inner (op1, lxs) = Some (Inr op1')"
  shows "exit op1' = exit op2'"
  using assms proof(induct "(op2, lxs)" r arbitrary: lxs op2' op1 op2 WM rule: produce_inner_induct)
  case (no_production op2 h lxs op' zs)
  from no_production(1,6,4,5) obtain op1'' where H1:"apply op1 h = (op1'', [])" and H2: "produce_inner (op1'', lxs) = Some (Inr op1')"
    apply -
    by (subst (asm) (2) produce_inner.simps; simp split: prod.splits list.splits)
  from no_production(5) have "monotone lxs WM"
    by blast
  from this no_production H1 H2 show ?case 
    apply hypsubst_thin
    apply (drule eq_op_next)
     apply assumption
    apply (auto split: event.splits)
    done
next
  case (produces op h x xs lxs lxs' op')
  then show ?case 
    by force
next
  case (terminates op)
  then show ?case 
    by (simp add: eq_op.simps)
qed

lemma produce_inner_eq_op_Some_Some:
  assumes "produce_inner (op1, lxs) = Some r"
    and "r = Inl (op1', x, xs, lxs')"
    and "eq_op WM op1 op2"
    and "monotone lxs WM"
    and "produce_inner (op2, lxs) = Some (Inl (op2', y, ys, lys'))"
  shows "lxs' = lys' \<and> x = y \<and> xs = ys"
  using assms proof (induct "(op1, lxs)" r arbitrary: lxs x xs lxs' op1 op2 op1' op2' y ys lys' WM rule: produce_inner_induct)
  case (no_production op h lxs op' zs)
  then show ?case 
    apply - 
    apply (subst (asm) (2) produce_inner.simps)
    apply (erule eq_op.cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
next
  case (produces op h x xs lxs lxs' op')
  then show ?case 
    apply - 
    apply (subst (asm) (1 2) produce_inner.simps)
    apply (erule eq_op.cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
next
  case (terminates op)
  then show ?case by auto
qed

lemma eq_op_produce_inner_next:
  assumes "eq_op WM op1 op2"
    and "apply op1 h = (op1', [])"
    and "monotone (LCons h lxs) WM"
  shows "produce_inner (op2, LCons h lxs) = produce_inner (fst (apply op2 h), lxs) \<and> apply op2 h = (fst (apply op2 h), []) \<and> 
         eq_op (case_event (\<lambda> _ _. WM) (\<lambda> wm. insert wm WM) h) (fst (apply op1 h)) (fst (apply op2 h))"
  using assms apply -
  apply (erule eq_op.cases)
  apply hypsubst_thin
  apply (drule spec[of _ h])
  apply (subst produce_inner.simps)
  apply (auto simp add: rel_prod_sel split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
  done


lemma produce_inner_Some_eq_op_ldropn:
  assumes "produce_inner (op1, lxs) = Some r"
    and "r = Inl (op1', x, xs, lxs')"
    and "eq_op WM op1 op2"
    and "monotone lxs WM"
    and "produce_inner (op2, lxs) = Some (Inl (op2', x, xs, lxs'))"
  shows "\<exists> n . eq_op (wms (list_of (ltake n lxs)) \<union> WM) op1' op2' \<and> ldropn n lxs = lxs' \<and> n > 0 \<and> monotone lxs' (wms (list_of (ltake n lxs)) \<union> WM)"
  using assms proof (induct "(op1, lxs)" r arbitrary: lxs x xs  op1 op2 op1' op2' lxs' WM rule: produce_inner_induct)
  case (no_production op h lxs op' zs)
  then show ?case
  proof (cases h)
    case (Data t d)
    from this no_production(2,3,4,5,6,1) have H: "\<exists> n. eq_op (wms (list_of (ltake (enat n) lxs)) \<union> WM) op1' op2' \<and>
      ldropn n lxs = lxs' \<and> 0 < n \<and> Watermarked_Stream.monotone lxs' (wms (list_of (ltake (enat n) lxs)) \<union> WM)"
      using eq_op_produce_inner_next 
      by fastforce
    from this and Data show ?thesis 
      by (metis eSuc_enat enat_ord_code(4) eq_LConsD ldropn_ltl lfinite_ltake list_of_LCons ltake_eSuc_LCons wms.simps(3) zero_less_Suc)
  next
    case (Watermark wm)
    from this no_production(2,3,4,5,6,1) have H: "\<exists> n. eq_op (wms (list_of (ltake (enat n) lxs)) \<union> insert wm WM) op1' op2' \<and>
      ldropn n lxs = lxs' \<and> 0 < n \<and> Watermarked_Stream.monotone lxs' (wms (list_of (ltake (enat n) lxs)) \<union> insert wm WM)"
      using eq_op_produce_inner_next by fastforce
    from this Watermark show ?thesis 
      by (metis (no_types, opaque_lifting) Un_insert_left eSuc_enat enat_ord_code(4) eq_LConsD ldropn_ltl lfinite_ltake list_of_LCons ltake_eSuc_LCons sup_commute wms.simps(2) zero_less_Suc)
  qed
next
  case (produces op h x xs lxs lxs' op')
  then show ?case 
    apply -
    apply (subst (asm) (1 2) produce_inner.simps)
    apply (erule eq_op.cases)
    apply (drule spec[of _ h])
    apply simp
    apply (intro exI[of _ 1] conjI)
       apply (simp_all split: prod.splits list.splits event.splits)
         apply (meson LConsData)
        apply (metis LConsData enat_0 list_of_LNil ltake_0 sup_bot.right_neutral sup_commute wms.simps(1))
       apply (metis enat_0 list_of_LNil ltake_0 sup_bot.right_neutral sup_commute wms.simps(1))
      apply (metis LConsData enat_0 list_of_LNil ltake_0 sup_bot.right_neutral sup_commute wms.simps(1))
     apply (metis LConsData enat_0 list_of_LNil ltake_0 sup_bot.right_neutral sup_commute wms.simps(1))
    apply (metis enat_0 list_of_LNil ltake_0 sup_bot.right_neutral sup_commute wms.simps(1))
    done
next
  case (terminates op)
  then show ?case by blast
qed

lemma eq_op_soundness:
  assumes "eq_op WM op1 op2"
    and "monotone lxs WM"
  shows "produce op1 lxs = produce op2 lxs"
  using assms proof (coinduction arbitrary: op1 op2 lxs WM rule: llist.coinduct_upto)
  case Eq_llist
  then show ?case 
  proof -
    have "lnull (produce op1 lxs) = lnull (produce op2 lxs)"
      if "eq_op WM op1 op2"
        and "monotone lxs WM"
      using that 
      apply -
      apply (subst (1 2) produce.code)
      apply (simp split: option.splits sum.splits)
      apply (intro conjI impI allI; hypsubst_thin)
      subgoal
        by (meson produce_inner_eq_op_Inl)
      subgoal
        using produce_inner_eq_op_Inr by blast
      subgoal
        by (meson eq_op_sym not_Some_eq produce_inner_eq_op_Inl)
      subgoal
        using produce_inner_eq_op_Inr_Inl by blast
      subgoal
        using produce_inner_None_not_lfinite_aux produce_inner_Some_Inr_lfinite by blast
      subgoal
        using eq_op_sym produce_inner_eq_op_Inr_Inl by blast
      subgoal
        by (simp add: produce_inner_eq_op_Inr_Inr)
      done
    moreover have "lhd (produce op1 lxs) = lhd (produce op2 lxs)"
      if "eq_op WM op1 op2"
        and "Watermarked_Stream.monotone lxs WM"
        and "\<not> lnull (produce op1 lxs)"
        and "\<not> lnull (produce op2 lxs)"
      using that 
      apply -
      apply (subst (1 2) produce.code)
      apply (simp split: option.splits sum.splits)
      apply (intro conjI impI allI; hypsubst_thin)
      subgoal
        by (meson produce_inner_eq_op_Inl)
      subgoal
        using produce_inner_eq_op_Inr by blast
      subgoal
        by (simp add: produce_inner_None_produce_LNil)
      subgoal
        by (meson produce_inner_eq_op_Some_Some)
      subgoal
        using produce_inner_eq_op_Inr_Inl by blast
      subgoal
        by (simp add: produce_inner_None_produce_LNil)
      subgoal
        using eq_op_sym produce_inner_eq_op_Inr_Inl by blast
      subgoal
        by (simp add: produce_inner_eq_op_Inr_Inr)
      done
    moreover have "llist.v1.congclp (\<lambda>llist llist'. \<exists>op1 op2 lxs WM. llist = produce op1 (lxs::('a, 'b) event llist) \<and> llist' = produce op2 lxs \<and> eq_op WM op1 op2 \<and> Watermarked_Stream.monotone lxs WM) (ltl (produce op1 lxs)) (ltl (produce op2 lxs))"
      if "eq_op WM op1 op2"
        and "Watermarked_Stream.monotone lxs WM"
        and "\<not> lnull (produce op1 lxs)"
        and "\<not> lnull (produce op2 lxs)"
      using that 
      apply -
      apply (subst (3 4) produce.code)
      apply (simp split: option.splits sum.splits)
      apply (intro llist.cong_lshift conjI impI allI)
      subgoal
        using lshift.cong_refl by blast
      subgoal
        by (meson produce_inner_eq_op_Inl)
      subgoal
        using produce_inner_eq_op_Inr by blast
      subgoal
        by (simp add: produce_inner_None_produce_LNil)
      subgoal
        by (meson produce_inner_eq_op_Some_Some)
      subgoal
        apply (intro lshift.cong_base)
        by (smt (verit, ccfv_SIG) produce_inner_Some_eq_op_ldropn produce_inner_eq_op_Some_Some)
      subgoal
        using produce_inner_eq_op_Inr_Inl by blast
      subgoal
        by (simp add: produce_inner_None_produce_LNil)
      subgoal
        using eq_op_sym produce_inner_eq_op_Inr_Inl by blast
      subgoal
        by (simp add: lshift.cong_refl produce_inner_eq_op_Inr_Inr)
      done
    ultimately show ?thesis
      using Eq_llist(1) Eq_llist(2) by blast
  qed
qed

end